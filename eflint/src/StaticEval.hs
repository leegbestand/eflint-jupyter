{-# LANGUAGE RecordWildCards, LambdaCase, TupleSections #-}

module StaticEval where

import Spec
import Binders

import Control.Monad
import Control.Applicative

import Data.Maybe (isNothing)
import Data.List ((\\))
import qualified Data.Map as M
import qualified Data.Set as S

data M_Stc a = M_Stc {runStatic :: Spec -> Either [String] (Spec, a)}

instance Monad M_Stc where
  return a = M_Stc $ \spec -> Right (spec, a)
  m >>= f  = M_Stc $ \spec -> case runStatic m spec of 
                                Right (spec',a)  -> runStatic (f a) spec'
                                Left err -> Left err

instance Applicative M_Stc where
  pure  = return
  (<*>) = ap

instance Functor M_Stc where
  fmap  = liftM

instance Alternative M_Stc where
  empty   = M_Stc (const (Left []))
  p <|> q = M_Stc $ \spec -> case runStatic p spec of 
                              Left ers1 -> case runStatic q spec of
                                            Left ers2 -> Left (ers1 ++ ers2)
                                            Right x   -> Right x
                              Right x   -> Right x

err :: String -> M_Stc a
err str = M_Stc $ \spec -> Left [str]

get_dom :: DomId -> M_Stc Domain
get_dom d = M_Stc $ \spec -> case find_decl spec d of 
                              Just tspec  -> Right (spec, domain tspec)
                              _           -> Left ["undeclared type: " ++ d]

get_spec :: M_Stc Spec
get_spec = M_Stc $ \spec -> Right (spec, spec)

execute_decl :: Decl -> M_Stc ()
execute_decl decl = M_Stc $ \spec -> 
  let spec' = case decl of 
          PlaceholderDecl f t -> spec { aliases = M.insert f t (aliases spec) }
          TypeExt ty clauses -> spec { decls = M.adjust (apply_type_ext ty clauses) ty (decls spec) }
          TypeDecl ty tspec -> spec { decls = M.insert ty tspec (decls spec) }
  in Right (spec', ())

with_spec :: Spec -> M_Stc a -> M_Stc a
with_spec spec' m = M_Stc $ \spec -> case runStatic m spec' of
  Left err    -> Left err
  Right (_,a) -> Right (spec, a)

with_decl :: DomId -> TypeSpec -> M_Stc a -> M_Stc a
with_decl ty tspec m = M_Stc $ \spec -> case runStatic m (spec{decls=M.insert ty tspec (decls spec)}) of
  Left err    -> Left err
  Right (_,a) -> Right (spec, a)

free_vars :: Term -> M_Stc (S.Set Var)
free_vars t = do spec <- get_spec
                 let xs = free spec t
                 check_known_type (S.toList xs)
                 return xs

compile_all :: Spec -> Refiner -> Initialiser -> Scenario -> Either [String] (Spec, Refiner, Initialiser, Scenario) 
compile_all f r i s = case runStatic compile f of
  Left errs                    -> Left errs  
  Right (_,(spec, init, scen)) -> Right (spec, r, init, scen)
  where compile = do
          f' <- compile_spec
          with_spec f' $ do
            i' <- compile_initialiser i
            s' <- compile_stmts s
            return (f',i',s')

compile_initialiser :: Initialiser -> M_Stc Initialiser
compile_initialiser = mapM (compile_effect [])

compile_stmts :: [Statement] -> M_Stc [Statement]
compile_stmts = mapM compile_stmt

compile_stmt :: Statement -> M_Stc Statement
compile_stmt (Query t0) = do
  spec <- get_spec
  fs <- free_vars t0
  let unbounds = S.toList fs
  let t1 | null unbounds    = t0
         | Not inner <- t0  = Not (Exists unbounds inner)
         | otherwise        = Exists unbounds t0
  case filter (isNothing . find_decl spec . remove_decoration spec) unbounds of
    []    -> Query <$> convert_term t1 TyBool
    (t:_) -> err ("undeclared type " ++ remove_decoration spec t ++ " in query")
compile_stmt (Trans xs aty (Right (d,mods))) = compile_trans_term xs aty (App d mods) (Just d)
compile_stmt (Trans xs aty (Left t)) = compile_trans_term xs aty t Nothing
compile_trans_term xs aty term md = do 
  fs <- free_vars term
  let unbounds = S.toList (fs `S.difference` S.fromList xs)
  Trans (xs ++ unbounds) aty . Left <$> converter term
  where converter term = case md of Just d -> convert_term term (TyTagged d)
                                    _      -> fst <$> compile_term term

compile_phrase :: Phrase -> M_Stc CPhrase
compile_phrase p = case p of
  PSkip             -> return CPSkip
  PDo tv            -> return (CDo tv)
  PTrigger vs t     -> fmap (de_stmt p) (compile_stmt (to_stmt p))
  Create vs t       -> fmap (de_stmt p) (compile_stmt (to_stmt p))
  Terminate vs t    -> fmap (de_stmt p) (compile_stmt (to_stmt p))
  Obfuscate vs t    -> fmap (de_stmt p) (compile_stmt (to_stmt p))
  PQuery t          -> fmap (de_stmt p) (compile_stmt (to_stmt p))
  PDeclBlock ds     -> do
    forM_ (filter introducesName ds) execute_decl 
    forM_ ds ((execute_decl =<<) . compile_decl)
    return CPOnlyDecls 
  where to_stmt (PTrigger vs t) = Trans vs Trigger (Left t)
        to_stmt (Create vs t)     = Trans vs AddEvent (Left t)
        to_stmt (Terminate vs t)  = Trans vs RemEvent (Left t)
        to_stmt (Obfuscate  vs t) = Trans vs ObfEvent (Left t)
        to_stmt (PQuery t)        = Spec.Query t
        to_stmt _ = error "Explorer.assert 1"
        de_stmt (PTrigger vs t) (Trans vs' Trigger (Left t')) = CTrigger vs' t'
        de_stmt (Create vs t) (Trans vs' AddEvent (Left t')) = CCreate vs' t'
        de_stmt (Terminate vs t) (Trans vs' RemEvent (Left t')) = CTerminate vs' t'
        de_stmt (Obfuscate vs t) (Trans vs' ObfEvent (Left t')) = CObfuscate vs' t'
        de_stmt (PQuery t) (Spec.Query t') = CQuery t'
        de_stmt _ _ = error "Explorer.assert 2"

compile_decl :: Decl -> M_Stc Decl
compile_decl d@(PlaceholderDecl x y) = check_known_type [no_decoration y] >> return d 
compile_decl d@(TypeExt ty clauses) = compile_ext ty clauses 
compile_decl d@(TypeDecl ty tspec) = compile_type_spec ty tspec 

compile_ext :: DomId -> [ModClause] -> M_Stc Decl
compile_ext ty clauses = do
  spec <- get_spec 
  case M.lookup ty (decls spec) of
   Nothing -> err ("cannot find the type " ++ ty ++ " to extend or " ++ ty ++ " of the wrong kind")
   Just tspec -> TypeExt ty <$> mapM (compile_clause ty tspec) clauses 
 where compile_clause ty tspec clause = case clause of 
        ConditionedByCl conds -> ConditionedByCl <$> mapM (convert_precon ty tspec) conds
        DerivationCl dvs -> DerivationCl <$> mapM (compile_derivation xs ty) dvs 
        PostCondCl effs -> PostCondCl <$> mapM (compile_effect xs) effs 
        SyncCl ss -> SyncCl <$> mapM (compile_sync xs) ss
        ViolationCl vts -> ViolationCl <$> mapM (compile_violation_condition ty) vts
        EnforcingActsCl ds -> return $ EnforcingActsCl ds
        where xs = case domain tspec of Products xs -> xs
                                        _           -> [no_decoration ty]
 
compile_type_spec :: DomId -> TypeSpec -> M_Stc Decl 
compile_type_spec ty tspec = do
  with_decl ty tspec $ do -- ensure the declaration is active during its compilation 
    dom <- get_dom ty
    check_domain ty dom
    let xs = case dom of 
              Products xs -> xs
              _           -> [no_decoration ty]
    derivation <- mapM (compile_derivation xs ty) (derivation tspec) 
    kind <- compile_kind ty tspec (kind tspec)
    conditions <- mapM (convert_precon ty tspec) (conditions tspec)
    dom_filter <- convert_term (domain_constraint tspec) TyBool
    ffs <- free_vars dom_filter
    let domain_constraint = case S.toList (ffs `S.difference` S.fromList xs) of
                              []   -> dom_filter
                              vars -> Exists vars dom_filter
    return (TypeDecl ty (TypeSpec {domain = domain tspec, closed = closed tspec,..}))

check_domain :: DomId -> Domain -> M_Stc ()
check_domain dty (Products xs) = check_known_type xs 
check_domain _ _ = return ()

check_known_type :: [Var] -> M_Stc ()
check_known_type xs = do
  spec <- get_spec
  let op var@(Var base dec) = case find_decl spec (remove_decoration spec var) of
          Nothing -> err ("Undeclared type or placeholder `" ++ base ++ dec ++ "`")
          Just _  -> return ()
  mapM_ op xs

convert_precon :: DomId -> TypeSpec -> Term -> M_Stc Term
convert_precon ty tspec t = do 
  let xs = case domain tspec of Products xs -> xs
                                _           -> [no_decoration ty]
  cond' <- convert_term t TyBool
  cond_fs <- free_vars cond'
  let unbounds = S.toList (cond_fs `S.difference` S.fromList xs)
  return $ if null unbounds then cond' else Exists unbounds cond'

compile_kind :: DomId -> TypeSpec -> Kind -> M_Stc Kind
compile_kind ty tspec k = case k of
  Act aspec -> do 
    let Products xs = domain tspec
    -- convert post-conditions
    effects' <- sequence (map (compile_effect xs) (effects aspec))
    -- convert syncs
    syncs' <- mapM (compile_sync xs) (syncs aspec)
    -- build new act
    return (Act (aspec { effects = effects', syncs = syncs' } ))
  Event espec -> do 
    let Products xs = domain tspec
    effects' <- sequence (map (compile_effect xs) (event_effects espec))
    return (Event (espec { event_effects = effects' } ))
  Duty dspec -> do -- TODO, should be dealt with by outer -> inner translation
                 e_conds <- concat <$> mapM select_condition (enforcing_acts dspec)
                 vconds <- mapM (compile_violation_condition ty) (e_conds ++ violated_when dspec)
                 return $ (Duty (dspec { violated_when = vconds }))
       where select_condition a = do
               spec <- get_spec
               case M.lookup a (decls spec) of 
                  Just tspec | Act _ <- kind tspec -> return [foldr And (BoolLit True) (conditions tspec)]
                  _ -> err ("duty " ++ ty ++ " is declared with enforcing act " ++ a ++ " which is not a declared or not declared as an act")
  Fact _     -> return k

compile_violation_condition :: DomId -> Term -> M_Stc Term
compile_violation_condition dty term = do
  domain <- get_dom dty
  let Products xs = domain
  term' <- convert_term term TyBool
  fs <- free_vars term'
  let unbounds = S.toList (fs `S.difference` (S.fromList xs))
      term'' | null unbounds = term'
             | otherwise     = Exists unbounds term'
  return term'' 

compile_sync :: [Var] -> Sync -> M_Stc Sync 
compile_sync bound (Sync vars t) = do
  (t', tau) <- compile_term t
  case tau of
    TyTagged _ -> do  frees <- free_vars t'
                      let unbounds = S.toList (frees `S.difference` S.fromList (vars ++ bound))
                      return $ Sync (vars ++ unbounds) t' 
    _          -> err ("sync clause is not an instance expression")

compile_spec :: M_Stc Spec
compile_spec = do
 spec <- get_spec
 ds   <- sequence (map (uncurry compile_type_spec) (M.toList (decls spec)))
 let tspecs = concatMap op ds
      where op (TypeDecl ty tspec) = [(ty,tspec)]
            op _                   = []
 return (spec {decls = decls_union (decls spec) (M.fromList tspecs) })
          
compile_derivation :: [Var] -> DomId -> Derivation -> M_Stc Derivation
compile_derivation bound d (HoldsWhen t) = do
  t' <- convert_term t TyBool 
  fs <- free_vars t'
  let unbounds = S.toList (fs `S.difference` (S.fromList bound))
  return (HoldsWhen (if null unbounds then t' else Exists unbounds t'))
compile_derivation bound d (Dv xs t) = compile_derived_from_clause xs t d

compile_derived_from_clause xs t d = do
  t' <- convert_term t (TyTagged d)
  fs <- free_vars t'
  let unbounds = S.toList (fs `S.difference` (S.fromList xs))
  return (Dv (xs ++ unbounds) t')

compile_primitive_application :: DomId -> Arguments -> M_Stc (Term, Type)
compile_primitive_application d params = get_dom d >>= \dom -> case (dom, params) of
  (_, Left as) | length as > 1 -> err error_string
--  (AnyString, Left [])   -> primitive d (StringLit "()") (Just TyStrings)
--  (AnyString, Right [])  -> primitive d (StringLit "()") (Just TyStrings)
  (AnyString, Left [a])  -> primitive d a (Just TyStrings)
  (Strings [s], Left []) -> primitive d (StringLit s) (Just TyStrings)
  (Strings [s], Right [])-> primitive d (StringLit s) (Just TyStrings)
  (Strings _, Left [a])  -> primitive d a (Just TyStrings)
  (AnyInt, Left [a])     -> primitive d a (Just TyInts)
  (Ints [i], Right [])   -> primitive d (IntLit i) (Just TyInts)
  (Ints [i], Left [])    -> primitive d (IntLit i) (Just TyInts)
  (Ints _, Left [a])     -> primitive d a (Just TyInts)
  (_, Right _)           -> err error_string
  _                      -> err error_string
  where error_string = "The constructor " ++ d ++ " is primitive, and should receive exactly one argument in functional style"
        primitive d t Nothing = do (t', _) <- compile_term t
                                   return (Tag t' d, TyTagged d)
        primitive d t (Just ty) = do t' <- convert_term t ty
                                     return (Tag t' d, TyTagged d)
        
 
compile_arguments :: DomId -> Arguments -> M_Stc Arguments
compile_arguments _ (Right ms) = Right <$> compile_modifiers ms
compile_arguments d (Left ts) = do
  spec <- get_spec
  dom <- get_dom d
  case dom of Products xs 
               | length xs == length ts -> Right <$> compile_modifiers (map (uncurry Rename) (zip xs ts))
               | otherwise -> err ("elements of " ++ d ++ " have " ++ show (length xs) ++ " components, " ++ show (length ts) ++ " given")
              _ -> err ("non-composite " ++ d ++ " used in application")

compile_modifiers :: [Modifier] -> M_Stc [Modifier]
compile_modifiers mods = do
  spec <- get_spec
  let compile_mod (Rename x t) = Rename x <$> convert_term t (TyTagged (remove_decoration spec x)) 
  sequence (map compile_mod mods)

compile_effect :: [Var] -> Effect -> M_Stc Effect
compile_effect bound eff = case eff of 
  TAll xs t -> compile_effect' TAll xs t
  CAll xs t -> compile_effect' CAll xs t
  OAll xs t -> compile_effect' OAll xs t
  where compile_effect' cons xs t = do (t',tau) <- compile_term t
                                       fs <- free_vars t'
                                       let unbounds = S.toList (fs `S.difference` S.fromList (bound ++ xs))
                                       return (cons (xs ++ unbounds) t')

compile_term :: Term -> M_Stc (Term, Type)
compile_term t0 = do
 spec <- get_spec 
 case t0 of
  CurrentTime -> return (CurrentTime, TyInts)
  StringLit s -> return (t0, TyStrings)
  IntLit i    -> return (t0, TyInts)
  BoolLit b   -> return (t0, TyBool)
  Ref x       -> check_known_type [x] >> return (t0, TyTagged (remove_decoration spec x))
  App d ms    -> do check_known_type [no_decoration d]
                    case fmap domain (find_decl spec d) of 
                      Just (Products _) -> do  
                        ms' <- compile_arguments d ms 
                        return (App d ms', TyTagged d)
                      _ -> compile_primitive_application d ms 
  Tag t d     -> err "tagging is an auxiliary operation" 
  Untag t     -> do (t', ty) <- compile_term t
                    case ty of TyTagged d   -> case find_decl spec d of
                                Nothing     -> err "untagging is an auxiliary operation"
                                Just decl   -> case domain decl of
                                  Strings _ -> return (Untag t', TyStrings)
                                  Ints    _ -> return (Untag t', TyInts)
                                  AnyString -> return (Untag t', TyStrings)
                                  AnyInt    -> return (Untag t', TyInts)
                                  _         -> err "untagging is an auxiliary operation"
                               _            -> err "untagging is an auxiliary operation"

  Not t       -> do t' <- convert_term t TyBool
                    return (Not t', TyBool)
  And t1 t2   -> do t1' <- convert_term t1 TyBool
                    t2' <- convert_term t2 TyBool
                    return (And t1' t2', TyBool)
  Or  t1 t2   -> do t1' <- convert_term t1 TyBool
                    t2' <- convert_term t2 TyBool
                    return (Or t1' t2', TyBool)

  Geq t1 t2   -> do t1' <- convert_term t1 TyInts
                    t2' <- convert_term t2 TyInts
                    return (Geq t1' t2', TyBool)
  Leq t1 t2   -> do t1' <- convert_term t1 TyInts
                    t2' <- convert_term t2 TyInts
                    return (Leq t1' t2', TyBool)
  Le t1 t2    -> do t1' <- convert_term t1 TyInts
                    t2' <- convert_term t2 TyInts
                    return (Le t1' t2', TyBool)
  Ge t1 t2    -> do t1' <- convert_term t1 TyInts
                    t2' <- convert_term t2 TyInts
                    return (Ge t1' t2', TyBool)

  Mult t1 t2  -> do t1' <- convert_term t1 TyInts
                    t2' <- convert_term t2 TyInts
                    return (Mult t1' t2', TyInts)
  Mod t1 t2   -> do t1' <- convert_term t1 TyInts
                    t2' <- convert_term t2 TyInts
                    return (Mod t1' t2', TyInts)
  Div t1 t2  ->  do t1' <- convert_term t1 TyInts
                    t2' <- convert_term t2 TyInts
                    return (Div t1' t2', TyInts)
  Sub t1 t2   -> do t1' <- convert_term t1 TyInts
                    t2' <- convert_term t2 TyInts
                    return (Sub t1' t2', TyInts)
  Add t1 t2   -> do t1' <- convert_term t1 TyInts
                    t2' <- convert_term t2 TyInts
                    return (Add t1' t2', TyInts)
  Sum xs t    -> do t'  <- convert_term t TyInts 
                    return (Sum xs t', TyInts)

  Eq t1 t2    -> (do  (t1', tau1) <- compile_term t1
                      t2' <- convert_term t2 tau1
                      return (Eq t1' t2', TyBool)) <|>
                 (do  (t2', tau2) <- compile_term t2
                      t1' <- convert_term t1 tau2
                      return (Eq t1' t2', TyBool))
  Neq t1 t2   -> (do  (t1', tau1) <- compile_term t1
                      t2' <- convert_term t2 tau1
                      return (Neq t1' t2', TyBool)) <|>
                 (do  (t2', tau2) <- compile_term t2
                      t1' <- convert_term t1 tau2
                      return (Neq t1' t2', TyBool))
  Count xs t  -> do (t', tau) <- compile_term t
                    return (Count xs t', TyInts)
  Max xs t    -> do (t', tau) <- compile_term t
                    return (Max xs t', TyInts)
  Min xs t    -> do (t', tau) <- compile_term t
                    return (Min xs t', TyInts)
  When t1 t2  -> do (t1', tau) <- compile_term t1
                    t2' <- convert_term t2 TyBool
                    return (When t1' t2', tau)
  Present t   -> do (t', tau) <- compile_term t -- simplification, assuming no conversion to tagged-elems yet
                    case tau of TyTagged d  -> return (Present t', TyBool) 
                                errt        -> err ("Holds(t) requires t to evaluate to a an instance, not a literal")
  Violated t  -> do (t', tau) <- compile_term t -- simplification, as above
                    case tau of TyTagged d -> return (Violated t', TyBool)
                                errt       -> err ("Violated(t) requires t to evaluate to an instance, not a literal")
  Enabled t   -> do (t', tau) <- compile_term t -- simplification, as above
                    case tau of TyTagged d -> return (Enabled t', TyBool)
                                errt       -> err ("Enabled(t) requires t to evaluate to an instance, not a literal")
  Exists xs t -> do t' <- convert_term t TyBool
                    return (Exists xs t', TyBool)
  Forall xs t -> do t' <- convert_term t TyBool
                    return (Forall xs t', TyBool)
  Project t x -> do (t',tau) <- compile_term t
                    case tau of 
                      TyTagged d -> do 
                        dom <- get_dom d
                        case dom of 
                          Products xs ->  if elem x xs 
                                          then return (Project t' x, TyTagged (remove_decoration spec x))
                                          else err ("project(" ++ show t++ ","++show x++") expects t to evaluate to a value of a product-type containing a reference to " ++ show x ++ " instead got: " ++ show xs) 
                          _ -> err ("project(" ++ show t++ ","++show x++") expects t to evaluate to a value of a product-type, instead got: " ++ show dom) 
                      _ -> err ("project(" ++ show t++ ","++show x++") expects t to evaluate to a tagged-element, instead got: " ++ show tau) 

-- term => term : type
convert_term :: Term -> Type -> M_Stc Term
convert_term t ty = do
  (t', ty') <- compile_term t
  if ty' == ty then return t'   -- rule id
               else case ty of
    TyStrings -> case ty' of TyTagged d -> flip match_domain AnyString <$> get_dom d >>= \case
                                            True  -> return (Untag t')
                                            False -> conv_err ty' ty
                             _ -> conv_err ty' ty
    TyInts -> case ty' of TyTagged d  -> flip match_domain AnyInt <$> get_dom d >>= \case
                                          True  -> return (Untag t')
                                          False -> conv_err ty' ty 
                          _           -> conv_err ty' ty
    TyBool -> case ty' of TyInts      -> return $ Geq t' (IntLit 1) -- rule INT -> BOOL
                          TyTagged _  -> return $ Present t' 
                          _           -> conv_err ty' ty
    TyTagged d -> get_dom d >>= match_type ty' >>= \case True  -> return (Tag t' d)
                                                         False -> conv_err ty' ty
  where conv_err source target = err ("cannot convert " ++ show source ++ " to " ++ show target)

match_type :: Type -> Domain -> M_Stc Bool
match_type (TyTagged d) dom = get_dom d >>= return . flip match_domain dom 
match_type TyInts dom = case dom of
  AnyInt      -> return True
  Ints _      -> return True
  Time        -> return True
  Strings _   -> return False
  AnyString   -> return False
  Products _  -> return False
match_type TyStrings dom = case dom of
  AnyString   -> return True
  Strings _   -> return True
  AnyInt      -> return False
  Ints _      -> return False
  Products _  -> return False
  Time        -> return False
match_type _ _ = return False

-- | second domain is the conversion target
match_domain :: Domain -> Domain -> Bool
match_domain dom dom' = case (dom, dom') of
  (AnyString, AnyString)    -> True 
  (Strings _, AnyString)    -> True
  (AnyString, Strings _)    -> False
  (Strings s1, Strings s2)  -> null (s1 \\ s2) 
  (AnyString, _)            -> False
  (Strings _, _)            -> False

  (AnyInt, AnyInt)          -> True
  (Ints _, AnyInt)          -> True
  (AnyInt, Ints _)          -> True
  (Ints i1, Ints i2)        -> null (i1 \\ i2)
  (AnyInt, AnyString)       -> False
  (AnyInt, Strings _)       -> False
  (AnyInt, Products _)      -> False
  (Ints _, AnyString)       -> False
  (Ints _, Strings _)       -> False
  (Ints _, Products _)      -> False
  (AnyInt, Time)            -> False
  (Ints _, Time)            -> False
  
  (Time, Time)              -> True
  (Time, AnyInt)            -> True
  (Time, Ints _)            -> False
  (Time, AnyString)         -> False
  (Time, Strings _)         -> False
  (Time, Products _)        -> False

  (Products r, Products r') -> r == r'
  (Products _, _)           -> False
