{-# LANGUAGE LambdaCase, TupleSections #-}

module Eval where

import Spec
import State

import Control.Monad
import Control.Applicative

import Data.Bool (bool)
import Data.List ((\\))
import Data.Maybe (fromJust)
import qualified Data.Map as M

data M_Subs a = M_Subs { runSubs :: Spec -> State -> InputMap -> Subs -> Either RuntimeError [a] }

err :: RuntimeError -> M_Subs a 
err re = M_Subs $ \spec state inpm subs -> Left re

nd :: [a] -> M_Subs a
nd vals = M_Subs $ \spec state inpm subs -> return vals

results :: M_Subs a -> M_Subs [a]
results n = M_Subs $ \spec state inpm subs -> (:[]) <$> runSubs n spec state inpm subs

ignoreMissingInput :: M_Subs a -> M_Subs a
ignoreMissingInput m = M_Subs $ \spec state inpm subs -> case runSubs m spec state inpm subs of
  Left (MissingInput _) -> Right []
  res                   -> res
 
bind :: Var -> Tagged -> M_Subs a -> M_Subs a
bind k v m = M_Subs $ \spec state inpm -> runSubs m spec state inpm . M.insert k v

scope_var :: Var -> M_Subs a -> M_Subs a
scope_var x m = do 
  te <- every_valid_subs x
  bind x te m

get_type_spec :: DomId -> M_Subs TypeSpec
get_type_spec d = M_Subs $ \spec state inpm subs -> 
                    case find_decl spec d of
                      Nothing    -> Left (InternalError (UndeclaredType d))
                      Just tspec -> Right [tspec]

get_dom :: DomId -> M_Subs (Domain, Term)
get_dom d = M_Subs $ \spec state inpm subs -> 
              case find_decl spec d of
                Nothing    -> Left (InternalError (UndeclaredType d))
                Just tspec -> Right [(domain tspec, domain_constraint tspec)]

get_time :: M_Subs Int
get_time = M_Subs $ \spec state inpm subs -> return [time state]

get_subs :: M_Subs Subs
get_subs = M_Subs $ \spec state inpm subs -> return [subs]

modify_subs :: (Subs -> Subs) -> M_Subs a -> M_Subs a
modify_subs mod m = M_Subs $ \spec state inpm -> runSubs m spec state inpm . mod 

get_spec :: M_Subs Spec 
get_spec = M_Subs $ \spec state inpm subs -> return [spec]

get_state :: M_Subs State
get_state = M_Subs $ \spec state inpm subs -> return [state]

get_input :: M_Subs InputMap
get_input = M_Subs $ \spec state inpm subs -> return [inpm]

get_input_assignment :: Tagged -> M_Subs Assignment
get_input_assignment te = M_Subs $ \spec state inpm subs -> 
  Right [maybe Unknown (bool HoldsFalse HoldsTrue) (M.lookup te inpm)]

get_assignment :: Tagged -> M_Subs Assignment
get_assignment te@(_,d) = M_Subs $ \spec state inpm subs -> 
  Right [maybe Unknown op (M.lookup te (contents state))]
    where op info | from_sat info = Unknown
                  | value info    = HoldsTrue
                  | otherwise     = HoldsFalse 


instance Functor M_Subs where
  fmap  = liftM 

instance Applicative M_Subs where
  pure  = return
  (<*>) = ap

instance Monad M_Subs where
  return a  = M_Subs $ \spec state inpm subs -> return [a]
  (>>=) m f = M_Subs $ \spec state inpm subs -> do 
                as <- runSubs m spec state inpm subs
                let op res a = (++res) <$> runSubs (f a) spec state inpm subs
                foldM op [] as 

instance Alternative M_Subs where
  empty     = M_Subs $ \spec state inpm subs -> return []
  m1 <|> m2 = M_Subs $ \spec state inpm subs -> do
                        xs <- runSubs m1 spec state inpm subs 
                        ys <- runSubs m2 spec state inpm subs
                        return (xs ++ ys)

instance MonadPlus M_Subs where

instantiate_domain :: DomId -> Domain -> M_Subs Elem
instantiate_domain d dom = case dom of
  Time          -> get_time >>= \time -> nd [ Int i | i <- [0..time]]
  AnyString     -> err (InternalError $ EnumerateInfiniteDomain d dom)
  AnyInt        -> err (InternalError $ EnumerateInfiniteDomain d dom)
  Strings ss    -> nd [ String s | s <- ss ]
  Ints is       -> nd [ Int i    | i <- is ]
  Products xs   -> Product <$> sequence (map every_valid_subs xs)

substitute_var :: Var -> M_Subs Tagged
substitute_var x = do
  spec <- get_spec
  subs <- get_subs
  case M.lookup x subs of
    Just te@(v,d') -> return (v, remove_decoration spec x)
    Nothing        -> err (InternalError $ MissingSubstitution x)

every_valid_subs :: Var -> M_Subs Tagged
every_valid_subs x = do
    spec <- get_spec
    let d = remove_decoration spec x
    (dom, _) <- get_dom d 
    if enumerable spec dom then generate_instances d
                           else every_available_subs spec d
 where generate_instances d = do  
          (dom, dom_filter) <- get_dom d 
          e <- instantiate_domain d dom
          let bindings = case (dom,e) of (Products xs, Product args) -> M.fromList (zip xs args)
                                         _ -> M.singleton (no_decoration d) (e,d)
          modify_subs (`subsUnion` bindings) (checkTrue (eval dom_filter))
          return (e,d)
       every_available_subs spec d = do
          state <- get_state 
          inpm  <- get_input
          nd [ te | te@(v,d') <- state_input_holds state inpm, d' == d ]

-- if fact/duty/event/action is of an inenumerable type, is derived with "Holds when" and is not in state,
-- then check if it is a valid instance and whether it satisfies derivation clause
-- if so, consider it to hold true
is_in_virtual_state :: Tagged -> M_Subs Bool
is_in_virtual_state te@(_,d) = do
  spec <- get_spec
  is_valid_instance te >>= \case
   False -> return False
   True  -> do
    get_input_assignment te >>= \case
     HoldsTrue   -> return True
     HoldsFalse  -> return False
     Unknown     -> do
      get_assignment te >>= \case
       HoldsTrue  -> return True
       HoldsFalse -> return False
       Unknown    -> do
        is_derivable te >>= \case
         True  -> return True
         False -> case fromJust (closed_type spec d) of
          True -> return False
          False -> err (MissingInput te)

is_enabled :: Tagged -> M_Subs Bool 
is_enabled v@(e,d) = do 
  spec <- get_spec
  is_in_virtual_state v >>= \case 
    False -> return False 
    True  -> sat_conditions v >>= \case
      False -> return False
      True  -> case fmap kind (find_decl spec d) of
        Just (Act aspec) -> do
          (dom, _) <- get_dom d
          let (Product args, Products xs) = (e, dom)
          modify_subs (`subsUnion` (M.fromList (zip xs args))) $ do
            sync_infos <- concat <$> mapM eval_sync (syncs aspec) 
            return (all (not . trans_forced) sync_infos)
        _ -> return True

is_valid_instance :: Tagged -> M_Subs Bool
is_valid_instance te@(e,d) = do 
  (dom, dom_filter) <- get_dom d 
  let bindings = case (dom,e) of (Products xs, Product args) -> M.fromList (zip xs args)
                                 _ -> M.singleton (no_decoration d) te
  let check_constraint = modify_subs (`subsUnion` bindings) (whenBool (eval dom_filter) return)
  case (e, dom) of 
    (Int i, Ints is) | i `elem` is -> check_constraint
    (Int i, AnyInt) -> check_constraint
    (String s, Strings ss) | s `elem` ss -> check_constraint
    (String s, AnyString) -> check_constraint
    (Product args, Products params) | length args == length params ->
      and <$> mapM is_valid_instance args >>= \case
        False -> return False
        True  -> check_constraint 
    _ -> return False

is_derivable :: Tagged -> M_Subs Bool
is_derivable te@(e,d) = do
  spec <- get_spec
  (dom, _) <- get_dom d
  let bindings = case (dom,e) of (Products xs, Product args) -> M.fromList (zip xs args)
                                 _ -> M.singleton (no_decoration d) te
  let consider_clause deriv = case deriv of 
          Dv xs dvt -> do tes <- modify_subs (`subsUnion` bindings) 
                                   (foreach (xs \\ M.keys bindings) (whenTagged (eval dvt) return))
                          return (te `elem` tes) -- valid instance and in DV
          HoldsWhen t -> modify_subs (`subsUnion` bindings) (whenBool (eval t) return )
  case fmap derivation (find_decl spec d) of 
    Nothing  -> return False
    Just dvs -> (or <$> mapM consider_clause dvs) >>= \case 
                  True  -> sat_conditions te
                  False -> return False

sat_conditions :: Tagged -> M_Subs Bool
sat_conditions te@(v,d) = 
  is_valid_instance te >>= \case  
    False -> return False
    True  -> do
      tspec <- get_type_spec d
      (dom, _) <- get_dom d
      let bindings = case (dom,v) of (Products xs, Product args) -> M.fromList (zip xs args)
                                     _ -> M.singleton (no_decoration d) te
      modify_subs (`subsUnion` bindings) (and <$> mapM (flip whenBool return . eval) (conditions tspec))

is_violated :: Tagged -> M_Subs Bool
is_violated te@(_,d) = (&&) <$> is_in_virtual_state te <*> violation_condition te
 where violation_condition te = do 
        spec <- get_spec 
        eval_violation_condition te (find_violation_cond spec d)

eval_violation_condition :: Tagged -> Maybe [Term] -> M_Subs Bool
eval_violation_condition te@(v,d) mconds = do
  (dom, _) <- get_dom d
  let Products xs = dom
      Product args = v
  modify_subs (`subsUnion` (M.fromList (zip xs args))) 
    (whenBool (eval (maybe (BoolLit False) (foldr Or (BoolLit False)) mconds)) return)


syncTransInfos :: [TransInfo] -> (Store, Bool {- forced? -})
syncTransInfos = foldr op (emptyStore, False)
  where op (TransInfo te ass is_f is_a tes) (ass',is_f') = 
          (ass `store_union` ass', is_f || is_f')

instantiate_trans :: Tagged -> M_Subs TransInfo
instantiate_trans te@(v,d) = do 
  tspec <- get_type_spec d
  is_enabled <- is_enabled te 
  case kind tspec of 
      Fact _      -> empty
      Duty _      -> empty 
      Act aspec   -> do_transition te actor is_enabled (effects aspec) (syncs aspec)
      Event espec -> do_transition te actor is_enabled (event_effects espec) []
  where do_transition te@(v,d) isAction is_enabled effects ss = do 
          (dom, _) <- get_dom d
          let Products xs = dom
          let Product args = v
          modify_subs (`subsUnion` (M.fromList (zip xs args))) $ do
            sync_infos <- concat <$> mapM eval_sync ss 
            let (ss_ass,any_f) = syncTransInfos sync_infos
            ass' <- store_unions <$> mapM eval_effect effects
            let ass = ass' `store_union` ss_ass
            return (TransInfo te ass (any_f || not is_enabled) isAction sync_infos)
        actor = case v of Product (a:objs) -> Just a
                          _                -> Nothing

eval_sync :: Sync -> M_Subs [TransInfo]
eval_sync (Sync xs t) = foreach xs (whenTagged (eval t) instantiate_trans)

eval_effect :: Effect -> M_Subs Store
eval_effect (CAll xs t) = M.fromList . map (,HoldsTrue) <$> foreach xs (whenTagged (eval t) return)
eval_effect (TAll xs t) = M.fromList . map (,HoldsFalse) <$> foreach xs (whenTagged (eval t) return)
eval_effect (OAll xs t) = M.fromList . map (,Unknown) <$> foreach xs (whenTagged (eval t) return)

get_kind :: DomId -> M_Subs Kind
get_kind d = M_Subs $ \spec state inpm subs -> return $ maybe [] (:[]) (find_kind spec d) 
  where find_kind :: Spec -> DomId -> Maybe Kind 
        find_kind spec d = fmap kind (find_decl spec d)

whenBool :: M_Subs Value -> (Bool -> M_Subs a) -> M_Subs a
whenBool m f = m >>= \case ResBool b -> f b
                           _         -> empty

checkTrue :: M_Subs Value -> M_Subs () 
checkTrue m = m >>= \case ResBool True -> return () 
                          _            -> empty

checkFalse :: M_Subs Value -> M_Subs () 
checkFalse m = m >>= \case ResBool False  -> return () 
                           _              -> empty


whenInt :: M_Subs Value -> (Int -> M_Subs a) -> M_Subs a
whenInt m f = m >>= \case ResInt v -> f v
                          _        -> empty

whenInts :: M_Subs Value -> ([Int] -> M_Subs a) -> M_Subs a
whenInts m f = results m >>= sequence . map (flip whenInt return . return) >>= f

whenTagged :: M_Subs Value -> (Tagged -> M_Subs a) -> M_Subs a
whenTagged m f = m >>= \case ResTagged v  -> f v
                             _            -> empty

whenTaggedHolds m f = m >>= \case ResTagged v -> is_in_virtual_state v >>= \case
                                                   True  -> f v
                                                   False -> empty
                                  _           -> empty

whenString :: M_Subs Value -> (String -> M_Subs a) -> M_Subs a
whenString m f = m >>= \case ResString s  -> f s
                             _            -> empty

eval :: Term -> M_Subs Value
eval t0 = case t0 of
  CurrentTime -> ResInt <$> get_time
  StringLit s -> return (ResString s)
  BoolLit b   -> return (ResBool b)
  IntLit i    -> return (ResInt i)
  Ref x       -> ResTagged <$> substitute_var x
  App d params-> do (dom,dom_filter) <- get_dom d
                    case dom of 
                      Products xs -> do 
                        let replacements = make_substitutions_of xs params
                        tes <- mapM (\(x,t) -> whenTagged (eval t) (return . (x,))) replacements
                        args <- modify_subs (`subsUnion` M.fromList tes) (mapM substitute_var xs)
                        modify_subs (`subsUnion` (M.fromList (zip xs args))) $ do
                          checkTrue (eval dom_filter)
                          return (ResTagged (Product args, d))
                      _           -> err (InternalError $ PrimitiveApplication d)
  Tag t d     -> eval t >>= flip tag d
  Untag t     -> eval t >>= untag
  Not t       -> whenBool (eval t) $ \b -> return (ResBool (not b))
  And t1 t2   -> whenBool (eval t1) $ \case 
                    False -> return (ResBool False)
                    True  -> whenBool (eval t2) (return . ResBool) 
  Or  t1 t2   -> whenBool (eval t1) $ \case 
                    True  -> return (ResBool True)
                    False -> whenBool (eval t2) (return . ResBool)
--  And t1 t2   -> whenBool (eval t1) $ \b1 -> whenBool (eval t2) (\b2 -> return (ResBool (and [b1,b2])))
--  Or  t1 t2   -> whenBool (eval t1) $ \b1 -> whenBool (eval t2) (\b2 -> return (ResBool (or [b1,b2])))
  Leq  t1 t2  -> whenInt  (eval t1) $ \v1 -> whenInt (eval t2) (\v2 -> return (ResBool (v1 <= v2)))
  Le   t1 t2  -> whenInt  (eval t1) $ \v1 -> whenInt (eval t2) (\v2 -> return (ResBool (v1 < v2)))
  Geq  t1 t2  -> whenInt  (eval t1) $ \v1 -> whenInt (eval t2) (\v2 -> return (ResBool (v1 >= v2)))
  Ge   t1 t2  -> whenInt  (eval t1) $ \v1 -> whenInt (eval t2) (\v2 -> return (ResBool (v1 > v2)))
  Mult  t1 t2 -> whenInt  (eval t1) $ \v1 -> whenInt (eval t2) (\v2 -> return (ResInt (v1 * v2)))
  Mod  t1 t2  -> whenInt  (eval t1) $ \v1 -> whenInt (eval t2) (\v2 -> return (ResInt (v1 `mod` v2)))
  Div  t1 t2  -> whenInt  (eval t1) $ \v1 -> whenInt (eval t2) (\v2 -> return (ResInt (v1 `div` v2)))
  Sub  t1 t2  -> whenInt  (eval t1) $ \v1 -> whenInt (eval t2) (\v2 -> return (ResInt (v1 - v2)))
  Add  t1 t2  -> whenInt  (eval t1) $ \v1 -> whenInt (eval t2) (\v2 -> return (ResInt (v1 + v2)))
  Eq  t1 t2   -> ((ResBool .) . (==)) <$> eval t1 <*> eval t2
  Neq t1 t2   -> ((ResBool .) . (/=)) <$> eval t1 <*> eval t2

  Sum xs t1   -> ResInt . sum <$> foreach xs (whenInt (eval t1) return)
  Count xs t1 -> ResInt . length <$> foreach xs (eval t1)
  Max xs t1   -> ResInt . (\xs -> if null xs then 0 else maximum xs) <$> foreach xs (whenInt (eval t1) return)
  Min xs t1   -> ResInt . (\xs -> if null xs then 0 else minimum xs) <$> foreach xs (whenInt (eval t1) return)
  When t1 t2  -> -- order matters because of constraint that equal variables have equal instantiations
                 -- however, with renaming some of these constraints can be lifted
                 -- this modification propagates in the same order as the evaluation order
                 eval t1 >>= \v1 -> whenBool (eval t2) (\case True -> return v1
                                                              False -> empty)
                 {- whenBool (eval t2) $ \case  True  -> eval t1 
                                              False -> empty-}
  Present t1  -> whenTagged (eval t1) (\v -> ResBool <$> is_in_virtual_state v)
  Violated t1 -> whenTagged (eval t1) (\v -> ResBool <$> is_violated v)
  Enabled t1  -> whenTagged (eval t1) (\v -> ResBool <$> is_enabled v)
  Exists xs t -> ResBool . not . null <$> results (foldr scope_var (checkTrue (eval t)) xs) 
  Forall xs t -> ResBool . and <$> results (foldr scope_var (whenBool (eval t) return) xs)

  Project t x -> whenTagged (eval (t)) $ \te@(e,d) -> case e of 
                    Product tes -> do (dom, _) <- get_dom d
                                      case dom of Products rs | length tes == length rs -> 
                                                    case elemIndex x rs of
                                                      Nothing -> empty
                                                      Just j  -> return (ResTagged (tes !! j))
                                                  _ -> empty
                    _ -> empty
    where elemIndex x rs = msum (zipWith op [0..] rs)
            where op j y | x == y    = Just j
                         | otherwise = Nothing


foreach :: [Var] -> M_Subs a -> M_Subs [a]
foreach xs m = results (foldr scope_var m xs)

tag :: Value -> DomId -> M_Subs Value
tag (ResInt i) d        = return $ ResTagged (Int i,d)
tag (ResString s) d     = return $ ResTagged (String s, d)
tag (ResTagged (v,_)) d = return $ ResTagged (v,d)
tag (ResBool b) _       = empty

untag :: Value -> M_Subs Value
untag (ResTagged (Int i, d))      = return $ ResInt i
untag (ResTagged (String s, d))   = return $ ResString s
untag (ResTagged (Product _, _))  = empty
untag (ResBool _)                 = empty
untag (ResInt _)                  = empty
untag (ResString _)               = empty


