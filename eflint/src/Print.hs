module Print where

import Prelude hiding (seq)

import Spec
import Interpreter  (Program(..))
import Data.List (intercalate, intersperse)

ppProgram :: Program -> String
ppProgram p = case p of
  Program p -> ppPhrase p 
  PSeq p1 p2 -> ppProgram p1 ++ "\n" ++ ppProgram p2
  ProgramSkip -> ""

ppPhrase :: Phrase -> String
ppPhrase p = case p of
  PQuery t          -> "?" ++ ppTerm t
  PDo t             -> ppTagged t
  PTrigger vs t     -> foreach vs $ ppTerm t
  Create vs t       -> "+" ++ foreach vs (ppTerm t)
  Terminate vs t    -> "-" ++ foreach vs (ppTerm t)
  Obfuscate vs t    -> "~" ++ foreach vs (ppTerm t)
  PSkip             -> ""
  PDeclBlock ds     -> unlines (map ppDecl ds)

ppCPhrase :: CPhrase -> String
ppCPhrase p = case p of 
  CPSkip          -> ""
  CPOnlyDecls     -> ""
  CSeq CPSkip p2  -> ppCPhrase p2
  CSeq p1 CPSkip  -> ppCPhrase p1
  CSeq p1 p2      -> seq [ppCPhrase p1,ppCPhrase p2]
  CDo te          -> ppTagged te
  CTrigger vs t   -> foreach vs $ ppTerm t
  CCreate vs t    -> "+" ++ foreach vs (ppTerm t)
  CTerminate vs t -> "-" ++ foreach vs (ppTerm t)
  CObfuscate vs t -> "~" ++ foreach vs (ppTerm t)
  CQuery t        -> "?" ++ ppTerm t
  CPDir dir       -> case dir of
   DirInv ty      -> "Invariant " ++ ty   

ppDecl :: Decl -> String
ppDecl td = case td of 
  PlaceholderDecl f t -> ppPlaceholder f t
  TypeExt ty clauses -> ppTypeExt ty clauses
  TypeDecl ty tspec -> ppDeclSpec ty tspec

ppTypeExt :: DomId -> [ModClause] -> String
ppTypeExt ty clauses = "Type extension of " ++ ty -- TODO, requires knowing kind of extended type

ppDeclSpec :: DomId -> TypeSpec -> String
ppDeclSpec d tspec = case kind tspec of
  Fact fspec  -> ppFact d tspec fspec
  Duty dspec  -> ppDuty d tspec dspec
  Event espec -> ppEvent d tspec espec
  Act aspec   -> ppAct d tspec aspec

ppDirective :: Directive -> String
ppDirective (Include fp) = "#include" ++ show fp
ppDirective (Require fp) = "#require" ++ show fp

ppClauses :: [ModClause] -> String
ppClauses = unwords . intersperse " " . concatMap ppClause

ppClause :: ModClause -> [String]
ppClause clause = case clause of
  ConditionedByCl pres | not (null pres) -> [ppPreConditions pres]
  DerivationCl dvs | not (null dvs) -> [ppDerivRules dvs]
  SyncCl ss | not (null ss) -> [] -- TODO
  PostCondCl effs | not (null effs) -> [ppPostConditions effs]
  ViolationCl vcs | not (null vcs) -> [ppViolationConds vcs] 
  EnforcingActsCl ds | not (null ds) -> [ppEnforcingActs ds] 
  _ -> []

ppAct d tspec aspec = ppAct' d (domain tspec) (domain_constraint tspec) 
                        [DerivationCl (derivation tspec) 
                        ,ConditionedByCl (conditions tspec)
                        ,PostCondCl (effects aspec)
                        ,SyncCl (syncs aspec)
                        ]

-- TODO print syncs(?)
ppAct' domainID domain domain_constr clauses = 
  "Act " ++ domainID ++ " Actor " ++ ppVar actor ++ " Recipient " ++ ppVar recipient ++ show_objects
    ++ ppConstraint (domain_constr)
    ++ ppClauses clauses
  where Products (actor:recipient:objects) = domain
        show_objects | null objects = ""
                     | otherwise    = " Related to " ++ intercalate ", " (map (\(Var x dec) -> x++dec) objects)

ppPostConditions :: [Effect] -> String
ppPostConditions effects = created_facts ++ terminated_facts ++ obfuscated_facts
 where (createds, terminateds, obfs) = foldr op ([],[],[]) effects
         where op e@(CAll _ _) (cs,ts,os) = (e:cs,ts,os) 
               op e@(TAll _ _) (cs,ts,os) = (cs,e:ts,os)
               op e@(OAll _ _) (cs,ts,os) = (cs,ts,e:os)
       created_facts | null createds = ""
                     | otherwise     = " Creates " ++ intercalate ", " (map ppEffect createds)
       terminated_facts | null terminateds = ""
                        | otherwise = " Terminates " ++ intercalate ", " (map ppEffect terminateds)
       obfuscated_facts | null obfs = ""
                        | otherwise = " Obfuscates " ++ intercalate ", " (map ppEffect obfs)

ppPreConditions :: [Term] -> String
ppPreConditions [] = ""
ppPreConditions ts = " Conditioned by " ++ intercalate ", " (map ppTerm ts)

ppEvent d tspec espec = ppEvent' d (domain tspec) (domain_constraint tspec)
                          [DerivationCl (derivation tspec)
                          ,ConditionedByCl (conditions tspec) 
                          ,PostCondCl (event_effects espec)]

ppEvent' domainID domain domain_constr clauses =
  "Event " ++ domainID ++ show_objects
    ++ ppConstraint domain_constr
    ++ ppClauses clauses
  where Products objects = domain
        show_objects | null objects = ""
                     | otherwise    = " Related to " ++ intercalate ", " (map (\(Var x dec) -> x++dec) objects)

ppEffect (CAll vs t) = foreach vs (ppTerm t)
ppEffect (TAll vs t) = foreach vs (ppTerm t)
ppEffect (OAll vs t) = foreach vs (ppTerm t)

ppFact :: DomId -> TypeSpec -> FactSpec -> String
ppFact d tspec fspec = 
  "Fact " ++ d ++ " Identified by " ++ ppDom (domain tspec) (domain_constraint tspec) 
    ++ ppPreConditions (conditions tspec)
    ++ ppDerivRules (derivation tspec)

ppDerivRules deriv = case deriv of 
                        [] -> "" 
                        holds | all isHolds holds -> "\n  Holds when " ++ intercalate ", " (map ppTerm ts)
                          where isHolds (HoldsWhen _) = True
                                isHolds _ = False
                                ts = concatMap op holds
                                  where op (HoldsWhen t) = [t]
                                        op _             = []
                        ts -> "\n  Derived from " ++ intercalate ", " (map ppDeriv ts)

ppDuty d tspec dspec = ppDuty' d (domain tspec) (domain_constraint tspec)
                              [DerivationCl (derivation tspec)
                              ,ConditionedByCl (conditions tspec)
                              ,ViolationCl (violated_when dspec)]

ppDuty' domainID domain domain_constr clauses = 
  "Duty " ++ domainID ++ " Holder " ++ ppVar holder ++ " Claimant " ++ ppVar claimant ++ show_objects
          ++ ppConstraint domain_constr
          ++ ppClauses clauses
   where Products (holder:claimant:objects) = domain
         show_objects | null objects = ""
                      | otherwise    = " Related to " ++ intercalate ", " (map (\(Var x dec) -> x++dec) objects)

ppViolationConds :: [Term] -> String
ppViolationConds ts | null ts = ""
                    | otherwise = "\n  Violated when " ++ intercalate ", " (map ppTerm ts)

ppEnforcingActs :: [DomId] -> String
ppEnforcingActs ds | null ds = ""
                   | otherwise = "\n  Enforced by " ++ intercalate ", " ds

ppDeriv :: Derivation -> String
ppDeriv (HoldsWhen a) = "<HOLDS WHEN>"
ppDeriv (Dv xs t)     = foreach xs (ppTerm t) 

ppDom :: Domain -> Term -> String
ppDom dom c = types ++ ppConstraint c
  where types = case dom of
                  Strings ss  -> intercalate ", " ss
                  Ints is     -> intercalate ", " (map show is)
                  AnyString   -> "String"
                  AnyInt      -> "Int"
                  -- Products rs -> intercalate " * " (map show rs)
                  Products rs -> intercalate " * " (map ppVar rs)
                  Time        -> "<TIME>"

ppConstraint c = case c of  BoolLit True -> ""
                            (Exists [] (BoolLit True)) -> ""
                            _         -> " Where " ++ ppTerm c

ppTerm :: Term -> String
ppTerm t = case t of
  Not t -> app "Not" [ppTerm t]
  And t1 t2 -> app_infix "&&" (ppTerm t1) (ppTerm t2)
  Or t1 t2 -> app_infix "||" (ppTerm t1) (ppTerm t2)
  BoolLit b -> show b
  Leq t1 t2 -> app_infix "<=" (ppTerm t1) (ppTerm t2)
  Geq t1 t2 -> app_infix ">=" (ppTerm t1) (ppTerm t2)
  Ge t1 t2 -> app_infix ">" (ppTerm t1) (ppTerm t2)
  Le t1 t2 -> app_infix "<" (ppTerm t1) (ppTerm t2)
  Sub t1 t2 -> app_infix "-" (ppTerm t1) (ppTerm t2)
  Add t1 t2 -> app_infix "+" (ppTerm t1) (ppTerm t2)
  Mult t1 t2 -> app_infix "*" (ppTerm t1) (ppTerm t2)
  Mod t1 t2 -> app_infix "%" (ppTerm t1) (ppTerm t2)
  Div t1 t2 -> app_infix "/" (ppTerm t1) (ppTerm t2)
  IntLit i -> show i
  StringLit s -> show s
  Eq t1 t2 -> app_infix "==" (ppTerm t1) (ppTerm t2)
  Neq t1 t2 -> app_infix "!=" (ppTerm t1) (ppTerm t2)
  Exists vs t -> exists vs (ppTerm t)
  Forall vs t -> forall vs (ppTerm t)
  Count vs t  -> "Count" ++ foreach vs (ppTerm t)
  Sum vs t    -> "Sum" ++ foreach vs (ppTerm t)
  Max vs t    -> "Max" ++ foreach vs (ppTerm t)
  Min vs t    -> "Min" ++ foreach vs (ppTerm t)
  When t1 t2  -> app_infix "When" (ppTerm t1) (ppTerm t2)
  Present t   -> app "Holds" [ppTerm t]
  Violated t  -> app "Violated" [ppTerm t] 
  Enabled t   -> app "Enabled" [ppTerm t] 
  Project t v -> app "" [ppTerm t] ++ "." ++ ppVar v
  Tag t d     -> app d [ppTerm t]
  Untag t     -> app "Untag" [ppTerm t]
  Ref v       -> ppVar v
  App d args  -> case args of
    Left ts   -> app d $ map ppTerm ts
    Right ms  -> app d $ map ppMod ms
  CurrentTime -> "<TIME>"

ppVar :: Var -> String
ppVar (Var x dec) = x ++ dec

ppMod :: Modifier -> String
ppMod (Rename v t) = ppVar v ++ "=" ++ ppTerm t 

ppPlaceholder :: DomId -> DomId -> String
ppPlaceholder var for = "Placeholder " ++ var ++ " For " ++ for

seq :: [String] -> String
seq = intercalate ".\n" 

foreach = binder "Foreach"
exists = binder "Exists"
forall = binder "Forall"
count = binder "Count"

binder :: String -> [Var] -> String -> String
binder op [] str = str
binder op vs str = "(" ++ op ++ " " ++ intercalate "," (map ppVar vs) ++ ": " ++ str ++ ")"

app :: String -> [String] -> String
app cons args = cons ++ "(" ++ intercalate "," args ++ ")"

app_infix :: String -> String -> String -> String
app_infix op x y = x ++ " " ++ op ++ " " ++ y
