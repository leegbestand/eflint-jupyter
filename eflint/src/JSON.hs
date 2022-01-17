{-# LANGUAGE DeriveGeneric, DuplicateRecordFields, TupleSections #-}

module JSON where

import Spec hiding (FactSpec(actor))
import qualified Spec as Spec

import Data.Aeson hiding (object)
import Data.Maybe
import Data.Char (toLower, isUpper, isSpace)
import qualified Data.Map as M

import GHC.Generics

decode_json_file :: String -> IO (Either String Spec)
decode_json_file f = fmap tModel <$> eitherDecodeFileStrict f

tExpr :: Expression -> Term
tExpr e = case e of 
  RefExpr v -> Ref (tVariable v) 
  MultiExpr m -> case (expression :: Multi -> String) m of
    "AND" -> foldr And (BoolLit True) (map tExpr (fromJust (operands m)))
    "OR"  -> foldr Or  (BoolLit False) (map tExpr (fromJust (operands m)))
    "NOT" -> Not (tExpr (fromJust (operand m)))
    "LIST"-> tExpr (fromJust (items m))
    cons  -> error ("JSON2SPEC: unknown expression type: " ++ cons)

tAct :: Act -> (DomId, TypeSpec)
tAct a = (act a,) $ TypeSpec {
    kind = Spec.Act aspec
  , domain = Products args 
  , domain_constraint = BoolLit True
  , derivation = [HoldsWhen condition_term]
  , closed = True 
  , conditions = []  
  }
  where condition_term = foldr And (BoolLit True) $ 
                          [ tExpr (preconditions a) 
                          , Ref (no_decoration (actor a))
                          , Ref (no_decoration (interested_party a))] ++
                          (map Ref objects)
        args = [no_decoration (actor a), no_decoration (interested_party a)] ++ objects
        aspec = ActSpec { effects = map mkT ((terminate :: Act -> [OptBinder]) a) 
                                 ++ map mkC ((create :: Act -> [OptBinder]) a)
                        , syncs = [] }
          where mkT ob = case ob of ImplicitDV expr -> tAll [] expr
                                    ExplicitDV b    -> tAll (vars b) (binder_expression b)
                  where tAll vs expr = TAll (map tVariable vs) (tExpr expr) 
                mkC ob = case ob of ImplicitDV expr -> cAll [] expr
                                    ExplicitDV b    -> cAll [] (binder_expression b)
                  where cAll vs expr = CAll (map tVariable vs) (tExpr expr) 
        objects | all isSpace (object a) = []
                | otherwise              = [no_decoration (object a)]


tDuty :: Duty -> (DomId, TypeSpec)
tDuty d = (duty d,) $ TypeSpec {
    kind = Spec.Duty dspec
  , domain = Products $ [no_decoration (duty_holder d)
                        ,no_decoration (claimant d)] ++ objects
  , domain_constraint = BoolLit True
  , derivation = case (derivation :: Duty -> Maybe Binder) d of 
      Nothing -> [] 
      Just b  -> [dv (duty d) (vars b) (binder_expression b)]
  , closed = True
  , conditions = []
  }
  where dspec = DutySpec {enforcing_acts = maybe [] (:[]) (enforcing d)
                         ,violated_when = []}
        objects | all isSpace (duty_components d) = []
                | otherwise                       = [no_decoration (duty_components d)]

tFact :: Fact -> (DomId, TypeSpec)
tFact f = (fact f,) $ TypeSpec {
    kind = Spec.Fact fspec 
  , domain = case (domain :: Fact -> Maybe JSON.Domain) f of 
                Nothing  -> case function f of 
                              ImplicitDV (RefExpr (BaseVar "[]")) -> AnyString 
                              _                                   -> Products []
                Just dom -> tDomain dom
  , domain_constraint = BoolLit True
  , derivation = case function f of
      ImplicitDV expr  -> case expr of 
          RefExpr (BaseVar "[]")    -> [] --Just (Dv [] (When (App (fact f) (Right [])) (BoolLit True)))
          RefExpr (BaseVar "<<>>")  -> [] 
          expr                      -> [dv (fact f) [] expr]
      ExplicitDV d                  -> [dv (fact f) (vars d) (binder_expression d)]
  , closed = False
  , conditions = []
  }
  where fspec = FactSpec { invariant = False, Spec.actor = False }

dv :: String -> [Variable] -> Expression -> Spec.Derivation
dv cons vars expr = Dv (map tVariable vars) (When (App cons (Right [])) (tExpr expr))

tDomain :: JSON.Domain -> Spec.Domain
tDomain d = case type_constructor d of 
  "ANY-STRING"    -> AnyString
  "ANY-INT"       -> AnyInt
  "STRING"        -> Strings (fromJust (strings d))
  "INT"           -> Ints (fromJust (ints d))
  "PRODUCT"       -> Products (map tVariable (fromJust (arguments d)))
  cons            -> error ("unknown type-constructor: " ++ cons)

tVariable :: Variable -> Spec.Var
tVariable (BaseVar var) = Var var ""
tVariable (DecVar (DecoratedVariable x d)) = Var x d 

tModel :: Model -> Spec
tModel m = Spec { decls = M.fromList $  
                            map tAct (acts m) ++ 
                            map tDuty (duties m) ++   
                            map tFact (facts m)
                , aliases = M.empty}

unhyphen :: String -> String
unhyphen = map op
  where op '-' = '_'
        op c   = c

hyphen :: String -> String
hyphen = map op
  where op '_' = '-'
        op c   = c

process_string :: String -> String
process_string = id
{-
process_string ('<':'<':s) = reverse (drop 2 (reverse (concatMap replace s)))
process_string ('<':s) = reverse (drop 1 (reverse (concatMap replace s)))
process_string ('[':s) = reverse (drop 1 (reverse (concatMap replace s)))
process_string s = s
-}

replace :: Char -> String
replace ',' = ""
replace '-' = ""
replace c | isUpper c = [toLower c]
replace c = [c]

customOptions = defaultOptions { fieldLabelModifier = hyphen, sumEncoding = UntaggedValue}

type BaseVariable = String
data Variable = BaseVar BaseVariable
              | DecVar DecoratedVariable
              deriving (Show, Generic)
instance ToJSON Variable where
  toJSON = genericToJSON customOptions
  toEncoding = genericToEncoding customOptions 
instance FromJSON Variable where
  parseJSON = genericParseJSON customOptions 

data DecoratedVariable = DecoratedVariable {
        base      :: BaseVariable
      , modifier  :: String
      } deriving (Show, Generic)
instance ToJSON DecoratedVariable where
  toJSON = genericToJSON customOptions
  toEncoding = genericToEncoding customOptions 
instance FromJSON DecoratedVariable where
  parseJSON = genericParseJSON customOptions 

data Model = Model {
    acts    :: [Act]
  , facts   :: [Fact]
  , duties  :: [Duty]
  } deriving (Show, Generic) 
instance ToJSON Model where
  toEncoding = genericToEncoding (defaultOptions { constructorTagModifier = unhyphen, sumEncoding = UntaggedValue} )
instance FromJSON Model where

data Act = Act {
    act               :: String
  , actor             :: String
  , action            :: String
  , object            :: String
  , interested_party  :: String
  , preconditions     :: Expression 
  , create            :: [OptBinder]
  , terminate         :: [OptBinder]
  , derivation        :: Maybe Binder
  , sources           :: Maybe [Source]
  , explanation       :: Maybe String
  , version           :: Maybe String
  , reference         :: Maybe References
  , juriconnect       :: Maybe String
  , sourcetext        :: Maybe String
  } deriving (Show, Generic)
instance ToJSON Act where
  toJSON = genericToJSON customOptions
  toEncoding = genericToEncoding customOptions 
instance FromJSON Act where
  parseJSON = genericParseJSON customOptions 

data Fact = Fact {
    fact        :: String
  , function    :: OptBinder
  , domain      :: Maybe JSON.Domain
  , sources     :: Maybe [Source]
  , explanation :: Maybe String
  , version     :: Maybe String
  , reference   :: Maybe References 
  , juriconnect :: Maybe String
  , sourcetext  :: Maybe String
  } deriving (Show, Generic)
instance ToJSON Fact where
  toJSON = genericToJSON customOptions
  toEncoding = genericToEncoding customOptions 
instance FromJSON Fact where
  parseJSON = genericParseJSON customOptions 

data Domain = Domain {
    type_constructor  :: String
  , arguments         :: Maybe [Variable]
  , strings           :: Maybe [String]
  , ints              :: Maybe [Int]
  } deriving (Show, Generic)
instance ToJSON JSON.Domain where
  toJSON = genericToJSON customOptions
  toEncoding = genericToEncoding customOptions 
instance FromJSON JSON.Domain where
  parseJSON = genericParseJSON customOptions 

data Duty = Duty {
    duty            :: String
  , duty_components :: String
  , duty_holder     :: String
  , claimant        :: String
  , create          :: String
  , terminate       :: String
  , enforcing       :: Maybe String
  , derivation      :: Maybe Binder
  , sources         :: Maybe [Source]
  , explanation     :: Maybe String
  , version         :: Maybe String
  , reference       :: Maybe References
  , juriconnect     :: Maybe String
  , sourcetext      :: Maybe String
  }   deriving (Show, Generic)
instance ToJSON Duty where
  toJSON = genericToJSON customOptions
  toEncoding = genericToEncoding customOptions 
instance FromJSON Duty where
  parseJSON = genericParseJSON customOptions 

data OptBinder = ExplicitDV Binder
               | ImplicitDV Expression 
               deriving (Show, Generic)
instance ToJSON OptBinder where
  toJSON = genericToJSON customOptions
  toEncoding = genericToEncoding customOptions 
instance FromJSON OptBinder where
  parseJSON = genericParseJSON customOptions 

data Binder = Binder {
        vars               :: [Variable]
      , binder_expression  :: Expression
      } deriving (Show, Generic)
instance ToJSON Binder where
  toJSON = genericToJSON customOptions
  toEncoding = genericToEncoding customOptions 
instance FromJSON Binder where
  parseJSON = genericParseJSON customOptions 

data Source = Source {
    validFrom       :: String
  , validTo         :: Maybe String
  , citation        :: String
  , juriconnect     :: String
  , text            :: String
  } deriving (Show, Generic)
instance ToJSON Source where
  toJSON = genericToJSON customOptions
  toEncoding = genericToEncoding customOptions 
instance FromJSON Source where
  parseJSON = genericParseJSON customOptions

data Expression = RefExpr Variable 
                | MultiExpr Multi 
                deriving (Show, Generic)
instance ToJSON Expression where
  toJSON = genericToJSON customOptions
  toEncoding = genericToEncoding customOptions 
instance FromJSON Expression where
  parseJSON = genericParseJSON customOptions

data Multi = Multi {
    expression  :: String
  , operands    :: Maybe [Expression]
  , operand     :: Maybe Expression
  , items       :: Maybe Expression
  } deriving (Show, Generic)
instance ToJSON Multi where
instance FromJSON Multi where

data References = RSingle String
                | RMulti  [String]
                deriving (Show, Generic)
instance ToJSON References where
  toEncoding = genericToEncoding customOptions
  toJSON = genericToJSON customOptions 
instance FromJSON References where
  parseJSON = genericParseJSON customOptions
