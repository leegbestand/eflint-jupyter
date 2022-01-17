module State where

import Spec

import Data.Maybe (isJust)
import qualified Data.Map as M

import Control.Applicative (empty)

data Info   = Info {
                value :: Bool
              , from_sat :: Bool -- whether assignment came from saturation process
              }
              deriving (Eq, Read, Show)

data State =  State {
                  contents :: M.Map Tagged Info  -- meta-info about components
              ,   time :: Int
              }
              deriving Eq

data Transition = Transition {
                    tagged :: Tagged
                  , exist :: Bool
                  }  
                  deriving (Ord, Eq, Show, Read)

type InputMap = M.Map Tagged Bool

type Store = M.Map Tagged Assignment 

data Assignment = HoldsTrue
                | HoldsFalse
                | Unknown
                deriving (Eq, Ord, Show, Read)

emptyInput :: InputMap
emptyInput = M.empty

emptyStore = M.empty

-- | based union over stores, precedence HoldsTrue > HoldsFalse > Unknown
store_union :: Store -> Store -> Store
store_union = M.unionWith op
  where op HoldsTrue _      = HoldsTrue
        op _ HoldsTrue      = HoldsTrue
        op HoldsFalse _     = HoldsFalse
        op _ HoldsFalse     = HoldsFalse
        op Unknown Unknown  = Unknown
store_unions :: [Store] -> Store
store_unions = foldr store_union emptyStore

make_assignments :: Store -> State -> State
make_assignments = flip (M.foldrWithKey op)
  where op te HoldsTrue   = create te
        op te HoldsFalse  = terminate te
        op te Unknown     = obfuscate te

derive :: Tagged -> State -> State
derive te s = s { contents = M.alter adj te (contents s) }
  where adj Nothing     = Just $ Info{ value = True, from_sat = True }
        adj (Just info) = Just info

derive_all :: [Tagged] -> State -> State
derive_all = flip (foldr derive)

create :: Tagged -> State -> State
create te s = s { contents = M.insert te Info{ value = True, from_sat = False } (contents s) }

create_all :: [Tagged] -> State -> State
create_all = flip (foldr create)

terminate :: Tagged -> State -> State
terminate te s = s { contents = M.insert te Info{ value = False, from_sat = False } (contents s) }

terminate_all :: [Tagged] -> State -> State
terminate_all = flip (foldr terminate)

obfuscate :: Tagged -> State -> State
obfuscate te s = s { contents = M.delete te (contents s) }

obfuscate_all :: [Tagged] -> State -> State
obfuscate_all = flip (foldr obfuscate)

-- | assumes the instance of a closed type
holds :: Tagged -> State -> Bool
holds te s = maybe False ((==True) . value) (M.lookup te (contents s))

emptyState = State { contents = M.empty, time = 0 }

increment_time state = state { time = 1 + (time state) }

instance Show State where
  show state = unlines $ 
      [ show_component c ++ " = " ++ show (value m)
      | (c,m) <- M.assocs (contents state)
      ]

-- instance ToJSON State where
-- toJSON state = toJSON (map TaggedJSON (state_holds state)) 

state_holds :: State -> [Tagged]
state_holds state = [ te | (te, m) <- M.assocs (contents state), True == value m ]

state_input_holds :: State -> InputMap -> [Tagged]
state_input_holds state inpm = state_holds state ++ input_holds inpm

state_not_holds :: State -> [Tagged]
state_not_holds state = [ te | (te, m) <- M.assocs (contents state), False == value m ]

input_holds :: InputMap -> [Tagged]
input_holds inpm = [ te |  (te, True) <- M.assocs inpm ]

data Context = Context {
                  ctx_spec        :: Spec --mutable 
                , ctx_state       :: State --mutable 
                , ctx_transitions :: [Transition] -- (label * enabled?) -- replaceable
                , ctx_duties      :: [Tagged] -- replaceable
                }

-- mutable means c0 ; c1 results in c1 adding to c0 with possible override
-- appendable means c0 ; c1 results in effects of c0 and c1 being concatenated
-- replaceable means c0 ; c1 results in effect of c1

emptyContext spec = 
               Context { 
                  ctx_spec = spec
                , ctx_state = emptyState
                , ctx_transitions = empty
                , ctx_duties = empty }

data TransInfo = TransInfo {
                  trans_tagged      :: Tagged 
                , trans_assignments :: Store  -- includes sync'ed effects
                , trans_forced      :: Bool -- whether this or a sync'ed transition is not enabled was forced (i.e. was not enabled)
                , trans_actor       :: Maybe Tagged
                , trans_syncs       :: [TransInfo] -- the transitions this transitions sync'ed with 
                }
                deriving (Eq, Ord, Show, Read) 

trans_is_action :: TransInfo -> Bool
trans_is_action = isJust . trans_actor

data Violation = DutyViolation      Tagged
               | TriggerViolation   TransInfo 
               | InvariantViolation DomId
               deriving (Ord, Eq, Show, Read) 

data QueryRes = QuerySuccess
              | QueryFailure
              deriving (Ord, Eq, Show, Read)

data Error = -- trigger errors
             NotTriggerable Tagged
           | NonDeterministicTransition
           | CompilationError String
           | RuntimeError RuntimeError
           deriving (Eq, Ord, Show, Read) 

data RuntimeError
      = MissingInput Tagged 
      | InternalError InternalError
      deriving (Eq, Ord, Show, Read) 

data InternalError 
      = EnumerateInfiniteDomain DomId Domain 
      | MissingSubstitution Var
      | PrimitiveApplication DomId
      | UndeclaredType DomId 
      deriving (Eq, Ord, Show, Read)

print_error :: Error -> String
print_error (NotTriggerable te) = "not a triggerable instance: " ++ ppTagged te
print_error (NonDeterministicTransition) = "non-deterministic transition attempt"
print_error (CompilationError err) = err
print_error (RuntimeError err) = print_runtime_error err

print_runtime_error :: RuntimeError -> String
print_runtime_error (MissingInput te) = "missing input assignment for: " ++ ppTagged te
print_runtime_error (InternalError err) = "INTERNAL ERROR " ++ print_internal_error err

print_internal_error :: InternalError -> String
print_internal_error (EnumerateInfiniteDomain d AnyString) = "cannot enumerate all strings of type: " ++ d
print_internal_error (EnumerateInfiniteDomain d AnyInt) = "cannot enumerate all integers of type: " ++ d
print_internal_error (EnumerateInfiniteDomain d _) = "cannot enumerate all instances of type: " ++ d
print_internal_error (MissingSubstitution (Var base dec)) = "variable " ++ base ++ dec ++ " not bound"
print_internal_error (PrimitiveApplication d) = "application of primitive type: " ++ d
print_internal_error (UndeclaredType d) = "undeclared type: " ++ d
