{-# LANGUAGE OverloadedStrings, LambdaCase, MultiParamTypeClasses, FlexibleInstances #-}

module ProtExplorer where

import Language.Explorer.Tools.Protocol
import qualified Language.Explorer.Monadic as EI
import Interpreter
import Data.Aeson hiding (Value(..),Options(..))
import qualified Data.Aeson as JSON
import Spec hiding (Value(..))
import State
import Util
import Options
import StaticEval
import Parse
import Print (ppProgram)
import Sim (make_initial_state)

import Control.Monad
import Control.Applicative

import Data.Text (unpack, pack)
import Data.Function (on)
import Text.Read (readMaybe)
import Data.List (isSuffixOf, sortBy, (\\))
import qualified Data.Set as S

type Ref = Int -- state identifier
type Path = [(Node, (Program, [Output]), Node)]
type Node = (Ref, Config)


instance ToJSON Program where
    toJSON p = JSON.String . pack $ ppProgram p

instance ToJSON Config where
    toJSON c = JSON.object
      [ "all-enabled-transitions" .= JSON.toJSON (map TaggedJSON (rest_enabled c))
      , "all-disabled-transitions" .= JSON.toJSON (map TaggedJSON (rest_disabled c))
      , "all-duties" .= JSON.toJSON (rest_duties c)]


instance ExplorerPostValue Program Config [Output] where
  postExecute ex_pre ex_post out =  object
    [ "created_facts"    .= toJSON (map TaggedJSON created)
    , "terminated_facts" .= toJSON (map TaggedJSON terminated)
    , "violations"       .= toJSON rep_viols
    ]
    where facts_from = state_holds (cfg_state $ EI.config ex_pre)
          facts_to   = state_holds (cfg_state $ EI.config ex_post)
          created    = facts_to \\ facts_from
          terminated = facts_from \\ facts_to
          rep_viols  = violations out



interface :: IO ()
interface = serve "3001" (EI.mkExplorerNoSharing defInterpreter initialConfig) parser


parser :: String -> Maybe Program
parser s = case parse_component syn_phrases s of
  (Left error) -> Nothing
  (Right v) -> Just $ collapse_programs . convert_programs $ v

defInterpreter :: Monad m => Program -> Config -> m (Maybe Config, [Output])
defInterpreter p c = return . getOutput $ interpreter p c



data Command    = ActionCommand DomId Term Term [Term] Bool
                | CmdTrigger Term Bool
                | CreateEvent Term
                | TerminateEvent Term
                | QueryCommand Term
                | StringInstances DomId [String]
                | IntInstances DomId [Int]
                | Revert Int
                | Status (Maybe Int)
                | Kill
                | GetFacts
                | History (Maybe Int)
                | Heads
                | Phrase String

instance FromJSON Command where
  parseJSON = withObject "Command" $ \v -> do
                cmd <- v .: "command"
                case cmd::String of
                  "create"      -> CreateEvent . value_to_term <$> v .: "value"
                  "terminate"   -> TerminateEvent . value_to_term <$> v .: "value"
                  "test-present"-> QueryCommand . value_to_term <$> v .: "value"
                  "test-absent" -> QueryCommand . Not . value_to_term <$> v .: "value"
                  "enabled"     -> QueryCommand . Enabled . value_to_term <$> v .: "value"
                  "revert"      -> Revert <$> v .: "value"
                  "action"      -> full_action <|> trigger_action
                    where full_action =
                            actionCommand <$>
                                    v .: "act-type" <*> v .: "actor" <*> v .: "recipient"
                               <*>  v .: "objects"  <*> maybe_force v
                          trigger_action = CmdTrigger . value_to_term <$> v .: "value" <*> maybe_force v
                          actionCommand d a r os = ActionCommand d (to_term a) (to_term r) (map to_term os)
                  "status"      -> Status <$> v .: "state"
                                <|> return (Status Nothing)
                  "history"     ->  History <$> v .: "state"
                                <|> return (History Nothing)
                  "trace-heads" -> return Heads
                  "kill"        -> return Kill
                  "phrase"      -> Phrase <$> v .: "text"
                  "event"       -> CmdTrigger . value_to_term <$> v .: "value" <*> maybe_force v
                  "instances-of"-> StringInstances <$> v .: "fact-type" <*> v .: "instances"
                               <|> IntInstances <$> v .: "fact-type" <*> v .: "instances"
                  "facts"       -> return GetFacts
                  _             -> mzero

maybe_force v = v .: "force" <|> return False

data Value      = Atom DomId (Either String Int)
                | Composite DomId [Value]

data StringOrValue = ST String | VT Value

instance FromJSON StringOrValue where
  parseJSON v = case v of
    JSON.String str -> return (ST (unpack str))
    JSON.Object obj -> VT <$> parseJSON v
    _               -> fail ("looking for a string or a value, not a " ++ show v)

to_term :: StringOrValue -> Term
to_term (ST s) = StringLit s
to_term (VT v) = value_to_term v

tag_of :: Value -> DomId
tag_of (Atom d _) = d
tag_of (Composite d _) = d

value_to_term :: Value -> Term
value_to_term v = case v of
  Atom d (Left s)  -> App d (Left [StringLit s])
  Atom d (Right i) -> App d (Left [IntLit i])
  Composite d vs   -> App d (Right $ map value_to_modifier vs)

value_to_modifier :: Value -> Modifier
value_to_modifier v = Rename (no_decoration (tag_of v)) (value_to_term v)

instance FromJSON Value where
  parseJSON = withObject "Value" $ \v ->
                    (\c i -> Atom c (Right i)) <$> v .: "fact-type" <*> v .: "value"
                <|> (\c s -> Atom c (Left s))  <$> v .: "fact-type" <*> v .: "value"
                <|> Composite <$> v .: "fact-type" <*> v .: "value"
                <|> Composite <$> v .: "fact-type" <*> v .: "arguments"

data Response   = InvalidCommand String
                | InvalidInput String -- parse error
                | CommandSuccess Int (S.Set Violation)
                                     (S.Set ExecutedTransitions)
                                     (S.Set Error) -- errors: compilation + transition
                                     [QueryRes]         -- query results
                                     (S.Set Tagged) -- new duties
                                     (S.Set Tagged) -- all duties in the current state
                                     (S.Set Tagged) -- newly enabled transitions
                                     (S.Set Tagged) -- newly disabled transitions
                                     (S.Set (Tagged, Bool)) -- all transitions
                | InvalidState
                | GiveFacts [Tagged]
                | GivePath Path
                | GiveNodes [Node]
                | ByeBye

instance ToJSON Response where
  toJSON (InvalidCommand err) = object [ "response" .= JSON.String "invalid command", "message" .= toJSON err ]
  toJSON (CommandSuccess i vs outs errs qress new_duties all_duties new_enabled new_disabled all_transitions) =
    object [ "response"   .= JSON.String "success"
           , "violations" .= toJSON vs
           , "output-events" .= toJSON outs
           , "errors"     .= toJSON errs
           , "query-results" .= toJSON qress
           , "new-state"  .= toJSON i
           , "new-duties" .= toJSON (map TaggedJSON $ S.toList new_duties)
           , "new-enabled-transitions" .= toJSON (map TaggedJSON $ S.toList new_enabled)
           , "new-disabled-transitions" .= toJSON (map TaggedJSON $ S.toList new_disabled)
           , "all-duties" .= toJSON (map TaggedJSON $ S.toList all_duties)
           , "all-disabled-transitions" .= toJSON (map TaggedJSON dis_transitions)
           , "all-enabled-transitions" .= toJSON (map TaggedJSON en_transitions)
           ]
   where en_transitions = map fst $ filter snd $ S.toList all_transitions
         dis_transitions = map fst $ filter (not . snd) $ S.toList all_transitions
  toJSON InvalidState       = object [ "response" .= JSON.String "invalid state" ]
  toJSON (InvalidInput err) = object [ "response" .= JSON.String "invalid input"
                                     , "error"    .= toJSON err ]
  toJSON ByeBye             = object [ "response"  .= JSON.String "bye world.." ]
  toJSON (GiveFacts tes)    = object [ "values" .= toJSON (map TaggedJSON tes) ]
  toJSON (GiveNodes nodes)  = object [ "nodes"  .= toJSON (map toJSONNode nodes) ]
    where toJSONNode (sid, cfg) =
            object [ "state_id"       .= toJSON sid
                   , "state_contents" .= toJSON (map TaggedJSON (state_holds (cfg_state cfg))) ]
  toJSON (GivePath edges)   = object [ "edges"  .= toJSON (map toJSONEdge edges') ]
    where edges' = sortBy (on compare (\((sid,_),_,_) -> sid)) edges
          toJSONEdge ((sid_from,ctx_from), (phr, output), (sid_to, ctx_to)) =
            object [ "source_id"        .= toJSON sid_from
                   , "source_contents"  .= toJSON (map TaggedJSON facts_from)
                   , "phrase"           .= toJSON (ppProgram phr)
                   , "target_id"        .= toJSON sid_to
                   , "target_contents"  .= toJSON (map TaggedJSON facts_to)
                   , "created_facts"    .= toJSON (map TaggedJSON created)
                   , "terminated_facts" .= toJSON (map TaggedJSON terminated)
                   , "violations"       .= toJSON rep_viols
                   , "output"           .= toJSON output
                   ]
           where facts_from = state_holds (cfg_state ctx_from)
                 facts_to   = state_holds (cfg_state ctx_to)
                 created    = facts_to \\ facts_from
                 terminated = facts_from \\ facts_to
                 rep_viols  = violations output

instance ToJSON Violation where
  toJSON (TriggerViolation te is_action) =
    object [ "violation" .= JSON.String "trigger"
           , "value"     .= toJSON (TaggedJSON te)
           , "is-action" .= JSON.Bool is_action ]
  toJSON (DutyViolation te) =
    object [ "violation" .= toJSON ("duty"::String)
           , "value"     .= toJSON (TaggedJSON te) ]
  toJSON (InvariantViolation d) =
    object [ "violation" .= toJSON ("invariant"::String)
           , "invariant" .= toJSON d ]

instance ToJSON QueryRes where
  toJSON qres = case qres of
    QuerySuccess -> "success"
    QueryFailure -> "failure"

instance ToJSON Error where
  toJSON err = case err of
    NonDeterministicTransition -> object [ "error-type" .= JSON.String "non-deterministic transition"]
    NotTriggerable te -> object ["error-type" .= JSON.String "not triggerable"
                                    ,"value" .= TaggedJSON te ]
    CompilationError err  -> object ["error-type" .= JSON.String "compilation error"
                                    ,"error" .= toJSON err]
    RuntimeError (MissingInput te) -> 
      object ["error-type" .= JSON.String "missing input"
             ,"error" .= JSON.toJSON (TaggedJSON te) ]
    RuntimeError (InternalError (EnumerateInfiniteDomain d dom)) ->
      object ["error-type" .= JSON.String "enumerating infinite domain"
             ,"error" .= toJSON (d, dom) ]
    RuntimeError (InternalError (MissingSubstitution var)) ->
      object ["error-type" .= JSON.String "missing substitution"
             ,"error" .= toJSON var ]
    RuntimeError (InternalError (PrimitiveApplication d)) ->
      object ["error-type" .= JSON.String "primitive application"
             ,"error" .= d ]
    RuntimeError (InternalError (UndeclaredType d)) ->
      object ["error-type" .= JSON.String "undeclared type"
             ,"error" .= d ]

instance ToJSON Output where
  toJSON (ExecutedTransitions e)  = toJSON e
  toJSON (Violation v)            = toJSON v
  toJSON (QueryRes r)             = toJSON r
  toJSON (ErrorVal e)             = toJSON e


instance ToJSON Elem where
  toJSON (String s) = toJSON s
  toJSON (Int i) = toJSON i
  toJSON (Product p) = toJSON p
