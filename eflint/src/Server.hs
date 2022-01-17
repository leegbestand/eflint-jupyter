{-# LANGUAGE OverloadedStrings, LambdaCase, DeriveGeneric #-}
{-# LANGUAGE RecordWildCards, DuplicateRecordFields #-}

import Spec hiding (Value(..))
import State
import Util
import Options
import StaticEval
import Parse
import Print (ppProgram)
import NewExplorer hiding (Instruction(Revert), Response)
import Interpreter
import JSON(decode_json_file)
import qualified NewExplorer as Explorer
import qualified Language.Explorer.Pure as EI

import Control.Monad
import Control.Applicative

import Data.Function (on)
import Data.Text (unpack)
import Text.Read (readMaybe)
import Data.List (isSuffixOf, sortBy, (\\))
import qualified Data.Set as S
import qualified Data.Map as M

import System.IO (hGetLine, hPutStrLn, hClose, IOMode(ReadWriteMode))
import System.IO.Error
import System.Environment (getArgs)
import System.Directory
import System.FilePath
import Network.Socket
import qualified Data.ByteString.Lazy.Char8 (pack,unpack)

import GHC.Generics
import Data.Aeson hiding (String, Value(..),Options(..))
import qualified Data.Aeson as JSON

-- determines which variant of execution graph to use
init_explorer = init_tree_explorer

main :: IO ()
main = do
  args <- getArgs
  cdir <- getCurrentDirectory
  case args of
    (f:p:opts) | ".eflint" `isSuffixOf` f, Just port_nr <- readMaybe p ->  do
                  fcont <- readFile f
                  opts' <- run_options (["-i",takeDirectory f,"-i",cdir] ++ opts)
                  case parse_component syn_directives_phrases fcont of
                    Left err1 -> case parse_flint fcont of
                      Left err2 -> do  putStrLn "could not parse flint phrases:\n" >> putStrLn err1
                                       putStrLn "could not parse flint spec:\n" >> putStrLn err2
                      Right (s, r, i, _) -> init_server opts' port_nr s r i
                    Right ps -> init_with_phrases opts' port_nr ps
    (p:opts)   | Just port_nr <- readMaybe p -> do
      opts <- run_options (["-i",cdir] ++ opts)
      init_with_phrases opts port_nr []
    _ -> putStrLn "please provide: <NAME>.eflint <PORT> <OPTIONS>"

init_with_phrases :: Options -> PortNumber -> [Either Directive Phrase] -> IO ()
init_with_phrases opts port_nr ps = do
  let explorer = init_explorer Nothing 
  run_directives_phrases opts ps (start_server opts port_nr) explorer
  return ()

type Cont a = Explorer -> IO a

run_directives_phrases :: Options -> [Either Directive Phrase] -> Cont a -> Cont a
run_directives_phrases opts [] cont exp = cont exp
run_directives_phrases opts (edp:ps) cont exp = let (_,_,(_,ctx)) = get_last_edge exp (EI.currRef exp) in
  case edp of
   Left d  -> run_directive opts d (run_directives_phrases opts ps cont) exp
   Right p -> run_phrase opts p (run_directives_phrases opts ps cont) exp

run_phrase :: Options -> Phrase -> Cont a -> Cont a
run_phrase opts phrase cont exp = case run_ exp (Execute (convert_programs [phrase]) emptyInput) of
  ResultTrans exp _ _ _  -> cont exp
  Path _                 -> putStrLn "Unexpected execution path encountered" >> cont exp 
  Nodes _                -> putStrLn "Unexpected collection of nodes encountered" >> cont exp 
  InvalidRevert          -> putStrLn "invalid revert error" >> cont exp
  ExportExploration _    -> putStrLn "Unexpected export problem of execution graph" >> cont exp
  LoadExploration _      -> putStrLn "Unexpected load problem of execution graph" >> cont exp

run_directive :: Options -> Directive -> Cont a -> Cont a
run_directive opts (Require fp) cont exp
  | has_been_included fp opts = cont exp
  | otherwise                 = run_directive opts (Include fp) cont exp
run_directive opts (Include fp) cont exp = do
  let dirs = find include_paths opts
  find_included_file dirs fp >>= \case
    []       -> putStrLn ("could not find " ++ fp ++ " in " ++ show dirs) >> cont exp
    (file:_) -> do
      add_include_path (takeDirectory file) opts
      add_include file opts
      case ".json" `isSuffixOf` file of
        True -> do
          mspec <- decode_json_file file
          case mspec of
            Left err -> putStrLn err >> cont exp
            Right spec -> putStrLn "including .json files is no longer supported" >> cont exp --repl_directive_phrases opts [Right (PFrames spec)] explorer
        False -> catchIOError (Right <$> readFile file) handler >>= \case
          Left err  -> putStrLn err >> cont exp
          Right str -> case parse_component syn_directives_phrases str of
            Left err -> putStrLn err >> cont exp
            Right eps -> run_directives_phrases opts eps cont exp
 where handler :: IOError -> IO (Either String a)
       handler exc | isDoesNotExistError exc = return (Left ("unknown file: " ++ fp))
                   | isPermissionError exc = return (Left ("cannot read: " ++ fp))
                   | isAlreadyInUseError exc = return (Left ("in use: " ++ fp))
                   | otherwise               = return (Left (show exc))



init_server :: Options -> PortNumber -> Spec -> Refiner -> Initialiser -> IO ()
init_server opts port_nr spec' ref' init' = do
  case compile_all spec' ref' init' [] of
    Left errs -> putStrLn "cannot compile specification" >> putStrLn (unlines errs)
    Right (spec', ref, init, _) -> do
      let spec = refine_specification spec' ref
      let state = make_initial_state spec init
      let explorer = init_explorer (Just (spec, state))
      start_server opts port_nr explorer

start_server :: Options -> PortNumber -> Cont ()
start_server opts port_nr explorer = do
      sock <- socket AF_INET Stream 0
      setSocketOption sock ReuseAddr 1
      Network.Socket.bind sock (SockAddrInet port_nr (tupleToHostAddress (127,0,0,1)))
      listen sock 2
      server opts sock  explorer

server :: Options -> Socket -> Cont ()
server opts = continue
  where continue :: Socket -> Cont ()
        continue sock exp = do
          putStrLn "--- AWAITING STATEMENT ---"
          conn <- accept sock
          handle <- socketToHandle (fst conn) ReadWriteMode
          string <- hGetLine handle
          let (_, _, (sid, ctx)) = get_last_edge exp (EI.currRef exp)
          putStrLn string
          let compile_and inpm program = report $ run_ exp (Execute [program] inpm)
              report res = case res of
                ResultTrans exp outs (old,oid) (new,sid) -> report_success sock outs oid old sid new exp
                Path path                        -> do
                  hPutStrLn handle (json_encode (GivePath path))
                  hClose handle
                  continue sock exp
--                Explorer.ExecError err    -> report_error (ExecError err) exp
                Nodes nodes -> do
                  hPutStrLn handle (json_encode (GiveNodes nodes))
                  hClose handle
                  continue sock exp
                ExportExploration exportGraph -> do
                  putStrLn "--- Exporting ---"
                  hPutStrLn handle (json_encode (GiveExportGraph exportGraph))
                  hClose handle
                  continue sock exp
                LoadExploration exp -> do
                  putStrLn "--- Loading execution graph ---"
                  hPutStrLn handle (json_encode (GiveLoadGraph))
                  hClose handle 
                  continue sock exp
                InvalidRevert             -> report_error InvalidState exp
--                CompilationError err      -> report_error (InvalidInput err) exp
              report_success sock outputs old_id c0 state_id ctx exp = do
                let facts_from = state_holds (cfg_state c0)
                let facts_to = state_holds (cfg_state ctx)
                let created_facts    = facts_to \\ facts_from
                let terminated_facts = facts_from \\ facts_to

                let viols = S.fromList (violations outputs)
                let outs = S.fromList (ex_triggers outputs)
                let errs = S.fromList (errors outputs)
                let qress = query_ress outputs

                let transitions = S.fromList (rest_transitions ctx)
                let new_duties = S.fromList (rest_duties ctx) S.\\ S.fromList (rest_duties c0)
                let new_enabled = S.fromList (rest_enabled ctx) S.\\ S.fromList (rest_enabled c0)
                let new_disabled = S.fromList (rest_disabled ctx) S.\\ S.fromList (rest_disabled c0)
                let all_duties = S.fromList $ rest_duties ctx

                let response = case missing_inputs outputs of
                      [] -> CommandSuccess old_id state_id
                                            facts_from facts_to created_facts terminated_facts
                                            viols outs errs qress
                                            new_duties all_duties
                                            new_enabled new_disabled transitions
                      ms -> InputRequired ms 
                hPutStrLn handle (json_encode response)
                hClose handle
                continue sock exp
              report_error err exp = do
                hPutStrLn handle (json_encode err)
                hClose handle
                continue sock exp
          let withCommand cmd = case cmd of 
                CreateEvent term inpm -> compile_and inpm $ Program (Create [] term) 
                TerminateEvent term inpm -> compile_and inpm $ Program (Terminate [] term) 
                QueryCommand term inpm  -> compile_and inpm $ Program (PQuery term)
                Revert new_state    -> report $ run_ exp (Explorer.Revert new_state)
                Status mid          -> report $ run_ exp (Display (maybe (EI.currRef exp) id mid))
                History mid         -> report $ run_ exp (DisplayFull (maybe (EI.currRef exp) id mid))
                Heads               -> report $ run_ exp ExplorationHeads
                CreateExport        -> report $ run_ exp CreateExportExploration
                LoadExport graph    -> report $ run_ exp (LoadExportExploration graph)
                GetFacts inpm       -> do hPutStrLn handle (json_encode (GiveFacts (state_input_holds (cfg_state ctx) inpm)))
                                          hClose handle
                                          continue sock exp
                Kill                -> hPutStrLn handle (json_encode ByeBye) >> hClose handle 
                ActionCommand d a r os force inpm -> compile_and inpm $ Program (PTrigger [] term)
                  where term = App d (Left (a : r : os))
                CmdTrigger t b inpm -> compile_and inpm (Program (PTrigger [] t)) 
                Phrase str inpm -> case parse_component syn_phrases str of
                  Left err  -> do hPutStrLn handle (json_encode (InvalidInput err))
                                  hClose handle >> continue sock exp
                  Right ps  -> report $ run_ exp (Execute (convert_programs ps) inpm)
                Phrases str inpm -> case parse_component syn_phrases str of
                  Left err  -> do hPutStrLn handle (json_encode (InvalidInput err))
                                  hClose handle >> continue sock exp
                  Right ps  -> report $ run_ exp (ExecuteOnce (collapse_programs (convert_programs ps)) inpm) 
          case eitherDecode (Data.ByteString.Lazy.Char8.pack string) of 
            Left err -> do when (find debug opts) (putStrLn err)
                           case (find accept_phrases opts) of
                            False -> do hPutStrLn handle (json_encode (InvalidCommand err))
                                        hClose handle
                                        continue sock exp
                            True  -> withCommand (Phrase string emptyInput)
            Right cmd-> withCommand cmd

json_encode r = Data.ByteString.Lazy.Char8.unpack (encode r)



data Command    = ActionCommand DomId Term Term [Term] Bool InputMap
                | CmdTrigger Term Bool InputMap
                | CreateEvent Term InputMap
                | TerminateEvent Term InputMap
                | QueryCommand Term InputMap
                | Revert Int
                | Status (Maybe Int)
                | Kill
                | GetFacts InputMap
                | History (Maybe Int)
                | Heads
                | CreateExport
                | LoadExport ExecutionGraph
                | Phrase String InputMap
                | Phrases String InputMap

instance FromJSON Command where
  parseJSON = withObject "Command" $ \v -> do
                cmd <- v .: "command"
                case cmd::String of
                  "create"      -> CreateEvent . value_to_term <$> v .: "value" <*> maybe_input v
                  "terminate"   -> TerminateEvent . value_to_term <$> v .: "value" <*> maybe_input v
                  "test-present"-> QueryCommand . value_to_term <$> v .: "value" <*> maybe_input v

                  "test-absent" -> QueryCommand . Not . value_to_term  <$> v .: "value" <*> maybe_input v

                  "enabled"     -> QueryCommand . Enabled . value_to_term <$> v .: "value" <*> maybe_input v
                  "revert"      -> Revert <$> v .: "value"
                  "action"      -> full_action <|> trigger_action
                    where full_action =
                            actionCommand <$>
                                    v .: "act-type" <*> v .: "actor" <*> v .: "recipient"
                               <*>  v .: "objects"  <*> maybe_force v <*> maybe_input v
                          trigger_action = CmdTrigger . value_to_term <$> v .: "value" <*> maybe_force v <*> maybe_input v
                          actionCommand d a r os = ActionCommand d (to_term a) (to_term r) (map to_term os)
                  "status"      -> Status <$> v .: "state"
                                <|> return (Status Nothing)
                  "history"     ->  History <$> v .: "state"
                                <|> return (History Nothing)
                  "trace-heads" -> return Heads
                  "create-export" -> return CreateExport
                  "load-export" -> LoadExport <$> v .: "graph"
                  "kill"        -> return Kill
                  "phrase"      -> Phrase <$> v .: "text" <*> maybe_input v
                  "phrases"     -> Phrases <$> v .: "text" <*> maybe_input v
                  "event"       -> CmdTrigger . value_to_term <$> v .: "value" <*> maybe_force v  <*> maybe_input v
                  "facts"       -> GetFacts <$> maybe_input v  
                  _             -> mzero

maybe_force v = v .: "force" <|> return False
maybe_input v = value_based_input <$> v .: "input" <|> return emptyInput

value_based_input :: [AssTuple] -> InputMap
value_based_input = M.fromList . map toTup
  where toTup at = (value_to_tagged $ (value :: AssTuple -> Value) at, assignment at)

encode_store :: Store -> [AssTuple]
encode_store = concatMap toTup . M.assocs
  where toTup (te, HoldsTrue)   = return $ AssTuple (tagged_to_value te) True
        toTup (te, HoldsFalse)  = return $ AssTuple (tagged_to_value te) False
        toTup (te, Unknown)     = [] 

data AssTuple = AssTuple { value :: Value
                         , assignment  :: Bool } deriving (Generic)
instance FromJSON AssTuple where
instance ToJSON AssTuple

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

value_to_tagged :: Value -> Tagged
value_to_tagged (Atom d (Left str)) = (String str, d)
value_to_tagged (Atom d (Right i))  = (Int i, d)
value_to_tagged (Composite d vs)    = (Product (map value_to_tagged vs), d)

tagged_to_value :: Tagged -> Value
tagged_to_value (String s, d) = Atom d (Left s)
tagged_to_value (Int i, d) = Atom d (Right i)
tagged_to_value (Product args, d) = Composite d (map tagged_to_value args)

instance FromJSON Value where
  parseJSON = withObject "Value" $ \v ->
                    (\c i -> Atom c (Right i)) <$> v .: "fact-type" <*> v .: "value"
                <|> (\c s -> Atom c (Left s))  <$> v .: "fact-type" <*> v .: "value"
                <|> Composite <$> v .: "fact-type" <*> v .: "value"
                <|> Composite <$> v .: "fact-type" <*> v .: "arguments"

instance ToJSON Value where
  toJSON v = case v of 
    Atom d (Left str) -> object [ "fact-type" .= d, "value" .= toJSON str ]
    Atom d (Right i)  -> object [ "fact-type" .= d, "value" .= toJSON i ]
    Composite d [v]   -> object [ "fact-type" .= d, "value" .= toJSON v ]
    Composite d vs    -> object [ "fact-type" .= d, "arguments" .= toJSON vs ]

data Response   = InvalidCommand String
                | InvalidInput String -- parse error
                | CommandSuccess Int -- Source node ID
                                 Int -- Target node ID
                                 [Tagged] -- source node facts
                                 [Tagged] -- target node facts
                                 [Tagged] -- created facts
                                 [Tagged] -- deleted facts
                                 (S.Set Violation)
                                 (S.Set TransInfo)
                                 (S.Set Error) -- errors: compilation + transition
                                 [QueryRes]         -- query results
                                 (S.Set Tagged) -- new duties
                                 (S.Set Tagged) -- all duties in the current state
                                 (S.Set Tagged) -- newly enabled transitions
                                 (S.Set Tagged) -- newly disabled transitions
                                 (S.Set Transition) -- all transitions
                | InvalidState
                | InputRequired [Tagged]
                | GiveFacts [Tagged]
                | GivePath Path
                | GiveNodes [Node]
                | GiveExportGraph ExecutionGraph
                | GiveLoadGraph
                | ByeBye

instance ToJSON Response where
  toJSON (InputRequired tes) = object [ "response" .= JSON.String "input required", "values" .= toJSON (map tagged_to_value tes)]
  toJSON (InvalidCommand err) = object [ "response" .= JSON.String "invalid command", "message" .= toJSON err ]
  toJSON (CommandSuccess sid_from i
                         facts_from facts_to created_facts terminated_facts
                         vs outs errs qress
                         new_duties all_duties
                         new_enabled new_disabled all_transitions) =
    object [ "response"   .= JSON.String "success"
           , "old-state" .= toJSON sid_from
           , "new-state"  .= toJSON i
           , "source_contents"  .= toJSON (map TaggedJSON facts_from)
           , "target_contents"  .= toJSON (map TaggedJSON facts_to)
           , "created_facts"    .= toJSON (map TaggedJSON created_facts)
           , "terminated_facts" .= toJSON (map TaggedJSON terminated_facts)

           , "violations" .= toJSON vs
           , "output-events" .= toJSON outs
           , "errors"     .= toJSON errs
           , "query-results" .= toJSON qress

           , "new-duties" .= toJSON (map TaggedJSON $ S.toList new_duties)
           , "new-enabled-transitions" .= toJSON (map TaggedJSON $ S.toList new_enabled)
           , "new-disabled-transitions" .= toJSON (map TaggedJSON $ S.toList new_disabled)
           , "all-duties" .= toJSON (map TaggedJSON $ S.toList all_duties)
           , "all-disabled-transitions" .= toJSON (map TaggedJSON dis_transitions)
           , "all-enabled-transitions" .= toJSON (map TaggedJSON en_transitions)
           ]
   where en_transitions = map fst $ filter snd $ map get_transition (S.toList all_transitions)
         dis_transitions = map fst $ filter (not . snd) $ map get_transition (S.toList all_transitions)
  toJSON InvalidState       = object [ "response" .= JSON.String "invalid state" ]
  toJSON (InvalidInput err) = object [ "response" .= JSON.String "invalid input"
                                     , "error"    .= toJSON err ]
  toJSON ByeBye             = object [ "response"  .= JSON.String "bye world.." ]
  toJSON (GiveFacts tes)    = object [ "values" .= toJSON (map TaggedJSON tes) ]
  toJSON (GiveNodes nodes)  = object [ "nodes"  .= toJSON (map toJSONNode nodes) ]
    where toJSONNode (sid, cfg) =
            object [ "state_id"             .= toJSON sid
                   , "state_contents"       .= toJSON (map TaggedJSON (state_contents))
                   , "duties"               .= toJSON (map TaggedJSON $ S.toList all_duties)
                   , "disabled-transitions" .= toJSON (map TaggedJSON dis_transitions)
                   , "enabled-transitions"  .= toJSON (map TaggedJSON en_transitions)
                   ]
             where state_contents = state_holds (cfg_state cfg)
                   all_duties = S.fromList $ rest_duties cfg
                   all_transitions = S.fromList (map get_transition (rest_transitions cfg))
                   en_transitions = map fst $ filter snd $ S.toList all_transitions
                   dis_transitions = map fst $ filter (not . snd) $ S.toList all_transitions

  toJSON (GivePath edges)   = object [ "edges"  .= toJSON (map toJSONEdge edges') ]
    where edges' = sortBy (on compare (\((sid,_),_,_) -> sid)) edges
          toJSONEdge ((sid_from,ctx_from), (phr, output), (sid_to, ctx_to)) =
            object [ "phrase"           .= toJSON (ppProgram (snd phr))
                   , "input"            .= toJSON (fst phr)
                   , "source_id"        .= toJSON sid_from
                   , "target_id"        .= toJSON sid_to

                   , "source_contents"  .= toJSON (map TaggedJSON facts_from)
                   , "target_contents"  .= toJSON (map TaggedJSON facts_to)
                   , "created_facts"    .= toJSON (map TaggedJSON created)
                   , "terminated_facts" .= toJSON (map TaggedJSON terminated)

                   , "violations"       .= toJSON rep_viols
                   , "output-events"    .= toJSON outs
                   , "errors"           .= toJSON errs
                   , "query-results"    .= toJSON qress

                   , "new-duties" .= toJSON (map TaggedJSON $ S.toList new_duties)
                   , "new-enabled-transitions" .= toJSON (map TaggedJSON $ S.toList new_enabled)
                   , "new-disabled-transitions" .= toJSON (map TaggedJSON $ S.toList new_disabled)
                   , "all-duties" .= toJSON (map TaggedJSON $ S.toList all_duties)
                   , "all-disabled-transitions" .= toJSON (map TaggedJSON dis_transitions)
                   , "all-enabled-transitions" .= toJSON (map TaggedJSON en_transitions)
                   ]
           where facts_from = state_holds (cfg_state ctx_from)
                 facts_to   = state_holds (cfg_state ctx_to)
                 created    = facts_to \\ facts_from
                 terminated = facts_from \\ facts_to

                 rep_viols  = violations output
                 outs = S.fromList (ex_triggers output)
                 errs = S.fromList (errors output)
                 qress = query_ress output

                 all_transitions = S.fromList (rest_transitions ctx_to)
                 en_transitions = map fst $ filter snd $ map get_transition (S.toList all_transitions)
                 dis_transitions = map fst $ filter (not . snd) $ map get_transition (S.toList all_transitions)
                 new_duties = S.fromList (rest_duties ctx_to) S.\\ S.fromList (rest_duties ctx_from)
                 new_enabled = S.fromList (rest_enabled ctx_to) S.\\ S.fromList (rest_enabled ctx_from)
                 new_disabled = S.fromList (rest_disabled ctx_to) S.\\ S.fromList (rest_disabled ctx_from)
                 all_duties = S.fromList $ rest_duties ctx_to

  toJSON (GiveExportGraph graph)  = toJSON graph
  toJSON GiveLoadGraph = object [ "response" .= JSON.String "success" ]

instance ToJSON Violation where
  toJSON (TriggerViolation info) =
    object [ "violation" .= JSON.String "trigger"
           , "info"     .= toJSON info 
           ]
  toJSON (DutyViolation te) =
    object [ "violation" .= toJSON ("duty"::String)
           , "value"     .= toJSON (TaggedJSON te) ]
  toJSON (InvariantViolation d) =
    object [ "violation" .= toJSON ("invariant"::String)
           , "invariant" .= toJSON d ]

instance FromJSON Violation where
  parseJSON = withObject "trigger or duty or invariant violation" $ \o -> do
    violationtype <- o .: "violation"
    case violationtype of
      "trigger"   -> TriggerViolation   <$> o .: "info"
      "duty"      -> DutyViolation      <$> o .: "value"
      "invariant" -> InvariantViolation <$> o .: "invariant"
      _           -> fail ("unknown type: " ++ violationtype)

instance ToJSON QueryRes where
  toJSON qres = case qres of
    QuerySuccess -> JSON.String "success"
    QueryFailure -> JSON.String "failure"

instance FromJSON QueryRes where
  parseJSON o = case o of
      "success" -> return QuerySuccess
      "failure" -> return QueryFailure
      res       -> fail ("unknown query-result " ++ show res)

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

instance FromJSON Error where
  parseJSON = withObject "NonDeterministicTransition or NotTriggerable or CompilationError" $ \o -> do
    errortype <- o .: "error-type"
    case errortype of
      "non-deterministic transition" -> return NonDeterministicTransition
      "not triggerable"              -> NotTriggerable <$> o .: "value"
      "compilation error"            -> CompilationError   <$> o .: "error"
      _                              -> fail ("unknown type: " ++ errortype)


instance ToJSON Output where
  toJSON (ExecutedTransition info) = object [ "output-type" .= JSON.String "executed-transition", "info" .= toJSON info]
  toJSON (Violation v)    = object [ "output-type" .= JSON.String "violation", "output" .= v]
  toJSON (QueryRes r)     = object [ "output-type" .= JSON.String "query-res", "output" .= r]
  toJSON (ErrorVal e)     = object [ "output-type" .= JSON.String "error-val", "output" .= e]

instance FromJSON Output where
  parseJSON = withObject "outputevent or violation or queryres or errorval" $ \o -> do
    outputtype <- o .: "output-type"
    case outputtype of
      "executed-transition" -> ExecutedTransition <$> o .: "info" 
      "violation"    -> Violation <$> o .: "output" 
      "query-res"    -> QueryRes <$> o .: "output" 
      "error-val"    -> ErrorVal <$> o .: "output" 
      _        -> fail ("unknown output: " ++ outputtype)

instance ToJSON Config where
  toJSON conf = object [
    "spec"             .= cfg_spec conf,
    "state"            .= cfg_state conf,
    "rest_transitions" .= rest_transitions conf,
    "rest_duties"      .= rest_duties conf
    ]

instance FromJSON Config where
  parseJSON = withObject "config" $ \o -> do
    cfg_spec         <- o .: "spec"
    cfg_state        <- o .: "state"
    rest_transitions <- o .: "rest_transitions"
    rest_duties      <- o .: "rest_duties"
    return Config{..}

instance ToJSON Elem where
  toJSON (String el)  = object ["elem-type" .= JSON.String "string",  "elem" .= el]
  toJSON (Int el)     = object ["elem-type" .= JSON.String "int",     "elem" .= el]
  toJSON (Product el) = object ["elem-type" .= JSON.String "product", "elem" .= el]

instance FromJSON Elem where
  parseJSON = withObject "string or int or product" $ \o -> do
    elemtype <- o .: "elem-type"
    case elemtype of
      "string"  -> String <$> o .: "elem"
      "int"     -> Int <$> o .: "elem"
      "product" -> Product <$> o .: "elem"
      _         -> fail ("unknown type: " ++ elemtype)

instance ToJSON Spec where
  toJSON spec = object [
    "decls"      .= decls spec,
    "aliases"    .= aliases spec
    ]

instance FromJSON Spec where
  parseJSON = withObject "spec" $ \o -> do
    decls      <- o .: "decls"
    aliases    <- o .: "aliases"
    return Spec{..}

-- TODO remove show and use ToJSON functions
instance ToJSON State where
  toJSON state = object [
    "contents" .=  show (contents state),
    "time"     .=  (time state)
    ]

-- TODO remove read and use FromJSON functions
instance FromJSON State where
  parseJSON = withObject "state" $ \o -> do
    contents_show <- o .: "contents"
    let contents = read contents_show
    time     <- o .: "time"
    return State{contents=contents, time=time}

instance ToJSON Info where
  toJSON info = object [
    "value" .= toJSON ((value :: Info -> Bool) info ),
    "from-sat" .= toJSON (from_sat info)
    ]

instance FromJSON Info where
  parseJSON = withObject "info" $ \o -> do
    value <- o .: "value"
    from_sat <- o .: "from-sat"
    return Info{..}

instance ToJSON TypeSpec where
  toJSON typespec = object [
    "kind"              .= kind typespec,
    "domain"            .= domain typespec,
    "domain_constraint" .= domain_constraint typespec,
    "derivation"        .= derivation typespec,
    "closed"            .= closed typespec,
    "conditions"        .= conditions typespec
    ]

instance FromJSON TypeSpec where
  parseJSON = withObject "typespec" $ \o -> do
    kind              <- o .: "kind"
    domain            <- o .: "domain"
    domain_constraint <- o .: "domain_constraint"
    derivation        <- o .: "derivation"
    closed            <- o .: "closed"
    conditions        <- o .: "conditions"
    return TypeSpec{..}

instance ToJSON Kind where
  toJSON (Fact kind)  = object ["kind-type" .= JSON.String "Fact",
                                "fact" .= kind]
  toJSON (Act kind)   = object ["kind-type" .= JSON.String "Act",
                                "act" .= kind]
  toJSON (Duty kind)  = object ["kind-type" .= JSON.String "Duty",
                                "duty" .= kind]
  toJSON (Event kind) = object ["kind-type" .= JSON.String "Event",
                                  "event" .= kind]

instance FromJSON Kind where
  parseJSON = withObject "fact or act or duty or event" $ \o -> do
    kindtype <- o .: "kind-type"
    case kindtype of
      "Fact"  -> Fact <$> o .: "fact"
      "Act"   -> Act <$> o .: "act"
      "Duty"  -> Duty <$> o .: "duty"
      "Event" -> Event <$> o .: "event"
      _       -> fail ("unknown type: " ++ kindtype)

instance ToJSON FactSpec where
  toJSON factspec = object [
    "invariant" .= invariant factspec,
    "actor"     .= actor factspec
    ]

instance FromJSON FactSpec where
  parseJSON = withObject "factsspec" $ \o -> do
    invariant <- o .: "invariant"
    actor  <- o .: "actor"
    return FactSpec{..}

instance ToJSON ActSpec where
  toJSON actspec = object [
    "effects"    .= effects actspec,
    "syncs"      .= syncs actspec
    ]

instance FromJSON ActSpec where
  parseJSON = withObject "actspec" $ \o -> do
    effects  <- o .: "effects"
    syncs  <- o .: "syncs"
    return ActSpec{..}

instance ToJSON Term where
  toJSON (Not t)          = object ["term-type" .= JSON.String "Not",
                                    "t" .= t]
  toJSON (And t1 t2)      = object ["term-type" .= JSON.String "And",
                                    "t1" .= t1, "t2" .= t2]
  toJSON (Or t1 t2)       = object ["term-type" .= JSON.String "Or",
                                    "t1" .= t1, "t2" .= t2]
  toJSON (BoolLit b)      = object ["term-type" .= JSON.String "BoolLit",
                                    "b" .= b]

  toJSON (Leq t1 t2)      = object ["term-type" .= JSON.String "Leq",
                                    "t1" .= t1, "t2" .= t2]
  toJSON (Geq t1 t2)      = object ["term-type" .= JSON.String "Geq",
                                    "t1" .= t1, "t2" .= t2]
  toJSON (Ge t1 t2)       = object ["term-type" .= JSON.String "Ge",
                                    "t1" .= t1, "t2" .= t2]
  toJSON (Le t1 t2)       = object ["term-type" .= JSON.String "Le",
                                    "t1" .= t1, "t2" .= t2]

  toJSON (Sub t1 t2)      = object ["term-type" .= JSON.String "Sub",
                                    "t1" .= t1, "t2" .= t2]
  toJSON (Add t1 t2)      = object ["term-type" .= JSON.String "Add",
                                    "t1" .= t1, "t2" .= t2]
  toJSON (Mult t1 t2)     = object ["term-type" .= JSON.String "Mult",
                                    "t1" .= t1, "t2" .= t2]
  toJSON (Mod t1 t2)      = object ["term-type" .= JSON.String "Mod",
                                    "t1" .= t1, "t2" .= t2]
  toJSON (Div t1 t2)      = object ["term-type" .= JSON.String "Div",
                                    "t1" .= t1, "t2" .= t2]

  toJSON (IntLit i)       = object ["term-type" .= JSON.String "IntLit",
                                    "int" .= i]
  toJSON (StringLit s)    = object ["term-type" .= JSON.String "StringLit",
                                    "string" .= s]

  toJSON (Eq t1 t2)       = object ["term-type" .= JSON.String "Eq",
                                    "t1" .= t1, "t2" .= t2]
  toJSON (Neq t1 t2)      = object ["term-type" .= JSON.String "Neq",
                                    "t1" .= t1, "t2" .= t2]

  toJSON (Exists vars t)  = object ["term-type" .= JSON.String "Exists",
                                    "vars" .= vars,
                                    "t" .= t]
  toJSON (Forall vars t)  = object ["term-type" .= JSON.String "Forall",
                                    "vars" .= vars,
                                    "t" .= t]
  toJSON (Count vars t)   = object ["term-type" .= JSON.String "Count",
                                    "vars" .= vars,
                                    "t" .= t]
  toJSON (Sum vars t)     = object ["term-type" .= JSON.String "Sum",
                                    "vars" .= vars,
                                    "t" .= t]
  toJSON (Max vars t)     = object ["term-type" .= JSON.String "Max",
                                    "vars" .= vars,
                                    "t" .= t]
  toJSON (Min vars t)     = object ["term-type" .= JSON.String "Min",
                                    "vars" .= vars,
                                    "t" .= t]
  toJSON (When t1 t2)     = object ["term-type" .= JSON.String "When",
                                    "t1" .= t1, "t2" .= t2]
  toJSON (Present t)      = object ["term-type" .= JSON.String "Present",
                                    "t" .= t]
  toJSON (Violated t)     = object ["term-type" .= JSON.String "Violated",
                                    "t" .= t]
  toJSON (Enabled t)      = object ["term-type" .= JSON.String "Enabled",
                                    "t" .= t]
  toJSON (Project t var)  = object ["term-type" .= JSON.String "Project",
                                    "t" .= t, "var" .= var]

  toJSON (Tag t domid)    = object ["term-type" .= JSON.String "Tag",
                                    "t" .= t, "domID" .= domid]
  toJSON (Untag t)        = object ["term-type" .= JSON.String "Untag",
                                    "t" .= t]
  toJSON (Ref var)        = object ["term-type" .= JSON.String "Ref",
                                    "var" .= var]
  toJSON (App domid args) = object ["term-type" .= JSON.String "App",
                                    "domID" .= domid, "args"  .= args]
  toJSON (CurrentTime)    = object ["term-type" .= JSON.String "CurrentTime"]

instance FromJSON Term where
  parseJSON = withObject "terms" $ \o -> do
    termtype <- o .: "term-type"
    case termtype of
      "Not"           -> Not <$> o .: "t"
      "And"           -> And <$> o .: "t1" <*> o .: "t2"
      "Or"            -> Or <$> o .: "t1" <*> o .: "t2"
      "BoolLit"       -> BoolLit <$> o .: "b"

      "Leq"           -> Leq <$> o .: "t1" <*> o .: "t2"
      "Geq"           -> Geq <$> o .: "t1" <*> o .: "t2"
      "Ge"            -> Ge <$> o .: "t1" <*> o .: "t2"
      "Le"            -> Le <$> o .: "t1" <*> o .: "t2"

      "Sub"           -> Sub <$> o .: "t1" <*> o .: "t2"
      "Add"           -> Add <$> o .: "t1" <*> o .: "t2"
      "Mult"          -> Mult <$> o .: "t1" <*> o .: "t2"
      "Mod"           -> Mod <$> o .: "t1" <*> o .: "t2"
      "Div"           -> Div <$> o .: "t1" <*> o .: "t2"

      "IntLit"        -> IntLit <$> o .: "int"
      "StringLit"     -> StringLit <$> o .: "string"

      "Eq"            -> Eq <$> o .: "t1" <*> o .: "t2"
      "Neq"           -> Neq <$> o .: "t1" <*> o .: "t2"

      "Exists"        -> Exists <$> o .: "vars" <*> o .: "t"
      "Forall"        -> Forall <$> o .: "vars" <*> o .: "t"
      "Count"         -> Count <$> o .: "vars" <*> o .: "t"
      "Sum"           -> Sum <$> o .: "vars" <*> o .: "t"
      "Max"           -> Max <$> o .: "vars" <*> o .: "t"
      "Min"           -> Min <$> o .: "vars" <*> o .: "t"

      "When"          -> When <$> o .: "t1" <*> o .: "t2"
      "Present"       -> Present <$> o .: "t"
      "Violated"      -> Violated <$> o .: "t"
      "Enabled"       -> Enabled <$> o .: "t"
      "Project"       -> Project <$> o .: "t" <*> o .: "var"

      "Tag"           -> Tag <$> o .: "t" <*> o .: "domID"
      "Untag"         -> Untag <$> o .: "t"
      "Ref"           -> Ref <$> o .: "var"
      "App"           -> App <$> o .: "domID" <*> o .: "args"
      "CurrentTime"   -> return CurrentTime{}

      _       -> fail ("unknown type: " ++ termtype)

instance ToJSON Modifier where
  toJSON (Rename var term) = object [
    "var"  .= var,
    "term" .= term
    ]

instance FromJSON Modifier where
  parseJSON = withObject "modifier" $ \o -> do
    var <- o.: "var"
    term <- o.: "term"
    return (Rename var term)


instance ToJSON Effect where
  toJSON (CAll vars t)  = object ["effect-type" .= JSON.String "CAll",
                                     "vars" .= vars,
                                     "term" .= t]
  toJSON (TAll vars t)  = object ["effect-type" .= JSON.String "TAll",
                                     "vars" .= vars,
                                     "term" .= t]
  toJSON (OAll vars t)  = object ["effect-type" .= JSON.String "OAll",
                                     "vars" .= vars,
                                     "term" .= t]

instance FromJSON Effect where
  parseJSON = withObject "CAll or Tall" $ \o -> do
    effecttype <- o .: "effect-type"
    case effecttype of
      "TAll"  -> TAll <$> o .: "vars" <*> o .: "term"
      "CAll"  -> CAll <$> o .: "vars" <*> o .: "term"
      _       -> fail ("unknown type: " ++ effecttype)

instance ToJSON Sync where
  toJSON (Sync vars term) = object [
    "vars"  .= vars,
    "term" .= term
    ]

instance FromJSON Sync where
  parseJSON = withObject "sync" $ \o -> do
    vars <- o.: "vars"
    term <- o.: "term"
    return (Sync vars term)

instance ToJSON Var where
  toJSON (Var domid string) = object [
    "domID"  .= domid,
    "string" .= string
    ]

instance FromJSON Var where
  parseJSON = withObject "var" $ \o -> do
    domid <- o.: "domID"
    string <- o.: "string"
    return (Var domid string)

instance ToJSON DutySpec where
  toJSON dutyspec = object [
    "enforcing_acts" .= enforcing_acts dutyspec,
    "violated_when"  .= violated_when dutyspec
    ]

instance FromJSON DutySpec where
  parseJSON = withObject "dutyspec" $ \o -> do
    enforcing_acts <- o.: "enforcing_acts"
    violated_when <- o.: "violated_when"
    return DutySpec{..}

instance ToJSON EventSpec where
  toJSON eventspec = object [
    "event_effects" .= event_effects eventspec
    ]

instance FromJSON EventSpec where
  parseJSON = withObject "eventspec" $ \o -> do
    event_effects <- o.: "event_effects"
    return EventSpec{..}

instance ToJSON Domain where
  toJSON (AnyString)       = object ["domain-type" .= JSON.String "AnyString"]
  toJSON (AnyInt)          = object ["domain-type" .= JSON.String "AnyInt"]
  toJSON (Strings strings) = object ["domain-type" .= JSON.String "Strings", "strings" .= strings]
  toJSON (Ints ints)       = object ["domain-type" .= JSON.String "Ints", "ints" .= ints]
  toJSON (Products vars)   = object ["domain-type" .= JSON.String "Products", "vars" .= vars]
  toJSON (Time)            = object ["domain-type" .= JSON.String "Time"]

instance FromJSON Domain where
  parseJSON = withObject "anystring or anyint or strings or ints or products or time or external" $ \o -> do
    domaintype <- o .: "domain-type"
    case domaintype of
      "AnyString" -> return AnyString{}
      "AnyInt"    -> return AnyInt{}
      "Strings"   -> Strings <$> o .: "strings"
      "Ints"      -> Ints <$> o .: "ints"
      "Products"  -> Products <$> o .: "vars"
      "Time"      -> return Time{}
      _           -> fail ("unknown type: " ++ domaintype)

instance ToJSON Derivation where
  toJSON (Dv vars term)   = object ["derivation-type" .= JSON.String "Dv",
                                    "vars" .= vars, "term" .= term]
  toJSON (HoldsWhen term) = object ["derivation-type" .= JSON.String "HoldsWhen",
                                    "term" .= term]

instance FromJSON Derivation where
  parseJSON = withObject "dv or holdswhen or externalvalue" $ \o -> do
    derivationtype <- o .: "derivation-type"
    case derivationtype of
      "Dv"            -> Dv <$> o .: "vars" <*> o .: "term"
      "HoldsWhen"     -> HoldsWhen <$> o .: "term"
      _       -> fail ("unknown type: " ++ derivationtype)

instance ToJSON TransInfo where
  toJSON info = object [  
      "trans-tagged"      .= toJSON (tagged_to_value (trans_tagged info))
    , "trans-assignments" .= toJSON (encode_store (trans_assignments info))
    , "trans-forced"      .= toJSON (trans_forced info)
    , "trans-actor"       .= toJSON (trans_actor info)
    , "trans-is-action"   .= toJSON (trans_is_action info)
    , "trans-syncs"       .= toJSON (trans_syncs info)
    ]

instance ToJSON Assignment where
  toJSON HoldsTrue = JSON.String "true"
  toJSON HoldsFalse = JSON.String "false"
  toJSON Unknown = JSON.String "unknown"

instance FromJSON Assignment where
  parseJSON o = case o of 
    "true" -> return HoldsTrue 
    "false" -> return HoldsFalse 
    "unknown" -> return Unknown
    s -> fail ("unknown assignment " ++ show s)

instance FromJSON TransInfo where
  parseJSON = withObject "TransInfo" $ \o -> do
    TransInfo <$> o .: "trans-tagged" 
              <*> o .: "trans-assignments"
              <*> o .: "trans-forced"
              <*> o .: "trans-actor"
              <*> o .: "trans-syncs"  

-- TODO remove show and use ToJSON functions
instance ToJSON Transition where
  toJSON transition = object [
    "tagged"  .= show (tagged transition),
    "present" .= exist transition
    ]

-- TODO remove read and use FromJSON functions
instance FromJSON Transition where
  parseJSON = withObject "transition" $ \o -> do
    tagged_show <- o .: "tagged"
    let tagged = read tagged_show
    exist  <- o .: "present"
    return Transition{tagged=tagged, exist=exist}

-- Converting to/from graph
instance ToJSON ExecutionGraph where
  toJSON graph = object [
    "current" .= current graph,
    "nodes"   .=  nodes graph,
    "edges"   .=  edges graph
    ]

instance FromJSON ExecutionGraph where
  parseJSON = withObject "execution graph" $ \o -> do
    current <- o .: "current"
    nodes   <- o .: "nodes"
    edges   <- o .: "edges"
    return ExecutionGraph{..}

instance ToJSON N where
  toJSON node = object [
    "ref"    .= ref node,
    "config" .= config node
    ]

instance FromJSON N where
  parseJSON = withObject "node" $ \o -> do
    ref    <- o .: "ref"
    config <- o .: "config"
    return N{..}

instance ToJSON Edge where
  toJSON edge = object [
    "source" .= source edge,
    "target" .= target edge,
    "po"     .= po edge
    ]

instance FromJSON Edge where
  parseJSON = withObject "edge" $ \o -> do
    source <- o .: "source"
    target <- o .: "target"
    po     <- o .: "po"
    return Edge{..}

-- TODO remove show and use ToJSON functions
instance ToJSON PO where
  toJSON po = object [
    "program" .= ppProgram (snd $ label po),
    "input"   .= show (fst $ label po),
    "output"  .= show (output po)
    ]

-- TODO remove read and use FromJSON functions
instance FromJSON PO where
  parseJSON = withObject "label output" $ \o -> do
    program_show <- o .: "label"
    output_show  <- o .: "output"
    input_show   <- o .: "input"
    let output =  read output_show
    let input = read input_show
    case parse_component syn_phrases program_show of
      Left err  -> error(err)
      Right ps  -> return PO{label=(input, collapse_programs (convert_programs ps)),..}
