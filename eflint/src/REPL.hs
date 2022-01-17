{-# LANGUAGE LambdaCase #-}

module Main where

import Spec
import NewExplorer
import qualified Language.Explorer.Pure as EI 
import Interpreter
import Parse
import Print (ppDeclSpec)
import State
import StaticEval
import Options
import Util
import JSON(decode_json_file)

import Control.Monad (forM_, foldM, when, unless)
import Control.Monad.Trans.Class (lift)
import Data.Char (isSpace)
import Data.List (isPrefixOf, isSuffixOf, (\\))
import qualified Data.Map as M
import qualified Data.Set as S

import Text.Read (readMaybe)

import System.IO.Error
import System.Environment 
import System.Directory
import System.FilePath
import System.Console.Haskeline hiding (display)

-- the kind of explorer to use
init_explorer = init_tree_explorer

main = getArgs >>= arg_select 

arg_select :: [String] -> IO ()
arg_select args = do
  cdir <- getCurrentDirectory 
  let (files, flags') = span (not . (\a -> isPrefixOf "--" a || isPrefixOf "-" a)) args
  opts <- run_options (["-i",cdir] ++ flags')
  case files of
       [] -> repl_without opts
       [f] | ".eflint" `isSuffixOf` f -> repl_with opts f
       [f] | ".json" `isSuffixOf` f -> repl_with opts f
       _ -> putStrLn "Please provide: <NAME>.eflint <OPTIONS>"

repl_without :: Options -> IO ()
repl_without opts = compile_and_init opts emptySpec M.empty [] []

repl_with :: Options -> FilePath -> IO ()
repl_with opts fsrc = do  
  add_filepath fsrc opts 
  input_exists <- doesFileExist (fsrc ++ ".input")
  when input_exists $
    readFile (fsrc ++ ".input") >>= flip add_input opts . lines
  add_include_path (takeDirectory fsrc) opts
  add_include fsrc opts
  case ".json" `isSuffixOf` fsrc of
    True -> decode_json_file fsrc >>= \case
      Left err -> putStrLn "could not parse JSON file:\n" >> putStrLn err
      Right spec -> compile_and_init opts spec M.empty [] []
    False ->  do
      fl <- readFile fsrc
      case parse_component syn_directives_phrases fl of
        Left err1 -> case parse_flint fl of 
          Left err2        -> do  putStrLn "could not parse flint phrases:\n" >> putStrLn err1
                                  putStrLn "could not parse flint spec:\n" >> putStrLn err2
          Right (f,r,i,s) -> case find ignore_scenario opts of
            True  -> compile_and_init opts f r i []
            False -> compile_and_init opts f r i s
        Right ps  -> init_with_phrases opts ps

compile_and_init :: Options -> Spec -> Refiner -> Initialiser -> Scenario -> IO ()
compile_and_init opts f r i s = case compile_all f r i s of
    Right (spec',r',i',s') -> do
      test <- is_in_test_mode opts
      unless test $ do 
        let spec = refine_specification spec' r'
        let state = make_initial_state spec i'
        let explorer = init_explorer (Just (spec,state))
        let ((_,c0),_,(sid, ctx)) = get_last_edge explorer (EI.currRef explorer)
        verbosity opts 1 $ display_commands
        verbosity opts 2 $ display_info opts [] c0 ctx
        runInputT defaultSettings (repl opts explorer)
    Left errs   -> putStrLn "compilation errors:" >> putStrLn (unlines errs) 

init_with_phrases :: Options -> [Either Directive Phrase] -> IO ()
init_with_phrases opts ps = do 
  let explorer = init_explorer Nothing
  test <- is_in_test_mode opts
  runInputT defaultSettings $ do 
      exp <- repl_directive_phrases opts ps explorer
      unless test (repl opts exp)

repl :: Options -> Explorer -> InputT IO ()
repl opts exp = do
  let (_, _, (sid, ctx)) = get_last_edge exp (EI.currRef exp)
  maybeLine <- getInputLine ("#" ++ show sid ++ " > ")
  case maybeLine of
   Nothing -> return ()
   Just input -> do
    case span (not . isSpace) input of 
      (":choose", mint) -> repl_trigger ctx mint 
      (":revert", mint) | Just sid' <- readMaybe (dropWhile isSpace mint)
                        -> case run_ exp (Revert sid') of
                            InvalidRevert -> outputStrLn ("state id " ++ show sid' ++ " unknown") >> continue exp
                            ResultTrans exp outs (old,_) (new,sid) -> do
                              lift (display_info opts outs old new)
                              continue exp
                        | otherwise -> lift display_commands >> continue exp
      (":display", _)   -> lift (display ctx) >> continue exp
      (":d", _)         -> lift (display ctx) >> continue exp 
      (":spec", mty)    -> lift (display_spec ctx mty) >> continue exp
      (":session", _)   -> outputStrLn (showTree exp) >> continue exp 
      (":s", _)         -> outputStrLn (showTree exp) >> continue exp 
      (":options", _)   -> lift (display_all_triggers ctx) >> continue exp 
      (":o", _)         -> lift (display_all_triggers ctx) >> continue exp
      (":help", _)      -> lift display_commands >> continue exp
      (":h", _)         -> lift display_commands >> continue exp
      (":quit", _)      -> return ()
      (":q", _)         -> return ()
      ((':':mint),_)    -> repl_trigger ctx mint
      ("#include", fp') -> repl_directive opts (Include fp) exp >>= continue 
        where fp = case readMaybe fp' of Nothing  -> dropWhile isSpace fp' 
                                         Just str -> str
      ("#require", fp') -> repl_directive opts (Require fp) exp >>= continue 
        where fp = case readMaybe fp' of Nothing  -> dropWhile isSpace fp' 
                                         Just str -> str
      _                 -> repl_recognize_phrase input
  where continue = repl opts
        repl_trigger ctx mint = case readMaybe (dropWhile isSpace mint) of
          Just trig | trig <= length (rest_transitions ctx), trig > 0
            -> repl_phrases opts emptyInput [PDo (fst $ map get_transition (rest_transitions ctx) !! (trig - 1))] exp >>= continue
          _ -> lift display_commands >> continue exp

        repl_recognize_phrase str = case parse_component syn_phrases str of
          Left err  -> outputStrLn err >> continue exp
          Right ps  -> repl_phrases opts emptyInput ps exp >>= continue

repl_directive_phrases :: Options -> [Either Directive Phrase] -> Explorer -> InputT IO Explorer
repl_directive_phrases opts [] explorer = return explorer
repl_directive_phrases opts (edp:ps) explorer = 
  case edp of 
   Left d  -> repl_directive opts d explorer >>= repl_directive_phrases opts ps
   Right p -> repl_phrases opts emptyInput [p] explorer >>= repl_directive_phrases opts ps
 where (_,_,(_,ctx)) = get_last_edge explorer (EI.currRef explorer) 
       isQuery phrase = case phrase of PQuery _ -> True
                                       _        -> False 

repl_phrases :: Options -> InputMap -> [Phrase] -> Explorer -> InputT IO Explorer 
repl_phrases opts inpm phrases explorer = 
  repl_report opts inpm phrases (run_ explorer (Execute (convert_programs phrases) inpm)) explorer

repl_directive :: Options -> Directive -> Explorer -> InputT IO Explorer 
repl_directive opts (Include fp) explorer = repl_import opts fp explorer
repl_directive opts (Require fp) explorer 
  | has_been_included fp opts = return explorer
  | otherwise                 = repl_import opts fp explorer

repl_import :: Options -> FilePath -> Explorer -> InputT IO Explorer
repl_import opts fp explorer = do
  let dirs = find include_paths opts
  files <- lift $ find_included_file dirs fp
  case files of 
    []       -> lift $ putStrLn ("could not find " ++ fp ++ " in " ++ show dirs) >> return explorer
    (file:_) -> do
      lift $ add_include_path (takeDirectory file) opts
      lift $ add_include file opts
      case ".json" `isSuffixOf` file of 
       True -> do
          mspec <- lift (decode_json_file file)
          case mspec of
            Left err -> lift (putStrLn err) >> return explorer
            Right spec -> lift (putStrLn "including .json files is no longer supported") >> return explorer --repl_directive_phrases opts [Right (PFrames spec)] explorer
       False -> lift (catchIOError (Right <$> readFile file) handler) >>= \case 
        Left err  -> lift (putStrLn err) >> return explorer
        Right str -> case parse_component syn_directives_phrases str of
          Left err -> lift (putStrLn err) >> return explorer
          Right eps -> repl_directive_phrases opts eps explorer
 where handler :: IOError -> IO (Either String a)
       handler exc | isDoesNotExistError exc = return (Left ("unknown file: " ++ fp))
                   | isPermissionError exc = return (Left ("cannot read: " ++ fp))
                   | isAlreadyInUseError exc = return (Left ("in use: " ++ fp))
                   | otherwise               = return (Left (show exc))


repl_report :: Options -> InputMap -> [Phrase] -> -- both used for re-execution in case of missing input 
                  Response -> Explorer -> InputT IO Explorer
repl_report opts inpm phrases res exp = case res of
  ResultTrans exp outs (old,_) (ctx,sid) -> case missing_inputs outs of
    []  -> lift (verbosity opts 3 (display_info opts outs old ctx)) >> return exp
    ms  -> do minpm <- foldM consider (Just inpm) ms
              case minpm of Just inpm' -> repl_phrases opts inpm' phrases exp 
                            Nothing -> return exp
      where consider Nothing _ = return Nothing
            consider (Just inpm) te@(_,d) = do
              mass <- lift (consume_input opts)
              let tryWith b = Just $ M.insert te b inpm
              case mass of
                Just b  -> return (tryWith b)
                Nothing -> do
                  lift $ putStrLn ("\nmissing truth-value for: " ++ ppTagged te)
                  lift $ putStrLn ("is this fact True or False?") 
                  getInputLine "(True/False) > " >>= \case
                    Just s  -> return $ tryWith (readAssignmentMaybe s)
                    Nothing -> return Nothing
  InvalidRevert                          -> error "REPL.assert 1"

display_commands = 
 putStrLn  "Available commands:\n\
           \  :<INT>          same as :choose <INT>\n\
           \  :choose <INT>   choose action or event trigger <INT>\n\
           \  :force  <INT>   choose and force action or event trigger <INT>\n\
           \  :revert <INT>   revert to the configuration with id <INT>\n\
           \  :display :d     show all contents of the current configuration\n\
           \  :spec           pretty-print all type definitions\n\
           \  :session :s     show the history of the session\n\
           \  :options :o     show all actions & events, including disabled actions\n\
           \  :help :h        show these commands\n\
           \  :quit :q        end the exploration\n\
           \ or just type a <PHRASE>"

display_info :: Options -> [Output] -> Config -> Config -> IO ()
display_info opts outs c0 cfg = do
  verbosity opts 4 $ display_errors (errors outs) 
  verbosity opts 5 $ display_query_results (query_ress outs)
  verbosity opts 6 $ display_transitions (ex_triggers outs)
  verbosity opts 7 $ display_violations (violations outs)
  verbosity opts 8 $ display_new_types (M.keysSet $ decls $ cfg_spec c0) (M.keysSet $ decls $ cfg_spec cfg)
  verbosity opts 9 $ display_fact_changes (cfg_state c0) (cfg_state cfg)
  verbosity opts 10$ display_new_invariants (invariants $ cfg_spec c0) (invariants $ cfg_spec cfg)
  where display_query_results [] = return ()
        display_query_results ress = mapM_ op ress
          where op QuerySuccess = verbosity opts 11 (putStrLn "query successful")
                op QueryFailure = verbosity opts 12 (putStrLn "query failed")

        display_errors [] = return ()
        display_errors errs = mapM_ op errs
          where op (CompilationError err)     = putStr err
                op err                        = putStrLn (print_error err)


display_violations [] = return () 
display_violations vs = putStrLn "violations:" >> mapM_ op vs
          where op (DutyViolation te)       = putStrLn ("  violated duty!: " ++ ppTagged te)
                op (InvariantViolation d)   = putStrLn ("  violated invariant!: " ++ d)
                op (TriggerViolation tinfo) = putStrLn ("  disabled " ++ trans_type ++ ": " ++ ppTagged (trans_tagged tinfo))
                  where trans_type = if trans_is_action tinfo then "action" else "event"

display_transitions = mapM_ display_transition 
display_transition trans = do 
  putStr ("executed transition: \n") 
  putStr (showTriggerTree trans)
        
display_fact_changes :: State -> State -> IO ()
display_fact_changes prev cur = do
  display_facts "~" (S.toList (M.keysSet (contents prev) `S.difference` M.keysSet (contents cur)))
  display_facts "-" (state_not_holds cur \\ state_not_holds prev)
  display_facts "+" (state_holds cur \\ state_holds prev)
  where display_facts pref fs = mapM_ op fs
          where op f = putStrLn (pref ++ ppTagged f)

display_new_types :: S.Set DomId -> S.Set DomId -> IO ()
display_new_types prev cur = do
  display_type_info "New type " (S.toList (cur `S.difference` prev)) 
  display_type_info "Removed type "  (S.toList (prev `S.difference` cur))
  where display_type_info pref ts = mapM_ op ts
          where op t = putStrLn (pref ++ t)

display_new_invariants :: S.Set DomId -> S.Set DomId -> IO ()
display_new_invariants prev cur = do  
  display_invariants "New invariant " (cur S.\\ prev)
  display_invariants "Removed invariant " (prev S.\\ cur)
  where display_invariants pref is = mapM_ op (S.toList is)
          where op i = putStrLn (pref ++ i)

display_all_triggers :: Config -> IO ()
display_all_triggers cfg = display_triggers "" (map get_transition (rest_transitions cfg))

display_triggers str tes = display_triggers' tes 
 where  display_triggers' []  = putStrLn ("no " ++ str ++ "actions or events")
        display_triggers' tes = putStrLn (str ++ "actions & events:") >> mapM_ op (zip [1..] tes)
          where op (i, (te,en)) = putStrLn (show i ++ ". " ++ ppTagged te ++ enabled)
                  where enabled | en = " (ENABLED)"
                                | otherwise = " (DISABLED)"

display :: Config -> IO ()
display cfg = putStrLn (show (cfg_state cfg))

display_spec :: Config -> String -> IO ()
display_spec ctx mty = case find_decl (cfg_spec ctx) ty of
  Nothing     -> forM_ (M.assocs (decls (cfg_spec ctx))) (putStrLn . uncurry ppDeclSpec) 
  Just tspec  -> putStrLn (ppDeclSpec ty tspec) 
  where ty = dropWhile isSpace mty
