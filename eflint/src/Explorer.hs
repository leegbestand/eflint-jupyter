module Explorer where

import Spec
import Eval
import State
import Saturation
import StaticEval (compile_phrase)

import Control.Monad (forM)
import Data.Maybe (fromJust)
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Set as S
import Data.IORef

-- | Simplified exploring interpreter algorithm, builds a tree rather than a graph 
type Explorer = Instruction -> IO Response

data Instruction = Execute CPhrase
                 | CompileAndExecute [Phrase]
                 | Revert Int
                 | Display
                 | DisplayFull
data Response    = ResContext Context (Int, Context)
                 | Path Path
                 | ExecError Error
                 | CompilationError String
                 | InvalidRevert

type SID = Int -- state identifier

type Ancestry = IM.IntMap (CPhrase, SID) -- mapping from newer to older, with the phrase that produced newer
type SIDMap   = IM.IntMap Context

type Path = [((SID, Context), CPhrase, (SID, Context))] 

init_explorer :: Spec -> State -> IO Explorer 
init_explorer spec state = do 
  seed_ref  <- newIORef 0
  conf_ref  <- newIORef 0
  let initialState = modify_ctx_state (rebase_and_sat' spec state) (emptyContext spec)
  sid_ref   <- newIORef (IM.fromList [((-1), emptyContext spec), (0,initialState)])
  ans_ref   <- newIORef (IM.singleton 0 (CFrames spec,-1))
  return (run_explorer conf_ref seed_ref sid_ref ans_ref)

get_ancestor :: SID -> IORef SIDMap -> IORef Ancestry -> IO (Context, Context)
get_ancestor sid sid_ref ans_ref = do
  ans_map <- readIORef ans_ref
  sid_map <- readIORef sid_ref 
  let new = sid_map IM.! sid
  case IM.lookup sid ans_map of
    Nothing       -> return (new, new) --sid must be root
    Just (p,sid') -> return (sid_map IM.! sid', new)

get_ancestor_response sid sid_ref ans_ref = 
  (\(old, new) -> ResContext old (sid, new)) <$> get_ancestor sid sid_ref ans_ref

get_history_response sid sid_ref ans_ref = Path <$> get_path sid_ref ans_ref sid

get_path :: IORef SIDMap -> IORef Ancestry -> Int -> IO Path 
get_path sid_ref ans_ref sid = do
  edge@((sid',_),_,(sid'',_)) <- get_edge sid_ref ans_ref sid
  if sid' == sid'' then return [edge]
                   else (edge:) <$> get_path sid_ref ans_ref sid'

get_edge :: IORef SIDMap -> IORef Ancestry -> Int -> IO ((SID, Context), CPhrase, (SID, Context)) 
get_edge sid_ref ans_ref to_sid = do
  ans_map <- readIORef ans_ref
  sid_map <- readIORef sid_ref 
  let to_ctx = sid_map IM.! to_sid
  let (from_sid, from_ctx, phrase) = case IM.lookup to_sid ans_map of
        Nothing           -> (to_sid, to_ctx, CEmptyConfig) --self-edge at root
        Just (p,from_sid) -> (from_sid, sid_map IM.! from_sid, p)
  return ((from_sid, from_ctx), phrase, (to_sid, to_ctx))

run_explorer :: IORef Int -> IORef Int -> IORef SIDMap -> IORef Ancestry -> Explorer
run_explorer conf_ref seed_ref sid_ref ans_ref inst = do
  (conf, ctx) <- readCurrentContext conf_ref sid_ref
  case inst of
    Execute phrase -> do
      let old = ctx
      ctx <- return (sem_phrase phrase ctx)
      modifyIORef seed_ref succ
      seed <- readIORef seed_ref 
      modifyIORef sid_ref (IM.insert seed ctx)
      modifyIORef conf_ref (const seed)
      modifyIORef ans_ref (IM.insert seed (phrase,conf))
      get_ancestor_response seed sid_ref ans_ref
    CompileAndExecute phrases -> 
      let compile_and_execute old [] = compile_and_execute old [PSkip]
          compile_and_execute old (p:ps) = do 
            (_, ctx) <- readCurrentContext conf_ref sid_ref
            case compile_phrase p ctx of 
              Left err -> return (CompilationError (unlines err))
              Right p' -> do  res <- run_explorer conf_ref seed_ref sid_ref ans_ref (Execute p')
                              case res of 
                                ResContext _ new -> if null ps then return (ResContext old new)
                                                               else compile_and_execute old ps
                                _ -> return res
      in compile_and_execute ctx phrases
    Revert mconf' -> do
      seed <- readIORef seed_ref
      case conf' > seed of
       True   -> return InvalidRevert
       False  -> do modifyIORef conf_ref (const conf')
                    get_ancestor_response conf' sid_ref ans_ref -- assumes there is no sharing 
      where conf' = max mconf' 0
    Display -> get_ancestor_response conf sid_ref ans_ref
    DisplayFull -> get_history_response conf sid_ref ans_ref 
  
readCurrentContext :: IORef Int -> IORef (IM.IntMap Context) -> IO (Int, Context)
readCurrentContext conf_ref sid_ref = do
  conf  <- readIORef conf_ref
  sidm <- readIORef sid_ref
  return (conf, sidm IM.! conf)

get_last_edge :: Explorer -> IO (Context, (Int, Context))
get_last_edge exp = do
  ResContext from to <- exp Display
  return (from, to)


