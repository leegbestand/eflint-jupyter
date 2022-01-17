module Main where

import qualified Data.Text as T

import System.Environment (getArgs)

import IHaskell.IPython.EasyKernel (easyKernel, installKernelspec, KernelConfig(..))
import IHaskell.IPython.Types
import Control.Monad.State
import Interpreter (Config(..), initialConfig, Output(..), Program(..), collapse_programs, convert_programs)
import Parse
import NewExplorer (defInterpreter, Instruction (Display))
import State
import Spec (Phrase, ppTagged)
import Print
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List

type Runtime = StateT Config IO

languageConfig :: LanguageInfo
languageConfig = LanguageInfo
  { languageName = "funcalc"
  , languageVersion = "1.0.0"
  , languageFileExtension = ".txt"
  , languageCodeMirrorMode = "null"
  , languagePygmentsLexer = "Text"
  , languageMimeType = "x/eflint"
  }

-- redundant for now since ihaskell uses ipython and not jupyter for installation.
languageKernelspec :: KernelSpec
languageKernelspec = KernelSpec
  { kernelDisplayName = "eflint"
  , kernelLanguage = "eflint"
  , kernelCommand = []
  }

simpleConfig :: KernelConfig Runtime String [Output]
simpleConfig = KernelConfig
  { kernelLanguageInfo = languageConfig
  , writeKernelspec = const $ return languageKernelspec
  , displayOutput = displayString
  , displayResult = displayStrings . displayOut
  , completion = languageCompletion
  , inspectInfo = languageInspect
  , run = languageRun
  , debug = False
  , kernelBanner = "eFLINT Jupyter"
  , kernelProtocolVersion = "5.0"
  , kernelImplName = "eflint"
  , kernelImplVersion = "0.0"
  }

displayString :: String -> [DisplayData]
displayString str = [DisplayData PlainText (T.pack str)]

displayViolation :: Violation -> String
displayViolation (DutyViolation te)       = "violated duty!: " ++ ppTagged te
displayViolation (InvariantViolation d)   = "violated invariant!: " ++ d
displayViolation (TriggerViolation tinfo) = "disabled " ++  trans_type ++ ": " ++ ppTagged (trans_tagged tinfo)
  where trans_type = if trans_is_action tinfo then "action" else "event"

displayFactChanges :: State.State -> State.State -> String
displayFactChanges prev cur = unlines .  concat $
  [ display_facts "~" (S.toList (M.keysSet (contents prev) `S.difference` M.keysSet (contents cur)))
  , display_facts "-" (state_not_holds cur \\ state_not_holds prev)
  , display_facts "+" (state_holds cur \\ state_holds prev)
  ]
  where display_facts pref fs = map op fs
          where op f = pref ++ ppTagged f


displayError :: Error -> String
-- displayError (DisabledTransition te)    = "not a compliant action"
displayError NonDeterministicTransition = "non-deterministic transition attempt"
displayError (CompilationError err)     = err


-- We should have a pretty printer for Output. This is the third function that transforms it into a string??
displayOut :: [Output] -> [String]
displayOut = map displayOut'
    where
        displayOut' (ErrorVal e) = displayError e
        displayOut' (QueryRes QuerySuccess) = "Query success"
        displayOut' (QueryRes QueryFailure) = "Query failed"
        displayOut' (Violation v) = displayViolation v
        displayOut' _ = ""

displayStrings :: [String] -> [DisplayData]
displayStrings = displayString . unlines

languageCompletion :: Monad m => T.Text -> Int -> m (T.Text, [T.Text])
languageCompletion code pos = return (T.pack "", [])

languageInspect :: Monad m => T.Text -> Int -> m (Maybe [DisplayData])
languageInspect _ _ = return Nothing

languageRun :: T.Text -> IO () -> (String -> IO ()) -> Runtime ([Output], ExecuteReplyStatus, String)
languageRun code init intermediate = do
  liftIO init
  let p = parse_component syn_phrases $ T.unpack code
  case p of
    Left err   -> return ([ErrorVal (CompilationError err)], IHaskell.IPython.Types.Ok, "")
    Right expr -> get >>= \c0 -> case defInterpreter (emptyInput, (collapsePrograms . convertPrograms $ expr)) c0 of
        (Just c, out) -> put c >> liftIO (intermediate (displayFactChanges (cfg_state c0) (cfg_state c)))
          >> return (out, IHaskell.IPython.Types.Ok, "")
        (Nothing, out) ->  return (out , IHaskell.IPython.Types.Ok, "")


convertPrograms :: [Phrase] -> [Program]
convertPrograms = map Program

collapsePrograms :: [Program] -> Program
collapsePrograms [] = ProgramSkip
collapsePrograms programs = foldr1 PSeq programs


main :: IO ()
main = do
  args <- getArgs
  case args of
    ["kernel", profileFile] ->
        evalStateT (easyKernel profileFile simpleConfig) (initialConfig Nothing)
    _ -> do
      putStrLn "Usage:"
      putStrLn
        "eflint-jupyter kernel FILE"

