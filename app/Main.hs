module Main where

import qualified Data.Text as T

import System.Environment (getArgs)

import IHaskell.IPython.EasyKernel (easyKernel, installKernelspec, KernelConfig(..))
import IHaskell.IPython.Types
import Control.Monad.State
import Language.EFLINT.Interpreter (Config(..), initialConfig, Output(..), Program(..), collapse_programs, convert_programs)
import Language.EFLINT.Parse
import Language.EFLINT.Explorer (defInterpreter, Instruction (Display))
import Language.EFLINT.State
import Language.EFLINT.Spec (Phrase, ppTagged)
import Language.EFLINT.Print
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List

type Runtime = StateT Config IO

languageConfig :: LanguageInfo
languageConfig = LanguageInfo
  { languageName = "eFLINT"
  , languageVersion = "1.0.0"
  , languageFileExtension = ".eflint"
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
displayViolation (DutyViolation te)       = "Violated duty!: " ++ ppTagged te
displayViolation (InvariantViolation d)   = "Violated invariant!: " ++ d
displayViolation (TriggerViolation tinfo) = "Disabled " ++  trans_type ++ ": " ++ ppTagged (trans_tagged tinfo)
  where trans_type = if trans_is_action tinfo then "action" else "event"

displayFactChanges :: Language.EFLINT.State.State -> Language.EFLINT.State.State -> String
displayFactChanges prev cur = unlines .  concat $
  [ display_facts "~" (S.toList (M.keysSet (contents prev) `S.difference` M.keysSet (contents cur)))
  , display_facts "-" (state_not_holds cur \\ state_not_holds prev)
  , display_facts "+" (state_holds cur \\ state_holds prev)
  ]
  where display_facts pref fs = map op fs
          where op f = pref ++ ppTagged f


displayError :: Error -> String
displayError (CompilationError err) = err
displayError err = print_error err



-- We should have a pretty printer for Output. This is the third function that transforms it into a string??
displayOut :: [Output] -> [String]
displayOut = map displayOut'
    where
        displayOut' (ErrorVal e) = displayError e
        displayOut' (QueryRes QuerySuccess) = "Query success"
        displayOut' (QueryRes QueryFailure) = "Query failed"
        displayOut' (Violation v) = displayViolation v
        displayOut' (ExecutedTransition info) = unlines $ map (("Executed transition: " ++) . ppTagged . trans_tagged) (trans_all_infos info)

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
        (Just c, out) -> put c >> case displayFactChanges (cfg_state c0) (cfg_state c) of
           [] -> return (out, IHaskell.IPython.Types.Ok, "")
           s  -> liftIO (intermediate s) >> return (out, IHaskell.IPython.Types.Ok, "")
        (Nothing, out) -> lift (print $ displayOut out) >> return (out, IHaskell.IPython.Types.Ok, "")


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

