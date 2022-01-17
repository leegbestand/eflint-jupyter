{-# LANGUAGE LambdaCase #-}

module Main where

import Sim (test_scenario, TestResult(..))
import StaticEval (compile_all)
import Parse (parse_frames, parse_initialiser, parse_refiner, parse_scenario, parse_flint)
import JSON(decode_json_file)

import Control.Monad (when)
import Data.List (isSuffixOf, isPrefixOf)
import Data.Aeson
import qualified Data.ByteString.Lazy.Char8

import System.Environment

main :: IO ()
main = getArgs >>= arg_select 

arg_select :: [String] -> IO ()
arg_select args = 
  let (files, flags) = span (not . isPrefixOf "--") args
  in case files of 
       [f] | not (".json" `isSuffixOf` f) -> exec_single args f
       [f,r,i]    -> exec args f r i Nothing
       [f,r,i,s]  -> exec args f r i (Just s)
       _ -> putStrLn "Please provide one, three, or four input files followed by zero or more flags.\n\nPossible input file combinations:\n\ta complete file containing both a policy description, a refinement, an initial state and a scenario\n\tthree files containing a policy description, refinement and initial state respectively\n\tfour files containing a policy description, refinement, initial state, and scenario respectively.\n Possible flags:\n\t--json"

exec :: [String] -> String -> String -> String -> Maybe String -> IO ()
exec args fsrc rsrc isrc msrc = do
  f_res <- spec_reader fsrc
  r   <- readFile rsrc
  i   <- readFile isrc
  ms  <- maybe (return Nothing) ((Just <$>) . readFile) msrc
  case f_res of
    Left err -> putStrLn "could not parse frames:\n" >> putStrLn err
    Right frames -> case parse_refiner r of
      Left err -> putStrLn "could not parse refinement specification:\n" >> putStrLn err
      Right refiner -> case parse_initialiser i of
        Left err -> putStrLn "could not parse initial state specification:\n" >> putStrLn err
        Right initialiser -> case fmap parse_scenario ms of 
          Nothing -> compile_and_run args frames refiner initialiser []
          Just (Left err) -> putStrLn "could not parse scenario specification:\n" >> putStrLn err
          Just (Right scenario) -> compile_and_run args frames refiner initialiser scenario

exec_single args fsrc = do
  fl <- readFile fsrc
  case parse_flint fl of 
    Left err -> putStrLn "could not parse flint spec:\n" >> putStrLn err
    Right (f,r,i,s) -> compile_and_run args f r i s

spec_reader fsrc | ".json" `isSuffixOf` fsrc = decode_json_file fsrc
                 | otherwise                 = fmap fst . parse_frames <$> readFile fsrc


compile_and_run args f r i s = 
  case compile_all f r i s of
    Right (spec',r',i',s') -> case "--json" `elem` args of
        True  -> Data.ByteString.Lazy.Char8.putStrLn (encode tr)
        False -> do mapM_ putStrLn (errors tr) 
                    when (not (null (errors tr))) $ 
                      mapM_ putStrLn (alternative_actions tr)
     where tr = test_scenario spec' r' i' s' True 
    Left errs   -> putStrLn "compilation errors:" >> putStrLn (unlines errs) 

