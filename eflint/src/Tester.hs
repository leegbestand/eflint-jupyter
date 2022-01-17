
module Main where

import Eval
import StaticEval
import Explorer
import State

main = getArgs >>= arg_select 

arg_select :: [String] -> IO ()
arg_select args = 
  let (files, flags) = span (not . isPrefixOf "--") args
  in case files of
       [] -> repl_without flags 
       [f] | ".eflint" `isSuffixOf` f -> repl_with flags f
       _ -> putStrLn "Please provide: <NAME>.eflint <OPTIONS>"


