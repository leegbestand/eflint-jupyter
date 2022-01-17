{-# LANGUAGE LambdaCase #-}

module Util where

import Control.Monad (forM)
import System.FilePath
import System.Directory

find_included_file :: [FilePath] -> FilePath -> IO [FilePath]
find_included_file dirs path = do 
  concat <$> forM dirs (\dir -> do 
    let file = dir </> path 
    doesFileExist file >>= \case True  -> return [file]
                                 False -> (doesFileExist (file ++ ".eflint") >>= \case True  -> return [file ++ ".eflint"]
                                                                                       False -> return []))

