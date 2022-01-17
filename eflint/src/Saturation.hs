{-# LANGUAGE LambdaCase #-}

module Saturation (rebase_and_sat) where

import Spec
import State
import Eval

import Control.Monad (forM)
import Control.Applicative (empty)

import qualified Data.Map as M
import qualified Data.Set as S

rebase_and_sat spec = saturate spec . rebase spec

rebase :: Spec -> State -> State
rebase spec s = s { contents = M.filterWithKey op (contents s) }
  where op (_,d) i = not (from_sat i)

saturate :: Spec -> State -> State
saturate spec state = case saturate' spec state of
                        state' | state == state' -> state
                               | otherwise       -> saturate spec state'
 where 
  saturate' spec s = foldl op s (S.toList (derived spec))
    where op s d = case find_decl spec d of 
                    Nothing -> s
                    Just tdecl -> foldl clause s (derivation tdecl) 
                      where clause s (HoldsWhen t) 
                             | Products xs <- domain tdecl = derive [] (When (App d $ Right []) t) s
                             | otherwise = derive [no_decoration d] (When (Ref $ no_decoration d) t) s
                            clause s (Dv xs t) = derive xs t s
            where derive xs t s = let dyn = do tes <- foreach xs (whenTagged (eval t) return) 
                                               forM tes $ \te -> sat_conditions te >>= \case
                                                True  -> return te
                                                False -> empty
                                      ress = case runSubs dyn spec s M.empty M.empty of
                                        Left err -> [] --error ("saturation error:\n" ++ show err)
                                        Right x  -> x
                                  in derive_all (concat ress) s
