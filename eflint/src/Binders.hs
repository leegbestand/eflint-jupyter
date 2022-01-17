
module Binders where

import Spec

import qualified Data.Set as S

class HasVars a where
  free :: Spec -> a -> S.Set Var

instance HasVars a => HasVars [a] where
  free spec as = S.unions (map (free spec) as)

instance HasVars Term where
  free spec t = case t of
    BoolLit _   -> S.empty
    IntLit _    -> S.empty
    StringLit _ -> S.empty
    CurrentTime -> S.empty

    Ref v       -> S.singleton v
    App d args  -> case fmap domain (find_decl spec d) of
                    Just (Products xs)  -> (S.fromList xs `S.difference` S.fromList (map fst replacements))
                                              `S.union` free spec (map snd replacements)
                      where replacements = make_substitutions_of xs args 
                    _                   -> free spec (either id (map (\(Rename p q) -> q)) args)

    Not t       -> free spec t
    Present t   -> free spec t
    Violated t  -> free spec t
    Enabled t  -> free spec t
    Project t x -> free spec t
    Tag t x     -> free spec t
    Untag t     -> free spec t

    And t1 t2   -> free spec t1 `S.union` free spec t2
    Or  t1 t2   -> free spec t1 `S.union` free spec t2
    Leq t1 t2   -> free spec t1 `S.union` free spec t2
    Geq t1 t2   -> free spec t1 `S.union` free spec t2
    Ge  t1 t2   -> free spec t1 `S.union` free spec t2
    Le  t1 t2   -> free spec t1 `S.union` free spec t2
    Mult t1 t2  -> free spec t1 `S.union` free spec t2
    Mod t1 t2   -> free spec t1 `S.union` free spec t2
    Div  t1 t2  -> free spec t1 `S.union` free spec t2
    Sub t1 t2   -> free spec t1 `S.union` free spec t2
    Add t1 t2   -> free spec t1 `S.union` free spec t2
    Eq  t1 t2   -> free spec t1 `S.union` free spec t2
    Neq t1 t2   -> free spec t1 `S.union` free spec t2
    When t1 t2  -> free spec t1 `S.union` free spec t2

    Exists xs t -> free spec t `S.difference` S.fromList xs
    Forall xs t -> free spec t `S.difference` S.fromList xs
    Count  xs t -> free spec t `S.difference` S.fromList xs
    Max    xs t -> free spec t `S.difference` S.fromList xs
    Min    xs t -> free spec t `S.difference` S.fromList xs
    Sum    xs t -> free spec t `S.difference` S.fromList xs
