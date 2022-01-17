module EDSL where

import Spec

_c :: (Value, DomId) -> Tagged
_c (c, t) = _c (c,t)

products :: [Var] -> Domain 
products = Products

products' :: [DomId] -> Domain
products' = products . map (flip Var "") 

