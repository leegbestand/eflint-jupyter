
import qualified Data.Map as M

type Element    = (Value, Domain, Props)

type Type       = String -- type identifiers
data DecType    = DecType Type String {- decoration -}
                deriving (Ord, Eq)

remove_decoration :: DecType -> Type
remove_decoration (DecType ty _) = ty

data Domain     = TypeRef DecType
                | Strings [String]
                | Ints [Int]
                | Products [Domain]
                | Sums [Domain]
                | Selection Domain [Constraint]
                | Projection Domain [DecType]
                deriving (Ord, Eq)

data Value      = String String 
                | Int Int
                | Product [Element]
                | Choice Element    -- a value of a "Sums" type, useful to keep track of instantiation process
                deriving (Ord, Eq)

data Props      = Props {
                }
                deriving (Ord, Eq)
eProps = Props {}

type Decomp     = M.Map Domain Element 

type Subs       = M.Map DecType DecType -- in order to instantiate <key> as <value> instead (recursively)

data Constraint   = As DecType DecType -- with type1 renamed to type2
                  deriving (Ord, Eq)

substitutions_of :: [Constraint] -> Subs
substitutions_of = foldr op M.empty 
  where op (As k v) = M.insert k v

type Spec       = M.Map Type Domain

decompose :: Element -> Decomp
decompose e@(v,dom,_) = maybe_insert dom e $ case v of 
  String s    -> M.empty
  Int i       -> M.empty
  Product es  -> M.unions (map decompose es) -- assumes every created element is consistent with itself (consistent = "all elements of equal domain have equal value and properties")
  Choice e    -> decompose e
  where maybe_insert dom@(TypeRef _) e = M.insert dom e
        maybe_insert _ _ = id

-- attempt to create a consistent decomposition from two given decompositions
unify :: Decomp -> Decomp -> Maybe Decomp
unify decom = M.foldrWithKey check (Just decom)
  where check dom e Nothing       = Nothing
        check dom e (Just decom)  | not (M.member dom decom)  = Just (M.insert dom e decom)
                                  | decom M.! dom == e        = Just decom
                                  | otherwise                 = Nothing
 
instantiate :: Spec -> Subs -> DecType -> [Element]
instantiate spec subs dty = 
  case M.lookup dty subs of 
    Just dty' -> instantiate spec subs dty'
    Nothing   ->
      case M.lookup (remove_decoration dty) spec of
        Nothing   -> error ("undeclared type: " ++ remove_decoration dty)
        Just dom  -> [ (v, TypeRef dty, p) | (v,_,p) <- instantiate_domain spec subs dom ]

instantiate_domain_seq :: Spec -> Subs -> [Domain] -> [[Element]]
instantiate_domain_seq spec subs = map fst . foldr op [([], M.empty)]
  where op :: Domain -> [([Element], Decomp)] -> [([Element], Decomp)]
        op dom ess =  [ (e:es, dec')
                      | (es, dec) <- ess
                      , e <- instantiate_domain spec subs dom
                      , let Just dec' = unify dec (decompose e) ]

instantiate_domain :: Spec -> Subs -> Domain -> [Element]
instantiate_domain spec subs dom = case dom of
  TypeRef dty   -> instantiate spec subs dty
  Strings ss    -> [ (String s, dom, eProps) | s <- ss ]
  Ints is       -> [ (Int i, dom, eProps) | i <- is ]
  Products doms -> [ (Product cs, dom, eProps) | cs <- instantiate_domain_seq spec subs doms ]
  Sums doms     -> [ (Choice c, dom, eProps) | dom' <- doms, c <- instantiate_domain spec subs dom ]
  Selection dom' cons -> [ (v, dom, p) | (v,_,p) <- instantiate_domain spec subs' dom' ]
    where subs' = (substitutions_of cons `M.union` subs)
  Projection dom' dtys -> 
    [ (v, dom, eProps) | c <- instantiate_domain spec subs dom', let dec = decompose c 
                       , let v = Product [ dec M.! (TypeRef dty) 
                                         | dty <- dtys, TypeRef dty `M.member` dec ] ]
