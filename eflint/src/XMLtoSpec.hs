module XMLtoSpec where

import Text.XML.HXT.Core

import Loader
import Parse (flint_parser, decorated_type) 
import Spec

import qualified Data.Map as M
import qualified Data.Set as S

xml_to_spec :: IOStateArrow s XmlTree Spec
xml_to_spec = 
  (   get_frames 
    &&&
      get_initials
    &&&
      get_aliases
  ) >>>
  make_spec

make_spec :: IOStateArrow s (M.Map Type TypeSpec, (Initialiser, M.Map Type Expr)) Spec
make_spec = arr make_spec' 
  where make_spec' (x,(y,z)) = x 

xml_to_scenario :: IOStateArrow s XmlTree Scenario
xml_to_scenario = 
  listA   (deep (isElem >>> hasName "scenario") >>> 
          getChildren >>> hasName "step" >>> make_transition_filter)

make_transition_filter :: IOStateArrow s XmlTree TransitionFilter 
make_transition_filter = 
  listA (getChildren >>> hasName "decomposition" >>>
      (   (getChildren >>> hasName "type" >>> parser_type_name) 
      &&& (listA (getChildren >>> hasName "binding" >>> make_binding) >>> arr M.unions)
      )) >>> arr S.fromList

get_frames :: IOStateArrow s XmlTree  (M.Map Type TypeSpec)
get_frames = (get_ifactframes &&& get_iactframes &&& get_idutyframes) >>> arr unite
  where unite (m1,(m2,m3)) = M.unions [m1,m2,m3]

get_ifactframes, get_idutyframes, get_iactframes :: IOStateArrow s XmlTree (M.Map Type TypeSpec)

get_ifactframes = 
  listA (deep (hasName "ifact-frame") >>> 
        (getAttrValue "id" &&& (getChildren >>> parser_type_expr >>> arr (TypeSpec (Fact Nothing))))) >>> 
  arr M.fromList

get_idutyframes =
  listA (deep (hasName "iduty-frame") >>>   
  (   getAttrValue "id"
  &&& (getChildren >>> hasName "holder" >>> getChild >>> getChild >>> parser_type_ref)
  &&& (getChildren >>> hasName "claimant" >>> getChild >>> getChild >>> parser_type_ref)
  &&& (listA (getChildren >>> hasName "ifact-ref" >>> getChild >>> parser_type_ref))
  &&& listA (getChildren >>> hasName "terminating_acts" >>> getChildren >>> parser_type)
  &&& listA (getChildren >>> hasName "enforcing_acts" >>> getChildren >>> parser_type)
  ) >>> arr cons_idutyframe ) >>>
  arr M.fromList
  where cons_idutyframe (ty, (holder, (claimant, (others, (terms, enfs))))) = 
          (ty, TypeSpec { kind = Duty (DutySpec { terminating_acts = terms, enforcing_acts = enfs } )
                        , domain = Products ([holder, claimant] ++ others) } )

get_iactframes = 
  listA (deep (hasName "iact-frame") >>>   
  (   getAttrValue "id"
  &&& (getChildren >>> hasName "actor" >>> getChild >>> getChild >>> parser_type_ref)
  &&& (getChildren >>> hasName "subject" >>> getChild >>> getChild >>> parser_type_ref)
  &&& (listA (getChildren >>> hasName "ifact-ref" >>> getChild >>> parser_type_ref))
  &&& (getChildren >>> hasName "value-expr" >>> parser_value_expr)
  &&& listA (getChildren >>> hasName "iterminates" >>> getChildren >>> parser_type_ref)
  &&& listA (getChildren >>> hasName "icreates" >>> getChildren >>> parser_type_ref)
  ) >>> arr cons_iactframe ) >>>
  arr M.fromList
  where cons_iactframe (ty, (actor, (subject, (others, (cond, (terms, cs)))))) = 
          (ty, TypeSpec { kind = Act (ActSpec { condition = cond, terminates = terms, creates = cs } )
                        , domain = Products ([actor, subject] ++ others) } )

get_aliases :: IOStateArrow s XmlTree (M.Map Type Expr)  
get_aliases = listA (
  deep (isElem >>> hasName "alias") >>>  
    (getAttrValue "id" &&& (getChildren >>> parser_value_expr))) >>> 
  arr M.fromList

get_initials :: IOStateArrow s XmlTree Initialiser
get_initials = deep (isElem >>> hasName "initials") >>> make_transition_filter

-- | assumes that the received tree is a fact/duty/act "element"
make_env :: IOStateArrow s XmlTree Env 
make_env = 
 (  (listA (getChildren >>> hasAttr "type" >>> make_env) >>> arr M.unions)
  &&& 
    (getAttrValue "type" >>> make_decorated_type) 
  &&& 
    make_tagged
 )>>> 
    arr add_entry
  where add_entry :: (Env, (DecType, Tagged)) -> Env 
        add_entry (env, (dty, c)) = M.insert dty c env

make_decorated_type :: IOStateArrow s String DecType
make_decorated_type = arrL (flint_parser decorated_type)

make_binding :: IOStateArrow s XmlTree Env
make_binding = 
  hasName "binding" >>> ((getChildren >>> hasName "type" >>> parser_type) &&& make_tagged) >>> 
  arr (uncurry M.singleton)
     
make_tagged :: IOStateArrow s XmlTree Tagged
make_tagged = ((getChildren >>> hasName "type" >>> parser_type) &&& make_value) >>> arr cons
  where cons (dty, val) = (val, remove_decoration dty, emptyProps)

make_value :: IOStateArrow s XmlTree Value
make_value = listA (getChildren >>> hasName "element" >>> getChild) >>> isA (not . null) >>> 
      (   (isA ((1==) . length) >>> unlistA >>> make_simple)
      <+> (isA ((>1) . length) >>> make_product))

make_simple :: IOStateArrow s XmlTree Value
make_simple =
      (hasName "string" >>> getChildren >>> (getText <+> getCdata) >>> arr String)
 <+>  (hasName "int" >>> getChildren >>> (getText <+> getCdata) >>> arr (Int . read))
 <+>  (hasAttr "type" >>> make_tagged >>> arr (Product . (:[])))

make_product :: IOStateArrow s [XmlTree] Value 
make_product = 
  listA (unlistA >>> hasAttr "type" >>> make_tagged) >>> isA (not . null) >>> arr Product 

getChild :: (ArrowTree a, Tree t) => a (t b) (t b)
getChild = listA getChildren >>> isA ((1==) . length) >>> unlistA 
