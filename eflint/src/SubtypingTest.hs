
import Sim
import Spec
import EDSL

import qualified Data.Map as M
import qualified Data.Set as S

main = run spec 

spec = Spec {
    types       = facts `M.union` duties `M.union` acts
  , initialiser = S.fromList 
      [("make request", M.fromList [("person", _c (String "chloe", "person"))] )  
      ,("biological parent", M.fromList [("parent", _c (String "bob", "person"))
                                        ,("child", _c (String "alice", "person"))])
      ,("adoptive parent", M.fromList [("parent", _c (String "david", "person"))
                                      ,("child", _c (String "chloe", "person"))])
      ]
  , aliases     = M.empty 
  }

facts = M.fromList [
    ("system", TypeSpec { kind = Fact, range = Strings ["system"] })
  , ("person", TypeSpec { kind = Fact, range = Strings ["alice", "bob", "chloe", "david", "eli"] } )
  , ("biological parent", TypeSpec { kind = Fact, range = products ["person", "person"] } )
  , ("adoptive parent", TypeSpec { kind = Fact, range = products ["person", "person"] } )
  , ("legal guardian", TypeSpec { kind = Fact, range = sums ["biological parent", "adoptive parent"] } )
  , ("registration", TypeSpec { kind = Fact, range = products ["person"] } )
  ]

duties = M.empty

register_ty = TypeSpec  { kind = Act register_extra
                        , range = products ["legal guardian", "person", "registration"] }
register_extra = ActSpec  { condition  = BoolLit True
                          , terminates = []
                          , creates = ["registration"] } 

make_request_ty = TypeSpec  { kind = Act make_request_extra
                            , range = products ["person", "system", "registration"] }
make_request_extra = ActSpec  { condition = BoolLit True
                              , terminates = []
                              , creates = [ "register" ] }

acts = M.fromList [
    ("make request", make_request_ty)
  , ("register", register_ty)
  ]

