{-# LANGUAGE LambdaCase, TupleSections, DeriveGeneric, OverloadedStrings #-}

module Sim where

import Spec
import State
import Eval 
import Saturation

import Control.Monad

import Data.Aeson hiding (String)
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Set as S
import Data.Maybe (fromJust, isNothing) 

import GHC.Generics

test_scenario :: Spec -> Refiner -> Initialiser -> Scenario -> Bool -> TestResult 
test_scenario spec' refiner initialiser scenario positive_test = 
  let (state, tr) = init_test_result spec (make_initial_state spec initialiser)
  in tester scenario spec state positive_test tr 
  where spec = refine_specification spec' refiner

init_test_result :: Spec -> State -> (State, TestResult)
init_test_result spec state0 = 
  let (state1, powers, duties) = normative_positions spec state0
      (state2, breaches) = test_invariants spec state1
  in (state2, empty_test_result spec state2 powers duties breaches)

steps :: Scenario -> Spec -> State -> IO () -- returns the final state
steps scenario spec state = print_state state >> steps' scenario spec state
 where steps' scenario spec state = do
        let (acts, scenario') = select_step_options scenario spec state 
        case acts of 
          []  -> case scenario of 
                    []        -> putStrLn "No more actions to perform..."
                    (stmt:_)  -> putStrLn ("No more actions to perform, restricted by: " ++ show_stmt stmt) 
          [Left (QueryInfo True)] -> steps scenario' spec state
          [Left (QueryInfo False)] -> do putStrLn ("Query at step " ++ show (time state + 1) ++ " failed")
                                         steps scenario' spec state
          _   -> do
            selection <- make_choice spec (concatMap (either (const []) (:[])) acts)
            case selection of 
              Nothing  -> return ()
              Just act -> steps scenario' spec (update_state spec state act)

update_state :: Spec -> State -> TransInfo -> State
update_state spec state act = rebase_and_sat spec (increment_time (fire_act spec state act))

test_single_statement :: Statement -> Spec -> State -> TestResult -> TestResult
test_single_statement s spec state = tester [s] spec state True 

-- | Quiet means test successful
tester :: Scenario -> Spec -> State -> Bool -> TestResult -> TestResult
tester [] spec state positive_test test_result 
  | positive_test  = test_result
  | otherwise      = test_fail (test_err "Last step executed successfully, unexpectedly" test_result)
tester scenario spec state positive_test test_result = 
  let (options, rest) = select_step_options scenario spec state
  in case options of
      [] | positive_test || not (null rest) -> test_fail (test_err ("Non-compliant action at step " ++ show (time state + 1)) test_result)
              | otherwise -> test_result -- negative_test + rest == []
      [option]   -> case option of 
        Right act -> 
          let state1 = update_state spec state act
              (state2, powers, duties) = normative_positions spec state1
              (state3, breaches) = test_invariants spec state2 
          in tester rest spec state3 positive_test (test_step act state3 powers duties breaches test_result)
        Left (QueryInfo True) -> tester rest spec (increment_time state) positive_test (test_repeat_step test_result)
        Left (QueryInfo False) -> tester rest spec (increment_time state) positive_test (test_fail (test_err ("Query at step " ++ show (time state + 1) ++ " failed") (test_repeat_step test_result)))
      options -> test_fail (test_ambig ("Multiple actions available at step " ++ show (time state + 1)) options test_result)

select_step_options :: Scenario -> Spec -> State -> ([Either QueryInfo TransInfo], Scenario)
select_step_options [] spec state = 
  let op (state',res) (k,_) = fmap (res++) $ enables_acts spec state' k
      (_, as) = foldl op (state, []) (M.assocs (contents state))
  in (map Right as, [])
select_step_options (query@(Query t):rest) spec state = 
  let (_,holds) = run_query spec state t 
  in ([Left (QueryInfo {query_success = holds})], rest)
select_step_options (stmt@(Trans xs aty (Left term)):rest) spec state = 
  (, rest) . map Right . snd $ mk_action spec state xs aty term
select_step_options (stmt@(Trans xs t (Right (d,m))):rest) spec state =
  (, rest) . map Right . snd $ mk_action spec state xs t (App d m)

mk_action spec state xs AddEvent t = create_create_act spec state xs t
mk_action spec state xs RemEvent t = create_terminate_act spec state xs t
mk_action spec state xs Trigger  t = enable_act spec state xs t

make_choice :: Spec -> [TransInfo] -> IO (Maybe TransInfo)
make_choice spec [option] = do
  putStrLn "Choosing the following option (only available):"
  putStrLn (show_action option)
  putStrLn "Press <ENTER> to continue"
  _ <- getLine 
  return (Just option)
make_choice spec options = do 
  putStrLn "Choose an act to perform (0 to quit): "
  show_options options
  input <- readLn -- TODO validate input
  if input == 0 then return Nothing
  else if input < 0 || input > length options then make_choice spec options
    else return (Just (options !! (input - 1)))

show_options :: [TransInfo] -> IO ()
show_options options = 
  forM_ (zip [1..] options) $ \(i, option) -> do
    putStrLn (show i ++ ": " ++ show_action option)

print_state :: State -> IO ()
print_state state = print state

-- ### acts

action_actor :: TransInfo -> Tagged
action_actor act = case trans_tagged act of 
  (Product (actor:_),_) -> actor
  _                     -> error "act;actor assert"

show_action :: TransInfo -> String
show_action act = show_component (trans_tagged act) ++ effects
  where effects | trans_type act /= Trigger = []
                | otherwise = concatMap ((" -"++) . show_component) (trans_terminates act) ++ 
                              concatMap ((" +"++) . show_component) (trans_creates act)


create_act :: (Tagged -> TransInfo -> TransInfo) -> Spec -> State -> [Var] -> Term -> (State, [TransInfo])
create_act app spec state xs t = fmap concat $ runSubs creater spec state emptyInput emptySubs
  where creater = do
          taggeds <- foreach xs (whenTagged (eval t) return)
          return [app tagged $ TransInfo { trans_tagged = tagged
                                          , trans_terminates = S.empty
                                          , trans_creates = S.empty
                                          , trans_type = Trigger
                                          , trans_forced = False
                                          , trans_is_action = False } | tagged <- taggeds ]

create_create_act, create_terminate_act :: Spec -> State -> [Var] -> Term -> (State, [TransInfo])
create_create_act = create_act (\t a -> a {trans_terminates = S.empty, trans_creates = S.singleton t})
create_terminate_act = create_act (\t a -> a {trans_terminates = S.singleton t, trans_creates = S.empty})

run_query :: Spec -> State -> Term -> (State, Bool)
run_query spec state t =
  let (s, vs) = runSubs (eval t) spec state emptyInput emptySubs  
  in (s, all (== (ResBool True)) vs)

data QueryInfo  = QueryInfo {
                  query_success  :: Bool
                }

instance ToJSON TransInfo where
  toJSON ai = object ["instance"    .= toJSON (TaggedJSON (trans_tagged ai))
                     ,"creates"     .= toJSON (map TaggedJSON (S.toList (trans_creates ai)))
                     ,"terminates"  .= toJSON (map TaggedJSON (S.toList (trans_terminates ai)))
                     ]

data DutyInfo = DutyInfo {
                duty_name         :: DomId
              , duty_tagged       :: Tagged
              , duty_violated  :: Bool
              }

instance ToJSON DutyInfo where
  toJSON di = object ["instance"    .= toJSON (show_component (duty_tagged di))
                     ,"enforceable" .= toJSON (duty_violated di)
                     ]

test_invariants :: Spec -> State -> (State, [DomId])
test_invariants spec state = foldl op (state, []) (invariants spec)
  where op (state, acc) d = 
          let (state', acc') = runSubs (check d) spec state emptyInput emptySubs
          in (state', acc ++ acc')
        check d = checkFalse (eval (Exists [Var d ""] (Present (Ref (Var d ""))))) >> return d

normative_positions :: Spec -> State -> (State, [TransInfo], [DutyInfo])
normative_positions spec state = --return (state, [], [])
  let op (state0,as,ds) (te@(v,d),_) = case fromJust (fmap kind (find_decl spec d)) of
        Fact _ -> (state0, as, ds)
        Duty dspec ->  
          let (st, vs) = runSubs (eval_violation_condition te (Just $ violated_when dspec)) spec state emptyInput emptySubs
              di = DutyInfo { duty_name = d, duty_tagged = te, duty_violated = or vs }
          in (state0, as, di:ds)
        Act _  -> let (state1,as') = enables_acts spec state0 te
                  in (state1, as' ++ as, ds)
        Event _ -> (state0, as, ds)
  in foldl op (state, [], []) (M.assocs (contents state))

-- given a component, check whether it is in the given state and whether that component enables any acts 
enables_acts :: Spec -> State -> Tagged -> (State, [TransInfo])
enables_acts spec state te = runSubs (instantiate_trans False te) spec state emptyInput emptySubs

enable_act :: Spec -> State -> [Var] -> Term -> (State, [TransInfo])
enable_act spec state xs t = fmap concat $ runSubs creater spec state emptyInput emptySubs
  where creater = foreach xs (whenTagged (eval t) (instantiate_trans False))

fire_act :: Spec -> State -> TransInfo -> State
fire_act spec state act = 
  do_creates (trans_creates act) (do_terminates (trans_terminates act) state)
  where 
        -- assumes the decomposition will result in consistency
        do_creates :: S.Set Tagged -> State -> State
        do_creates = flip (S.foldr create)

        -- likewise
        do_terminates :: S.Set Tagged -> State -> State
        do_terminates = flip (S.foldr terminate)

-- ### instantiation mechanisms

data TestResult = TestResult { 
                    success             :: Bool
                  , errors              :: [String]
                  , alternative_actions :: [String]
                  , present_powers      :: IM.IntMap [TaggedJSON] 
                  , present_duties      :: IM.IntMap [(TaggedJSON, Bool)]
                  , violated_invariants :: IM.IntMap [DomId]
                  , violated_duties     :: IM.IntMap [TaggedJSON]
                  , exec_actions        :: IM.IntMap (Maybe TransInfo)
                  -- , reached_states      :: IM.IntMap State
                  , current_state       :: Int
                  } deriving (Generic) 

instance ToJSON TestResult where

empty_test_result :: Spec -> State -> [TransInfo] -> [DutyInfo] -> [DomId] -> TestResult
empty_test_result spec state powers duties breaches = 
  test_step' Nothing state powers duties breaches $
  -- TestResult True [] [] IM.empty IM.empty IM.empty IM.empty IM.empty IM.empty (-1)
  TestResult True [] [] IM.empty IM.empty IM.empty IM.empty IM.empty (-1)

test_step :: TransInfo -> State -> [TransInfo] -> [DutyInfo] -> [DomId] -> TestResult -> TestResult 
test_step a = test_step' (Just a)
test_step' maction state powers duties breaches tr = 
  tr { exec_actions   = (if isNothing maction then id else IM.insert k maction) (exec_actions tr)
     -- , reached_states = IM.insert k state (reached_states tr)
     , present_powers = IM.insert k (map (TaggedJSON . trans_tagged) powers) (present_powers tr)
     , present_duties = IM.insert k (map duty_res duties) (present_duties tr)
     , violated_duties = IM.insert k (map TaggedJSON viol_duties) (violated_duties tr)
     , violated_invariants = IM.insert k breaches (violated_invariants tr) 
     , errors = (errors tr) ++ add_errors
     , current_state = k }
 where k | isNothing maction = 0
         | otherwise         = length (exec_actions tr) + 1
       duty_res d = (TaggedJSON (duty_tagged d), duty_violated d)
       viol_duties = map duty_tagged (filter duty_violated duties) 
       add_errors = map (toDutyErr k . show_component) viol_duties ++
                    map (toInvErr k) breaches
        where toDutyErr k d = "Duty violated at step " ++ show k ++ "\n    " ++ d 
              toInvErr k i  = "Invariant violated at step " ++ show k ++ "\n    " ++ i

test_repeat_step :: TestResult -> TestResult
test_repeat_step tr = 
  tr { exec_actions = IM.insert k Nothing (exec_actions tr)
     -- , reached_states = IM.insert k (reached_states tr IM.! (k-1)) (reached_states tr)
     , present_powers = IM.insert k (present_powers tr IM.! (k-1)) (present_powers tr)
     , present_duties = IM.insert k (present_duties tr IM.! (k-1)) (present_duties tr)
     , violated_duties = IM.insert k (violated_duties tr IM.! (k-1)) (violated_duties tr)
     , violated_invariants = IM.insert k (violated_invariants tr IM.! (k-1)) (violated_invariants tr)
     , current_state = k
     }
  where k = length (exec_actions tr) + 1

test_err :: String -> TestResult -> TestResult
test_err str tr = tr {errors = (errors tr) ++ [str]}

test_fail :: TestResult -> TestResult
test_fail tr = tr { success = False }

test_ambig :: String -> [Either QueryInfo TransInfo] -> TestResult -> TestResult
test_ambig str acts tr = (test_err str tr){ alternative_actions = map (either (const "<query>") show_action) acts} 
