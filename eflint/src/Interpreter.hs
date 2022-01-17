{-# LANGUAGE RecordWildCards, LambdaCase #-}

module Interpreter (Config(..), Program(..), interpreter, initialConfig, rest_disabled, rest_enabled, get_transition, context2config, make_initial_state
                   ,OutputWriter, Output(..), getOutput
                   ,errors, violations, ex_triggers, query_ress, missing_inputs
                   ,convert_programs, collapse_programs) where

import Eval
import Spec
import Saturation
import StaticEval (compile_phrase, runStatic) 
import State

import Control.Monad (forM, when)
import Control.Monad.Writer (Writer, tell, runWriter)
import Control.Applicative (empty)

import qualified Data.Map as M
import qualified Data.Set as S

data Program = Program Phrase 
             | PSeq Program Program
             | ProgramSkip
             deriving (Eq, Show)

data Config = Config {
        cfg_spec          :: Spec
      , cfg_state         :: State 
      , rest_transitions  :: [Transition] -- (label * enabled?) -- replaced
      , rest_duties       :: [Tagged] -- replaced after ever step
      }
      deriving (Eq)

data Output = ErrorVal Error
            | ExecutedTransition TransInfo 
            | Violation Violation
            | QueryRes QueryRes -- whether query succeed or not
            deriving (Eq, Show, Read)

convert_programs :: [Phrase] -> [Program]
convert_programs phrases = map Program phrases

collapse_programs :: [Program] -> Program
collapse_programs [] = ProgramSkip
collapse_programs programs = (foldr1 PSeq programs)

interpreter :: (InputMap, Program) -> Config -> OutputWriter (Maybe Config)
interpreter (inpm, Program p) cfg = case runStatic (compile_phrase p) (ctx_spec ctx) of
    Left err  -> tell [ErrorVal (CompilationError (unlines err))] >> return Nothing 
    Right (spec', p') -> fmap context2config <$> sem_phrase p' inpm 
                          (ctx{ctx_spec = spec', ctx_state = rebase_and_sat spec' (ctx_state ctx)}) 
  where ctx = config2context cfg
interpreter (inpm, PSeq p1 p2) cfg = (interpreter (inpm,p1) cfg) >>= interpreter (inpm,p2) . maybe cfg id
interpreter (inpm, ProgramSkip) cfg = return Nothing

initialConfig Nothing = context2config (emptyContext emptySpec)
initialConfig (Just (spec,state)) = context2config $
  (emptyContext spec) { ctx_state = state }

context2config :: Context -> Config
context2config ctx = Config {
    cfg_spec    = ctx_spec ctx
  , cfg_state   = ctx_state ctx
  , rest_transitions = ctx_transitions ctx
  , rest_duties      = ctx_duties ctx
  }

config2context :: Config -> Context
config2context cfg = Context {
    ctx_spec = cfg_spec cfg
  , ctx_state = cfg_state cfg
  , ctx_transitions = []
  , ctx_duties = []
  }

rest_enabled = map fst . filter snd . map get_transition . rest_transitions
rest_disabled = map fst . filter (not . snd) . map get_transition . rest_transitions

get_transition :: Transition -> (Tagged, Bool)
get_transition transition = (tagged transition, exist transition)

ex_triggers :: [Output] -> [TransInfo]
ex_triggers = concatMap op
 where op (ExecutedTransition out) = [out]
       op _ = []

violations :: [Output] -> [Violation]
violations = concatMap op
 where op (Violation v) = [v]
       op _ = []

errors :: [Output] -> [Error]
errors = concatMap op
  where op (ErrorVal err) = [err]
        op _ = []

query_ress :: [Output] -> [QueryRes]
query_ress = concatMap op
  where op (QueryRes b) = [b]
        op _ = []

missing_inputs :: [Output] -> [Tagged]
missing_inputs = S.toList . S.fromList . concatMap op
  where op (ErrorVal (RuntimeError (MissingInput te))) = [te]
        op _ = []

type OutputWriter = Writer [Output]

getOutput :: OutputWriter a -> (a,[Output])
getOutput = runWriter

error_or_process :: M_Subs a -> Spec -> State -> InputMap -> ([a] -> OutputWriter (Maybe Context)) -> OutputWriter (Maybe Context)
error_or_process ma spec state inpm fa = case runSubs ma spec state inpm emptySubs of
  Left err  -> tell [ErrorVal $ RuntimeError err] >> return Nothing
  Right as  -> fa as

sem_phrase :: CPhrase -> InputMap -> Context -> OutputWriter (Maybe Context)
sem_phrase p inpm c0 = case p of
  CPSkip   -> return Nothing
  CPOnlyDecls -> no_effect 
  CQuery t -> error_or_process (eval t) spec state inpm $ \vs -> do  
                 let queryRes | all (== (ResBool True)) vs = QuerySuccess
                              | otherwise                  = QueryFailure
                 tell [QueryRes queryRes] >> no_effect
  CCreate vs t    -> single_effect (CAll vs t)
  CTerminate vs t -> single_effect (TAll vs t)
  CObfuscate vs t -> single_effect (OAll vs t)
  CDo te          -> error_or_process (trigger_or_fail te) spec state inpm (consider_transinfos . (:[]))
  CTrigger vs t -> let m_subs = do  tes <- Eval.foreach vs (whenTagged (eval t) return)
                                    forM tes trigger_or_fail 
                     in error_or_process m_subs spec state inpm consider_transinfos
  CPDir dir -> return_context emptyStore [dir] 
  CSeq p q -> sem_phrase p inpm c0 >>= (sem_phrase q inpm . maybe c0 id)
  where spec = ctx_spec c0
        state = ctx_state c0

        return_context :: Store -> [CDirective] -> OutputWriter (Maybe Context)
        return_context ass dirs = do  
          let duties = [ te | te@(v,d) <- (state_input_holds state' inpm)
                            , Duty _ <- maybe [] (:[]) (fmap kind (find_decl spec' d)) ]
          error_or_process (find_duty_violations duties) spec' state' inpm $ \d_viols -> 
            error_or_process (find_inv_violations (S.toList $ invariants spec')) spec' state' inpm $ \i_viols -> do
              tell (map Violation (concat d_viols ++ concat i_viols)) 
              error_or_process find_transitions spec' state' inpm $ \tss ->  
                return $ Just $ c0
                  { ctx_state = state'
                  , ctx_spec = spec'
                  , ctx_transitions = concat tss
                  , ctx_duties = duties 
                  }
          where state' = rebase_and_sat spec (make_assignments ass state)
                spec'  = process_directives dirs spec

        no_effect :: OutputWriter (Maybe Context)
        no_effect = return_context emptyStore []

        single_effect :: Effect -> OutputWriter (Maybe Context)
        single_effect eff =
          error_or_process (eval_effect eff) spec state inpm $ \stores ->
            return_context (M.unions stores) {- always just one store-} []

        trigger_or_fail :: Tagged -> M_Subs (Either Tagged TransInfo)
        trigger_or_fail te@(_,d) | triggerable spec d = Right <$> instantiate_trans te
                                 | otherwise          = return $ Left te

        consider_transinfos infos = case infos of
          [[Left te]]    -> tell [ErrorVal (NotTriggerable te)] >> no_effect
          [[Right info]] -> report_on_trans info
          _              -> tell [ErrorVal NonDeterministicTransition] >> no_effect 


        report_on_trans :: TransInfo -> OutputWriter (Maybe Context)
        report_on_trans info = do
          tell [ExecutedTransition info]
          when (trans_is_action info && trans_forced info) 
            (tell [Violation (TriggerViolation info)])
          return_context (trans_assignments info) [] 

find_inv_violations :: [DomId] -> M_Subs [Violation]
find_inv_violations ds = do 
  spec <- get_spec 
  forM ds $ \d -> do
    let term = Exists [Var d ""] (Present (Ref (Var d "")))
    ignoreMissingInput (checkFalse (eval term))
    return (InvariantViolation d)

find_duty_violations :: [Tagged] -> M_Subs [Violation]
find_duty_violations tes = do 
  spec <- get_spec 
  forM tes $ \te@(_,d) -> do
    ignoreMissingInput (eval_violation_condition te (find_violation_cond spec d)) >>= \case 
      True  -> return (DutyViolation te)
      False -> empty 
 
find_transitions :: M_Subs [Transition]
find_transitions = do
  spec <- get_spec 
  concat <$> mapM gen_trans (trigger_decls spec)
  where gen_trans (d,_) = results $ ignoreMissingInput $ do
          tagged <- every_possible_subs (no_decoration d)
          exist  <- is_in_virtual_state tagged
          return Transition{..}

every_possible_subs :: Var -> M_Subs Tagged
every_possible_subs x = do
    spec <- get_spec
    let d = remove_decoration spec x
    (dom, _) <- get_dom d
    if enumerable spec dom then generate_instances d
                           else every_available_subs d
 where generate_instances d = do
          (dom, dom_filter) <- get_dom d
          e <- instantiate_domain d dom
          let bindings = case (dom,e) of (Products xs, Product args) -> M.fromList (zip xs args)
                                         _ -> M.singleton (no_decoration d) (e,d) 
          modify_subs (`subsUnion` bindings) (checkTrue (eval dom_filter))
          return (e,d)
       every_available_subs d = do
          (dom, dom_filter) <- get_dom d
          case dom of
            Products xs -> do
              args <- sequence (map every_possible_subs xs)
              modify_subs (`subsUnion` (M.fromList (zip xs args))) (checkTrue (eval dom_filter))
              return (Product args, d)
            _ -> do
              state <- get_state
              input <- get_input
              nd $  [ te | te@(v,d') <- state_input_holds state input, d' == d ]

make_initial_state :: Spec -> Initialiser -> State
make_initial_state spec inits = do
  case runSubs (store_unions <$> mapM eval_effect inits) spec emptyState emptyInput emptySubs of
    Left err -> error (print_runtime_error err)
    Right res -> case res of 
      []    -> error "failed to initialise state"
      [sto] -> rebase_and_sat spec (make_assignments sto emptyState)
      _     -> error "non-deterministic state initialisation"          
