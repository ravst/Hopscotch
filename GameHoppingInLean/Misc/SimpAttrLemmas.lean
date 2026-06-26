import GameHoppingInLean.Misc.SimpAttrs
import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.Normalization.PMF.Simprocs
import GameHoppingInLean.Normalization.PMF.Lemmas
import GameHoppingInLean.Normalization.BitVec.Simprocs
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.PMFLiftOrder
import GameHoppingInLean.IndistinguishabilityDef
import Lean

open Lean Elab Tactic


/-! ### Reduction lemmas for the `goodDoubleAction` state-commutation step

These small lemmas push `simulateQ`/`StateT.run` through the various query heads while
keeping `simulateQ` itself folded, so that the induction hypotheses of
`goodDoubleAction_step`/`goodDoubleAction_core` still match.  They are bundled into the
`goodDoubleActionSimps` simp set together with the relevant unfolding lemmas. -/

/-- `liftM` into the same monad is the identity. -/
@[goodDoubleActionSimps] lemma liftM_self {m : Type u → Type v} [Monad m] {α} (x : m α) :
    (liftM x : m α) = x := rfl

/-- Push `simulateQ` through a `FreeM.roll` node. -/
lemma simulateQ_roll {ι} {spec : OracleSpec ι} (t : spec.Domain) {m} {β}
    [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (k : spec.Range t → OracleComp spec β) :
    simulateQ impl (PFunctor.FreeM.roll t k) = impl t >>= fun u => simulateQ impl (k u) := by
  unfold simulateQ
  rw [PFunctor.FreeM.mapM.eq_def]; rfl


/-- Running `StateT.get`. -/
@[goodDoubleActionSimps] lemma stateT_run_get {m} [Monad m] {σ} (s : σ) :
    (StateT.get s : m (σ × σ)) = pure (s, s) := rfl

/-- Running `f <$> StateT.get`. -/
@[goodDoubleActionSimps] lemma stateT_run_map_get {σ α} (f : σ → α) (s : σ) :
    ((f <$> StateT.get) s : PMF (α × σ)) = pure (f s, s) := by
  change PMF.map (fun p : σ × σ => (f p.1, p.2)) (PMF.pure (s, s)) =
    PMF.pure (f s, s)
  exact PMF.pure_map (fun p : σ × σ => (f p.1, p.2)) (s, s)

/-- Running `StateT.set`. -/
@[goodDoubleActionSimps] lemma stateT_run_set {m} [Monad m] {σ} (st s : σ) :
    (StateT.set st) s = (pure (PUnit.unit, st) : m (PUnit × σ)) := rfl

@[simp]
lemma simulateQ_pure2 (x : α) {ι} {spec : OracleSpec ι} {r : Type u → Type*}
    [Monad r] (impl : QueryImpl spec r) :
    simulateQ impl (PFunctor.FreeM.pure x : OracleComp spec α) = pure x := rfl


attribute [GameHoppingSimplifyPMF]
  PMF.monad_bind_eq_bind
  PMF.monad_pure_eq_pure
  PMF.monad_map_eq_map
  PMF.map_id
  PMF.bind_const

attribute [OracleReductionSimps]
  OracleReduction.apply
  simulateQ_roll
  simulateQ_bind
  simulateQ_pure
  simulateQ_pure2
  OracleReduction.query
  liftM
  monadLift
  MonadLift.monadLift
  OracleReduction.liftWithPMFAndState
  OracleSpec.query
  OracleQuery.input_query
  OracleQuery.cont_query
  id_map
  addPMFtoImpl
  ro_seq_fixed
-- OracleComp.instMonadLiftOracleQuery._aux_1
-- PFunctor.FreeM.mapM


attribute [correctAbstractionDiagSimps]
  mapInputState
  mapOutputState
  mapSecond
  bindInputState
  bindOutputState
  bindSecond

attribute [StateTSimps]
  StateT.lift
  StateT.pure
  StateT.run
  StateT.get
  _root_.modify
  StateT.run_bind
  StateT.run_lift
  StateT.run_pure
  RState.run_liftM
  pure_bind
  bind_pure
  PMF.pure_bind
  PMF.map_bind
  PMF.bind_map
  PMF.bind_bind
  OracleReduction.statefulOracleComp_pure
  OracleReduction.statefulOracleComp_bind
  -- RState.modify
  -- MonadState.get
  -- getThe
  -- MonadStateOf.get

attribute [goodDoubleActionSimps]
  OracleReduction.liftWithPMFAndState
  OracleReduction.defaultImpl
  addPMFtoImpl
  OracleComp.queryBind
  OracleQuery.query
  OracleQuery.cont
  id_eq
  Function.comp_def
  Prod.mk.eta


/-- Solve a correct-abstraction query diagram by extensionality and standard unfolding. -/
syntax "solveCorrectAbstractionDiag" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
          | `(tactic| solveCorrectAbstractionDiag [$simps,*]) =>
            `(tactic|
              (ext1 st;
               try let ⟨st1, st₂⟩ := st;
               try simp [game_hopping_unfold];
               try simp [OracleReductionSimps];
               try simp [correctAbstractionDiagSimps];
               try simp [StateTSimps];
               try simp [RStateSimplifier];
               try simp [OracleReductionSimps];
               try simp [correctAbstractionDiagSimps];
               try unfold mapSecond
               try unfold bindSecond
               try simp [game_hopping_unfold]
               try simp [GameHoppingSimplifyPMF, RStateSimplifier, $simps,*];
               try rfl;
               try split_ifs
               all_goals try simp_all [GameHoppingSimplifyPMF, RStateSimplifier, $simps,*]
               all_goals try rfl))

/--
Basic correct-abstraction query-diagram setup.  This unfolds the oracle/state plumbing and
then stops after the first `rfl` attempt, leaving PMF normalization and branch splitting to
the caller.
-/
syntax "solveCorrectAbstractionDiagBasic" : tactic

macro_rules
          | `(tactic| solveCorrectAbstractionDiagBasic) =>
            `(tactic|
              (ext1 st;
               try let ⟨st1, st₂⟩ := st;
               try simp [game_hopping_unfold];
               try simp [OracleReductionSimps];
               try simp [correctAbstractionDiagSimps];
               try simp [StateTSimps];
               try simp [RStateSimplifier];
               try simp [OracleReductionSimps];
               try simp [correctAbstractionDiagSimps];
               try unfold mapSecond
               try unfold bindSecond
               try simp [game_hopping_unfold]
               try rfl))

/-- Solve a correct-abstraction initialization diagram by standard unfolding. -/
syntax "solveCorrectAbstractionInit" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
          | `(tactic| solveCorrectAbstractionInit [$simps,*]) =>
            `(tactic|
              (try simp [OracleReduction.apply, game_hopping_unfold];
               try simp [OracleReductionSimps];
               try simp [GameHoppingSimplifyPMF, RStateSimplifier, $simps,*];
               try rfl))

/-- Solve both initialization and query branches of a correct-abstraction proof. -/
syntax "solveCorrectAbstraction" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| solveCorrectAbstraction [$simps,*]) =>
    `(tactic|
      (constructor
       <;> try solveCorrectAbstractionInit [$simps,*]
       try swap
       try
         (intro query
          cases query <;> try solveCorrectAbstractionDiag [$simps,*])))

/--
Basic version of `solveCorrectAbstraction` whose query diagrams stop before PMF
normalization.
-/
syntax "solveCorrectAbstractionBasic" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| solveCorrectAbstractionBasic [$simps,*]) =>
    `(tactic|
      (constructor
       <;> try solveCorrectAbstractionInit [$simps,*]
       try swap
       try
         (intro query
          cases query <;> try solveCorrectAbstractionDiagBasic)))

/--
Strict version used by tactic search: unlike `solveCorrectAbstraction`, it must close both
branches, so failed attempts can be reliably backtracked.
-/
syntax "solveCorrectAbstraction!" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| solveCorrectAbstraction! [$simps,*]) =>
    `(tactic|
      (constructor
       · solveCorrectAbstractionInit [$simps,*]
       · -- try solveCorrectAbstractionInit [$simps,*]
         intro query
         cases query <;> solveCorrectAbstractionDiag [$simps,*]))

private def tryCloseCurrentGoal (tac : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try
    evalTactic tac
    if (← getGoals).isEmpty then
      return true
    else
      restoreState s
      return false
  catch _ =>
    restoreState s
    return false

/--
Try common observational-equivalence abstraction shapes.  Each attempt must close
the current goal completely; failed or partial attempts restore the original goal.
-/
syntax "solve_obs_eq" : tactic
syntax "solve_obs_eq" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| solve_obs_eq) => `(tactic| solve_obs_eq [])

elab_rules : tactic
  | `(tactic| solve_obs_eq [$simps,*]) => do
      let attempts ← pure #[
        ← `(tactic|
          (apply correctAbstractionImpliesObsEq _ _ (fun x => ((), x))
           solveCorrectAbstraction! [$simps,*])),
        ← `(tactic|
          (apply correctAbstractionImpliesObsEq _ _ (fun x => (x, ()))
           solveCorrectAbstraction! [$simps,*])),
        ← `(tactic|
          (refine correctAbstractionImpliesObsEq _ _ (fun x => x) ?_
           solveCorrectAbstraction! [$simps,*])),
        ← `(tactic|
          (apply correctAbstractionImpliesObsEq _ _ (fun _ => ())
           solveCorrectAbstraction! [$simps,*])),
        ← `(tactic|
          (symm
           apply correctAbstractionImpliesObsEq _ _ (fun x => ((), x))
           solveCorrectAbstraction! [$simps,*])),
        ← `(tactic|
          (symm
           apply correctAbstractionImpliesObsEq _ _ (fun x => (x, ()))
           solveCorrectAbstraction! [$simps,*]))
      ]
      for attempt in attempts do
        if ← tryCloseCurrentGoal attempt then
          return
      throwError "solve_obs_eq failed; please provide an abstraction function manually"
