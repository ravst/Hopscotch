import GameHoppingInLean.Misc.SimpAttrs
import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.Misc.PMFLemmas
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.PMFLiftOrder
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
  simp [StateT.run, StateT.get, StateT.map, map_eq_pure_bind]

/-- Running `StateT.set`. -/
@[goodDoubleActionSimps] lemma stateT_run_set {m} [Monad m] {σ} (st s : σ) :
    (StateT.set st) s = (pure (PUnit.unit, st) : m (PUnit × σ)) := rfl

@[simp]
lemma simulateQ_pure2 (x : α) {ι} {spec : OracleSpec ι} {r : Type u → Type*}
    [Monad r] (impl : QueryImpl spec r) :
    simulateQ impl (PFunctor.FreeM.pure x : OracleComp spec α) = pure x := rfl


attribute [GameHoppingSimplifyPMF]
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
-- OracleComp.instMonadLiftOracleQuery._aux_1
-- PFunctor.FreeM.mapM


attribute [correctAbstractionDiagSimps]
  mapInputState
  mapOutputState

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
  | `(tactic| solveCorrectAbstractionDiag [$defs,*]) =>
    `(tactic|
      (ext1 st
       try simp [game_hopping_unfold, $defs,*]
       try simp [OracleReductionSimps]
       try simp [correctAbstractionDiagSimps]
       try simp [StateTSimps]
       try simp [OracleReductionSimps]
       try simp only [GameHoppingSimplifyPMF]
       try simp
       try simp only [GameHoppingSimplifyPMF]
       try rfl))

/-- Solve a correct-abstraction initialization diagram by standard unfolding. -/
syntax "solveCorrectAbstractionInit" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| solveCorrectAbstractionInit [$defs,*]) =>
    `(tactic|
      (
       try simp [OracleReduction.apply, game_hopping_unfold, $defs,*]
       try simp [OracleReductionSimps]
       try simp only [GameHoppingSimplifyPMF]
       try rfl))

/-- Solve both initialization and query branches of a correct-abstraction proof. -/
syntax "solveCorrectAbstraction" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| solveCorrectAbstraction [$defs,*]) =>
    `(tactic|
      (constructor
       <;> try solveCorrectAbstractionInit [$defs,*]
       try swap
       try
         (intro query
          cases query <;> try solveCorrectAbstractionDiag [$defs,*])))

/--
Strict version used by tactic search: unlike `solveCorrectAbstraction`, it must close both
branches, so failed attempts can be reliably backtracked.
-/
syntax "solveCorrectAbstraction!" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| solveCorrectAbstraction! [$defs,*]) =>
    `(tactic|
      (constructor
       · solveCorrectAbstractionInit [$defs,*]
       · intro query
         cases query <;> solveCorrectAbstractionDiag [$defs,*]))

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

elab_rules : tactic
  | `(tactic| solve_obs_eq) => do
      let attempts ← pure #[
        ← `(tactic|
          (apply correctAbstractionImpliesObsEq _ _ (fun x => ((), x))
           solveCorrectAbstraction! [])),
        ← `(tactic|
          (apply correctAbstractionImpliesObsEq _ _ (fun x => (x, ()))
           solveCorrectAbstraction! [])),
        ← `(tactic|
          (apply correctAbstractionImpliesObsEq _ _ (fun x => x)
           solveCorrectAbstraction! [])),
        ← `(tactic|
          (apply correctAbstractionImpliesObsEq _ _ (fun _ => ())
           solveCorrectAbstraction! [])),
        ← `(tactic|
          (symm
           apply correctAbstractionImpliesObsEq _ _ (fun x => ((), x))
           solveCorrectAbstraction! [])),
        ← `(tactic|
          (symm
           apply correctAbstractionImpliesObsEq _ _ (fun x => (x, ()))
           solveCorrectAbstraction! []))
      ]
      for attempt in attempts do
        if ← tryCloseCurrentGoal attempt then
          return
      throwError "solve_obs_eq failed; please provide an abstraction function manually"
