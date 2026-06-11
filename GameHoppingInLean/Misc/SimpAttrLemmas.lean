import GameHoppingInLean.Misc.SimpAttrs
import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.OracleReductions
import Lean

open Lean Elab Tactic

attribute [GameHoppingSimplifyPMF]
  PMF.map_id

attribute [OracleReductionSimps]
  OracleReduction.apply
  -- OracleComp.instMonadLiftOracleQuery._aux_1
  simulateQ
  OracleReduction.query
  PFunctor.FreeM.mapM
  liftM
  monadLift
  MonadLift.monadLift
  OracleReduction.liftWithPMFAndState

attribute [correctAbstractionDiagSimps]
  mapInputState
  mapOutputState

attribute [StateTSimps]
  StateT.lift
  StateT.run
  StateT.get
  _root_.modify

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
       try simp only [GameHoppingSimplifyPMF]
       try simp
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
           solveCorrectAbstraction [])),
        ← `(tactic|
          (apply correctAbstractionImpliesObsEq _ _ (fun x => x)
           solveCorrectAbstraction [])),
        ← `(tactic|
          (symm
           apply correctAbstractionImpliesObsEq _ _ (fun x => ((), x))
           solveCorrectAbstraction []))
      ]
      for attempt in attempts do
        if ← tryCloseCurrentGoal attempt then
          return
      throwError "solve_obs_eq failed; please provide an abstraction function manually"
