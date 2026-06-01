import GameHoppingInLean.Misc.SimpAttrs
import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.OracleReductions

attribute [GameHoppingSimplifyPMF]
  PMF.map_id

attribute [OracleReductionSimps]
  OracleReduction.apply
  OracleComp.instMonadLiftOracleQuery._aux_1
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
       try simp [$defs,*]
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
       try simp [OracleReduction.apply, $defs,*]
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
