import GameHoppingInLean.Indistinguishability.Def
import GameHoppingInLean.Tactic.SimpAttrLemmas
import Lean

open Lean Elab Tactic Meta

/-- Turn an observational-equivalence proof goal into an indistinguishability proof. -/
syntax "obs_eq" : tactic

macro_rules
  | `(tactic| obs_eq) => `(tactic| apply Indistinguishable.of_ObsEq)

/--
Turn an indistinguishability goal into an observational-equivalence goal, prove it with
the supplied abstraction map, and discharge the generated correctness conditions.

Use `by_abstraction ← f` for the symmetric direction.
-/
syntax (name := byAbstractionForward) "by_abstraction" term : tactic
syntax (name := byAbstractionSymm) "by_abstraction" "←" term : tactic
syntax (name := byRandAbstractionForward) "by_rand_abstraction" term : tactic
syntax (name := byRandAbstractionSymm) "by_rand_abstraction" "←" term : tactic
syntax (name := obsEqByAbstractionForward) "obs_eq_by_abstraction" term : tactic
syntax (name := obsEqByAbstractionSymm) "obs_eq_by_abstraction" "←" term : tactic
syntax (name := obsEqByRandAbstractionForward) "obs_eq_by_rand_abstraction" term : tactic
syntax (name := obsEqByRandAbstractionSymm) "obs_eq_by_rand_abstraction" "←" term : tactic
syntax (name := byAbstractionBasicForward) "by_abstraction_basic" term : tactic
syntax (name := byAbstractionBasicSymm) "by_abstraction_basic" "←" term : tactic
syntax (name := byRandAbstractionBasicForward) "by_rand_abstraction_basic" term : tactic
syntax (name := byRandAbstractionBasicSymm) "by_rand_abstraction_basic" "←" term : tactic

macro_rules (kind := byAbstractionForward)
  | `(tactic| by_abstraction $f:term) =>
      `(tactic|
        (obs_eq
         refine correctAbstractionImpliesObsEq _ _ $f ?_
         solveCorrectAbstraction[]))

macro_rules (kind := byAbstractionSymm)
  | `(tactic| by_abstraction ← $f:term) =>
      `(tactic|
        (obs_eq
         symm
         refine correctAbstractionImpliesObsEq _ _ $f ?_
         solveCorrectAbstraction[]))

macro_rules (kind := byRandAbstractionForward)
  | `(tactic| by_rand_abstraction $f:term) =>
      `(tactic|
        (obs_eq
         refine correctAbstractionBindImpliesObsEq _ _ $f ?_
         solveCorrectAbstraction[]))

macro_rules (kind := byRandAbstractionSymm)
  | `(tactic| by_rand_abstraction ← $f:term) =>
      `(tactic|
        (obs_eq
         symm
         refine correctAbstractionBindImpliesObsEq _ _ $f ?_
         solveCorrectAbstraction[]))

macro_rules (kind := obsEqByAbstractionForward)
  | `(tactic| obs_eq_by_abstraction $f:term) =>
      `(tactic|
        (refine correctAbstractionImpliesObsEq _ _ $f ?_
         solveCorrectAbstraction[]))

macro_rules (kind := obsEqByAbstractionSymm)
  | `(tactic| obs_eq_by_abstraction ← $f:term) =>
      `(tactic|
        (symm
         refine correctAbstractionImpliesObsEq _ _ $f ?_
         solveCorrectAbstraction[]))

macro_rules (kind := obsEqByRandAbstractionForward)
  | `(tactic| obs_eq_by_rand_abstraction $f:term) =>
      `(tactic|
        (refine correctAbstractionBindImpliesObsEq _ _ $f ?_
         solveCorrectAbstraction[]))

macro_rules (kind := obsEqByRandAbstractionSymm)
  | `(tactic| obs_eq_by_rand_abstraction ← $f:term) =>
      `(tactic|
        (symm
         refine correctAbstractionBindImpliesObsEq _ _ $f ?_
         solveCorrectAbstraction[]))

macro_rules (kind := byAbstractionBasicForward)
  | `(tactic| by_abstraction_basic $f:term) =>
      `(tactic|
        (obs_eq
         refine correctAbstractionImpliesObsEq _ _ $f ?_
         solveCorrectAbstractionBasic[]))

macro_rules (kind := byAbstractionBasicSymm)
  | `(tactic| by_abstraction_basic ← $f:term) =>
      `(tactic|
        (obs_eq
         symm
         refine correctAbstractionImpliesObsEq _ _ $f ?_
         solveCorrectAbstractionBasic[]))

macro_rules (kind := byRandAbstractionBasicForward)
  | `(tactic| by_rand_abstraction_basic $f:term) =>
      `(tactic|
        (obs_eq
         refine correctAbstractionBindImpliesObsEq _ _ $f ?_
         solveCorrectAbstractionBasic[]))

macro_rules (kind := byRandAbstractionBasicSymm)
  | `(tactic| by_rand_abstraction_basic ← $f:term) =>
      `(tactic|
        (obs_eq
         symm
         refine correctAbstractionBindImpliesObsEq _ _ $f ?_
         solveCorrectAbstractionBasic[]))

private partial def gameHoppingIndexCandidates (idxType : Expr) : TermElabM (Array Expr) := do
  let idxTypeWhnf ← withTransparency .all <| whnf idxType
  match idxTypeWhnf.getAppFnArgs with
    | (``Unit, #[]) =>
        pure #[mkConst ``Unit.unit idxTypeWhnf.getAppFn.constLevels!]
    | (``PUnit, #[]) =>
        pure #[mkConst ``PUnit.unit idxTypeWhnf.getAppFn.constLevels!]
    | (``Empty, #[]) =>
        pure #[]
    | (``PEmpty, #[]) =>
        pure #[]
    | (``Bool, #[]) =>
        pure #[mkConst ``Bool.false, mkConst ``Bool.true]
    | (``Sum, #[α, β]) =>
        let lefts ← gameHoppingIndexCandidates α
        let rights ← gameHoppingIndexCandidates β
        let lefts ← lefts.mapM fun i =>
          mkAppOptM ``Sum.inl #[some α, some β, some i]
        let rights ← rights.mapM fun i =>
          mkAppOptM ``Sum.inr #[some α, some β, some i]
        pure (lefts ++ rights)
    | (``Prod, #[α, β]) =>
        let lefts ← gameHoppingIndexCandidates α
        let rights ← gameHoppingIndexCandidates β
        let mut candidates := #[]
        for i in lefts do
          for j in rights do
            candidates := candidates.push <| ←
              mkAppOptM ``Prod.mk #[some α, some β, some i, some j]
        pure candidates
    | _ =>
        try
          let inhabitedType ← mkAppM ``Inhabited #[idxType]
          match ← trySynthInstance inhabitedType with
          | .some _ => pure #[← mkAppM ``default #[idxType]]
          | .none => pure #[]
          | .undef => pure #[]
        catch _ =>
          pure #[]

private def closeGameHoppingAssumptionGoal : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let proof ← goal.withContext <| runTermElab do
    let target ← whnf target
    unless target.getAppFn.constName? == some ``IndistinguishableI do
      throwError "game_hopping_reduce_assumption expected an IndistinguishableI goal"
    let args := target.getAppArgs
    if h : 2 < args.size then
      let Assumptions := args[1]
      let q_b := args[2]
      let assumptionsType ← withTransparency .all <| whnf (← inferType Assumptions)
      let idxType := (assumptionsType.getAppArgs)[0]!
      for idx in ← gameHoppingIndexCandidates idxType do
        let proof ← withTransparency .all <|
          mkAppOptM ``IndistinguishableI.assumption #[none, some Assumptions, some q_b, some idx]
        if ← withTransparency .all <| isDefEq (← inferType proof) target then
          return proof
      throwError "game_hopping_reduce_assumption could not find a matching assumption index"
    else
      throwError "game_hopping_reduce_assumption expected an IndistinguishableI goal"
  goal.assign proof
  replaceMainGoal []

/--
Discharge goals of the form `r ◇ ro₁ ≈ r ◇ ro₂` when `ro₁` and `ro₂`
are an available indistinguishability assumption, in either direction.
-/
elab "game_hopping_reduce_assumption" : tactic => do
  let s ← saveState
  try
    evalTactic (← `(tactic| refine IndistinguishableI.reduction _ _ ?_))
    closeGameHoppingAssumptionGoal
  catch _ =>
    restoreState s
    evalTactic (← `(tactic| refine IndistinguishableI.reduction _ _ ?_))
    evalTactic (← `(tactic| apply IndistinguishableI.symm))
    closeGameHoppingAssumptionGoal

private def checkGameHoppingEndpoints (first last : TSyntax `term) : TacticM Unit := do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  goal.withContext <| runTermElab do
    let target ← whnf target
    unless target.getAppFn.constName? == some ``IndistinguishableI do
      throwError "game_hopping expected an IndistinguishableI goal"
    let args := target.getAppArgs
    if h : 6 < args.size then
      let roStart := args[5]
      let roEnd := args[6]
      let firstExpr ← Term.elabTermEnsuringType first (← inferType roStart)
      unless ← withTransparency .all <| isDefEq firstExpr roStart do
        throwError "game_hopping first oracle does not match the current goal"
      let lastExpr ← Term.elabTermEnsuringType last (← inferType roEnd)
      unless ← withTransparency .all <| isDefEq lastExpr roEnd do
        throwError "game_hopping final oracle does not match the current goal"
    else
      throwError "game_hopping expected an IndistinguishableI goal"

/--
`game_hopping [G₀, H₁, ..., Gₙ]` proves an `IndistinguishableI` goal by repeated
transitivity through the listed chain. The first and final oracles must match the
current goal, and the tactic creates one goal for each adjacent pair:
`G₀ ≈ H₁`, `H₁ ≈ H₂`, ..., `Hₖ ≈ Gₙ`.
-/
syntax "game_hopping" " [" term,* "]" : tactic
syntax "game_hopping" " [" term,* "]" " using " Lean.Parser.Tactic.simpLemma,* : tactic

syntax "game_hopping_basic" " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| game_hopping_basic [$chain,*]) => do
      let elems := chain.getElems
      if elems.size < 2 then
        throwError "game_hopping expected at least a start and final oracle"
      checkGameHoppingEndpoints elems[0]! elems[elems.size - 1]!
      let mids := elems.extract 1 (elems.size - 1)
      let mut goals := #[]
      for mid in mids do
        match (← getGoals) with
        | current :: rest =>
            setGoals [current]
            evalTactic (← `(tactic|
              refine IndistinguishableI.trans ($mid) _ ?_ ?_))
            match (← getGoals) with
            | left :: right :: [] =>
                goals := goals.push left
                setGoals (right :: rest)
            | _ =>
                throwError "game_hopping internal error: transitivity did not create two goals"
        | [] =>
            throwError "game_hopping failed: no goals"
      match (← getGoals) with
      | current :: rest =>
          setGoals (goals.toList ++ current :: rest)
      | [] =>
          setGoals goals.toList

elab_rules : tactic
  | `(tactic| game_hopping [$chain,*]) => do
      evalTactic (← `(tactic|game_hopping_basic [$chain,*]))
      evalTactic (← `(tactic| all_goals try game_hopping_reduce_assumption))
      evalTactic (← `(tactic| all_goals try (obs_eq; solve_obs_eq)))
  | `(tactic| game_hopping [$chain,*] using $simps,*) => do
      evalTactic (← `(tactic|game_hopping_basic [$chain,*]))
      evalTactic (← `(tactic| all_goals try game_hopping_reduce_assumption))
      evalTactic (← `(tactic| all_goals try (obs_eq; solve_obs_eq [$simps,*])))
