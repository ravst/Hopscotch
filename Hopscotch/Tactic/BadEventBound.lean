import Hopscotch.ApproxEq.BadEventBound
import Hopscotch.Tactic.Normalization.RState.Lemmas
import Hopscotch.Tactic.Normalization.PMF.Simprocs
import Mathlib.Tactic.SplitIfs
import Lean

/-!
# Valuation and probability-bound automation

`valid_bad_bound [definitions] using [lemmas]` proves `IsValidBadEventBound`.
It checks the valuation's upper bound and value on bad states, then proves
its one-query Bellman inequality. States with valuation one are handled by
the framework. Unresolved subunit transitions remain as explicit goals.

`bound_expectation [definitions] using [lemmas]` lifts pointwise bounds on a
PMF's support to bounds on its expectation. Budget-monotonicity proofs can
be supplied as lemmas, but never replace the transition obligation.
-/

open Lean Elab Tactic Meta

private partial def boundConjuncts (h : Expr) : MetaM (List Expr) := do
  let type ← whnf (← inferType h)
  if type.isAppOf ``And then
    let left ← mkAppM ``And.left #[h]
    let right ← mkAppM ``And.right #[h]
    return (← boundConjuncts left) ++ (← boundConjuncts right)
  return [h]

/-- Apply supplied valuation facts and local hypotheses without unfolding kernels. -/
syntax "solveBoundRules" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

elab_rules : tactic
  | `(tactic| solveBoundRules [$rules,*]) => withMainContext do
      let step ← `(term| IsValidBadEventBound.monotone_budget_step)
      let terms : List (TSyntax `term) := rules.getElems.toList.filterMap fun arg =>
        if arg.raw[0].isNone && arg.raw[1].isNone then some ⟨arg.raw[2]⟩ else none
      for term in terms do
        let saved ← saveState
        try
          evalTactic (← `(tactic| exact $term))
          return
        catch _ => restoreState saved
      let (lemmas, locals) ← Lean.Meta.SolveByElim.mkAssumptionSet
        true true (terms ++ [step]) [] #[]
      -- Derive conjunction facts once, rather than using unconstrained `And.left`
      -- as a search rule on arbitrary probability inequalities.
      let facts := fun cfg => do
        let hypotheses ← locals cfg
        hypotheses.flatMapM fun h => boundConjuncts h
      replaceMainGoal (← Lean.Meta.SolveByElim.solveByElim
        { maxDepth := 3, transparency := .default } lemmas facts [← getMainGoal])

syntax "bound_expectation" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
syntax "bound_expectation" " using " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
syntax "bound_expectation" : tactic

macro_rules
  | `(tactic| bound_expectation) => `(tactic| bound_expectation [] using [])
  | `(tactic| bound_expectation using [$rules,*]) =>
      `(tactic| bound_expectation [] using [$rules,*])

elab_rules : tactic
  | `(tactic| bound_expectation [$simps,*] using [$rules,*]) => do
      evalTactic (← `(tactic|
        focus
          classical
          first
            | solve | solveBoundRules [$rules,*]
            | (apply PMF.expectation_le_const_of_support
               intro value support
               try simp only [ENNReal.coe_le_coe]
               try (solve | solveBoundRules [$rules,*])
               all_goals try simp only [PMF.mem_support_pure_iff, $simps,*] at support
               all_goals try subst value
               all_goals try simp [sPMF, sRState, ENNReal.coe_le_coe, $simps,*]
               all_goals try solveBoundRules [$rules,*])))

syntax "valid_bad_bound" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
syntax "valid_bad_bound" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
syntax "valid_bad_bound" : tactic

macro_rules
  | `(tactic| valid_bad_bound) => `(tactic| valid_bad_bound [] using [])
  | `(tactic| valid_bad_bound [$simps,*]) => `(tactic| valid_bad_bound [$simps,*] using [])

elab_rules : tactic
  | `(tactic| valid_bad_bound [$simps,*] using [$rules,*]) => do
      let goal ← getMainGoal
      let budgetDependent ← goal.withContext do
        let target ← whnf (← goal.getType)
        unless target.isAppOf ``IsValidBadEventBound do
          throwError "valid_bad_bound expects an IsValidBadEventBound goal"
        let bound := target.getAppArgs.back!
        forallTelescope (← inferType bound) fun args _ => do
          let body ← withTransparency .all <| whnf (mkAppN bound args)
          return body.containsFVar args[1]!.fvarId!
      let otherGoals := (← getGoals).tail!
      setGoals [goal]
      let combined := simps.getElems ++ rules.getElems
      evalTactic (← `(tactic| apply IsValidBadEventBound.of_subunit))
      let fields ← getGoals
      let mut remaining := []
      for (field, index) in fields.zipIdx do
        setGoals [field]
        if index < 2 then
          evalTactic (← `(tactic|
            first
              | (solve | solveBoundRules [$rules,*])
              | solve |
                  classical
                  intros
                  try simp_all [sPMF, sRState, $combined,*]
                  all_goals (try split_ifs) <;> simp_all [sPMF, sRState, $combined,*]
              | skip))
        if index == 2 then
          let query := mkIdent (← mkFreshUserName `query)
          let budget := mkIdent (← mkFreshUserName `budget)
          let splitBudget ← if budgetDependent then `(tactic| cases $budget:ident)
            else `(tactic| skip)
          let finish ← if budgetDependent then `(tactic| skip) else `(tactic|
            (all_goals try (cases $query:ident)
             all_goals try simp [sRState, sPMF, PMF.expectation_bind, $simps,*]
             all_goals try (solve | solveBoundRules [$rules,*])
             all_goals repeat' (first
               | simp_all [PMF.expectation_bind, PMF.expectation_uniform_eq,
                   ENNReal.coe_le_coe, $combined,*]
               | split_ifs)
             all_goals try solveBoundRules [$rules,*]))
          evalTactic (← `(tactic|
            (classical
             intro $query:ident st $budget:ident subunit
             $splitBudget
             all_goals try simp only [IsValidBadEventBound.top_add_one,
               IsValidBadEventBound.coe_add_one] at subunit
             all_goals try dsimp only [$simps,*] at subunit
             all_goals try simp only [ite_self, ne_eq, not_true_eq_false] at subunit
             all_goals try (split at subunit)
             all_goals try simp only [not_or, not_not, Bool.not_eq_true,
               ne_eq, not_true_eq_false] at *
             all_goals try simp only [IsValidBadEventBound.top_add_one,
               IsValidBadEventBound.coe_add_one]
             all_goals try (solve | bound_expectation [$simps,*] using [$rules,*])
             all_goals try
               (solve |
                 simp [sRState, sPMF, PMF.expectation_bind, $simps,*]
                 all_goals solveBoundRules [$rules,*])
             $finish)))
        remaining := remaining ++ (← getGoals)
      setGoals (remaining ++ otherGoals)
