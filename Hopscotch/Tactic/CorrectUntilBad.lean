import Hopscotch.ApproxEq.CorrectUntilBad
import Hopscotch.Tactic.Normalization.RState.Lemmas
import Hopscotch.Tactic.Normalization.PMF.Simprocs
import Mathlib.Tactic.SplitIfs
import Aesop
import Lean

/-!
# Proving correctness until a bad event

`correct_until_bad [definitions]` proves the routine fields of
`IsCorrectUntilBad`: identical initialization, absorbing bad flags, and
pointwise identical queries. For absorption it splits the query constructors,
normalizes PMF support and state operations, and reasons about conditional
branches. Unsolved fields remain in declaration order, with their binders
intact, for the game-specific argument.

`correct_until_bad [definitions] using [lemmas]` also tries the supplied
proofs before normalization. This supports kernels whose absorption property
has already been established separately.

Unlike `by_correct_until_bad`, this tactic proves the correctness condition
itself; it does not apply the approximate-equivalence theorem or prove the
bad-event probability bound.
-/

open Lean Elab Tactic Meta

/-- Discharge routine `IsCorrectUntilBad` fields, leaving game-specific fields. -/
syntax (name := correctUntilBad) "correct_until_bad" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " "[" Lean.Parser.Tactic.SolveByElim.arg,* "]" : tactic
syntax "correct_until_bad" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
syntax "correct_until_bad" : tactic

macro_rules
  | `(tactic| correct_until_bad) => `(tactic| correct_until_bad [] using [])
  | `(tactic| correct_until_bad [$simps,*]) =>
      `(tactic| correct_until_bad [$simps,*] using [])

elab_rules : tactic
  | `(tactic| correct_until_bad [$simps,*] using [$lemmas,*]) => do
      let goal ← getMainGoal
      goal.withContext do
        let target ← whnf (← instantiateMVars (← goal.getType))
        unless target.isAppOf ``IsCorrectUntilBad do
          throwError "correct_until_bad expects an IsCorrectUntilBad goal"
      -- Work only on the main goal, preserving any unrelated goals.
      let otherGoals := (← getGoals).tail!
      setGoals [goal]
      evalTactic (← `(tactic|
        (classical
         refine IsCorrectUntilBad.mk ?_ ?_ ?_ ?_)))
      let fields ← getGoals
      let mut remaining := []
      for (field, index) in fields.zipIdx do
        setGoals [field]
        -- Failed `solve` branches roll back, keeping the field's binders intact.
        evalTactic (← `(tactic|
          (classical
           first
             | solve | intros; rfl
             | solve | assumption
             | solve | solve_by_elim (config := { maxDepth := 2 }) only [$lemmas,*]
             | solve | intros; simp only [id_eq] at *; subst_vars; rfl
             | skip)))
        -- Support normalization is specific to the two absorption fields.
        -- Do not expand pointwise PMF equalities before the user's coupling proof.
        if index < 2 && !(← getGoals).isEmpty then
          evalTactic (← `(tactic|
            (classical
             first
               | solve |
                   intro i st hb p hp
                   cases i <;> simp [$simps,*, sRState, sPMF] at hp
                   all_goals (try split_ifs at hp) <;> simp_all [$simps,*]
                   all_goals aesop
               | skip)))
        remaining := remaining ++ (← getGoals)
      setGoals (remaining ++ otherGoals)
