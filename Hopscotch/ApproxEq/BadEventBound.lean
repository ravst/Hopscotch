import Hopscotch.ApproxEq.CorrectUntilBad
import Mathlib.Probability.Distributions.Uniform

/-!
# Tools for Bellman bad-event bounds

A valuation is an upper bound on the probability of reaching the bad event.
The Bellman condition compares the expected valuation after a query with the
current valuation with one more query available. Monotonicity in the query
budget alone is not sufficient: the transition condition must also be proved.
-/

namespace PMF

/-- Bound an expectation by a constant using only points in its support. -/
lemma expectation_le_const_of_support {A : Type} (p : PMF A) (f : A → ENNReal)
    (c : ENNReal) (h : ∀ a ∈ p.support, f a ≤ c) : p.expectation f ≤ c := by
  calc
    _ ≤ p.expectation (fun _ => c) := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases ha : p a = 0
      · simp [ha]
      · exact mul_le_mul_right (h a (by simpa only [PMF.mem_support_iff] using ha)) _
    _ = c := p.expectation_const c

/-- A `[0,1]`-valued function has expectation at most one. -/
lemma expectation_nnreal_le_one {A : Type} (p : PMF A) (f : A → NNReal)
    (h : ∀ a, f a ≤ 1) : p.expectation (fun a => (f a : ENNReal)) ≤ 1 := by
  apply expectation_le_const_of_support
  intro a _
  exact ENNReal.coe_le_coe.mpr (h a)

/-- The probability of guessing a fixed uniformly sampled value. -/
lemma expectation_uniform_eq {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]
    (a : A) : (PMF.uniformOfFintype A).expectation
      (fun b => ((if a = b then 1 else 0 : NNReal) : ENNReal)) =
        (Fintype.card A : ENNReal)⁻¹ := by
  simp [PMF.expectation, apply_ite]

end PMF

namespace IsValidBadEventBound

/-- Only states with valuation below one need a transition calculation. -/
lemma of_subunit {I S : Type} {O : OracleSpec I} {bad : S → Bool}
    {queries : QueryImpl O (RState S)} {bound : S → ENat → NNReal}
    (hle : ∀ s q, bound s q ≤ 1)
    (hbad : ∀ s q, bad s = true → bound s q = 1)
    (hstep : ∀ i s q, bound s (q + 1) ≠ 1 →
      (queries i s).expectation (fun p => (bound p.2 q : ENNReal)) ≤
        (bound s (q + 1) : ENNReal)) :
    IsValidBadEventBound O bad queries bound := by
  refine ⟨hle, hbad, ?_⟩
  intro i s q
  by_cases h : bound s (q + 1) = 1
  · rw [h, ENNReal.coe_one]
    exact PMF.expectation_nnreal_le_one _ _ (fun p => hle p.2 q)
  · exact hstep i s q h

/-- Normal forms for the infinite and finite query budgets. -/
lemma top_add_one : (⊤ : ENat) + 1 = ⊤ := rfl

lemma coe_add_one (n : Nat) : (n : ENat) + 1 = ((n + 1 : Nat) : ENat) := rfl

/-- More available queries cannot decrease a budget-monotone valuation. -/
lemma monotone_budget_step {S : Type} {bound : S → ENat → NNReal}
    (h : ∀ s, Monotone (bound s)) (s : S) (q : ENat) :
    bound s q ≤ bound s (q + 1) :=
  h s le_self_add

end IsValidBadEventBound
