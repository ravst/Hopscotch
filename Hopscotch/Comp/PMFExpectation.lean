import Mathlib.Probability.ProbabilityMassFunction.Monad

/- # Expected values of `ENNReal`-valued functions under a `PMF` -/

namespace PMF

/-- The expected value of a nonnegative extended-real-valued function under a probability
mass function. This formulation requires no measurable-space instance on the sample type. -/
noncomputable def expectation (p : PMF α) (f : α → ENNReal) : ENNReal :=
  ∑' x, p x * f x

/-- Expose a PMF expectation as its probability-weighted sum. -/
theorem expectation_eq_tsum (p : PMF α) (f : α → ENNReal) :
    p.expectation f = ∑' x, p x * f x := rfl

@[simp]
theorem expectation_const (p : PMF α) (c : ENNReal) :
    p.expectation (fun _ => c) = c := by
  simp [expectation, ENNReal.tsum_mul_right]

@[simp]
theorem expectation_pure (x : α) (f : α → ENNReal) :
    (pure x : PMF α).expectation f = f x := by
  simp [expectation]

/-- The expectation under a bound PMF is an iterated expectation. -/
theorem expectation_bind (p : PMF α) (g : α → PMF β) (f : β → ENNReal) :
    (p.bind g).expectation f =
      p.expectation (fun x => (g x).expectation f) := by
  simp only [expectation, bind_apply, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  simp only [mul_assoc]

end PMF
