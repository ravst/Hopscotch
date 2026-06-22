import GameHoppingInLean.Normalization.BitVec.Attrs
import GameHoppingInLean.Normalization.PMF.Lemmas
import GameHoppingInLean.MonadRandomState
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ToMathlib.General

@[GHSimpPMFBitVec]
theorem bitVec_extractLsb'_cast_eq {n m start len : ℕ} (h : n = m) (x : BitVec n) :
    BitVec.extractLsb' start len (BitVec.cast h x) = BitVec.extractLsb' start len x := by
  cases h
  rfl

namespace PMF

/-- Two independent uniform bitvector draws, appended together, are the same as one
uniform draw at the appended width. -/
@[GHSimpPMFBitVec]
theorem bind_uniformOfFintype_bitVec_append_do
    {a b : ℕ} {α : Type} (f : BitVec (a + b) → PMF α) :
    (do
      let x₁ ← PMF.uniformOfFintype (BitVec a)
      let x₂ ← PMF.uniformOfFintype (BitVec b)
      f (x₁ ++ x₂)) =
    (do
      let x ← PMF.uniformOfFintype (BitVec (a + b))
      f x) := by
  change (PMF.uniformOfFintype (BitVec a)).bind
      (fun x₁ => (PMF.uniformOfFintype (BitVec b)).bind
        (fun x₂ => f (x₁ ++ x₂))) =
    (PMF.uniformOfFintype (BitVec (a + b))).bind f
  rw [← PMF.uniformOfFintype_prod_bind
    (f := fun p : BitVec a × BitVec b => f (p.1 ++ p.2))]
  exact (PMF.bind_uniformOfFintype_equiv
    (e := RState.bitVecAppendEquiv a b)
    (g := f)).symm

/-- A uniform bitvector draw observed only through its high and low slices is equivalent
to two independent uniform bitvector draws. -/
@[GHSimpPMFBitVec]
theorem bind_uniformOfFintype_bitVec_extract_do
    {a b : ℕ} {α : Type} (f : BitVec a → BitVec b → PMF α) :
    (do
      let x ← PMF.uniformOfFintype (BitVec (a + b))
      f (BitVec.extractLsb' b a x) (BitVec.extractLsb' 0 b x)) =
    (do
      let x₁ ← PMF.uniformOfFintype (BitVec a)
      let x₂ ← PMF.uniformOfFintype (BitVec b)
      f x₁ x₂) := by
  rw [← bind_uniformOfFintype_bitVec_append_do
    (f := fun x => f (BitVec.extractLsb' b a x) (BitVec.extractLsb' 0 b x))]
  simp [GHSimpPMFBitVec]

/-- The `2 * k` specialization of `bind_uniformOfFintype_bitVec_extract_do`, transported
through the standard `BitVec (k + k) ≃ BitVec (2 * k)` cast. -/
@[GHSimpPMFBitVec]
theorem bind_uniformOfFintype_bitVec_two_mul_extract_do
    {k : ℕ} {α : Type} (f : BitVec k → BitVec k → PMF α) :
    (do
      let x ← PMF.uniformOfFintype (BitVec (2 * k))
      f (BitVec.extractLsb' k k x) (BitVec.extractLsb' 0 k x)) =
    (do
      let x₁ ← PMF.uniformOfFintype (BitVec k)
      let x₂ ← PMF.uniformOfFintype (BitVec k)
      f x₁ x₂) := by
  let h : k + k = 2 * k := by simp [two_mul]
  calc
    (do
      let x ← PMF.uniformOfFintype (BitVec (2 * k))
      f (BitVec.extractLsb' k k x) (BitVec.extractLsb' 0 k x)) =
        (do
          let x ← PMF.uniformOfFintype (BitVec (k + k))
          f (BitVec.extractLsb' k k (BitVec.cast h x))
            (BitVec.extractLsb' 0 k (BitVec.cast h x))) := by
          simpa [RState.bitVecAddEquivTwoMul] using
            (PMF.bind_uniformOfFintype_equiv
              (e := RState.bitVecAddEquivTwoMul k)
              (g := fun x : BitVec (2 * k) =>
                f (BitVec.extractLsb' k k x) (BitVec.extractLsb' 0 k x)))
    _ =
        (do
          let x ← PMF.uniformOfFintype (BitVec (k + k))
          f (BitVec.extractLsb' k k x) (BitVec.extractLsb' 0 k x)) := by
          simp [GHSimpPMFBitVec]
    _ =
        (do
          let x₁ ← PMF.uniformOfFintype (BitVec k)
          let x₂ ← PMF.uniformOfFintype (BitVec k)
          f x₁ x₂) := by
          exact bind_uniformOfFintype_bitVec_extract_do f

end PMF
