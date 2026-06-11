import Mathlib.Data.Finset.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Multiset.UnionInter
import Mathlib.Data.Finset.Empty
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Probability.ProbabilityMassFunction.Basic

-- SUM JOINIG
def finsetSum {X : Type} [DecidableEq X] (s1 s2 : Finset X) : Finset X :=
  s1 ∪ s2

def sumJoining {Univ : Type} (XJ : Univ -> Type v) [DecidableEq Univ] (D1 D2 : Finset Univ)
  (val1 : (J : D1) -> XJ J)
  (val2 : (J : D2) -> XJ J)
  (f : {J : Univ} -> XJ J -> NNReal)
  (val3 : (J : finsetSum D1 D2) -> XJ J) : Prop :=
    (∑ j1, f (val1 j1)) + (∑ j2, f (val2 j2)) =
    (∑ j3, f (val3 j3))

def sumJoiner {Univ : Type} (XJ : Univ -> Type v) [DecidableEq Univ] {D1 D2 : Finset Univ}
  (val1 : (J : D1) -> XJ J)
  (val2 : (J : D2) -> XJ J)
  (joiner : {J : Univ} -> XJ J -> XJ J -> XJ J) : (J : finsetSum D1 D2) -> XJ J  :=
    fun x =>
      have H0 : x.val ∈ D1 ∨ x.val ∈ D2 := by
        cases x
        case mk a b =>
          simp [finsetSum] at b
          apply b
      if H : x.val ∉ D1 then
        val2 ⟨x, by
          simp [H] at H0
          apply H0⟩
      else
      let Hn : x.val ∈ D1 := by simp [] at H; apply H
      if H2 : x.val ∉ D2 then
        val1 ⟨x, Hn⟩
      else joiner (val1 ⟨x, Hn⟩) (val2 ⟨x, by
        simp [] at H2
        apply H2
        ⟩)

def sumJoinerCorrect {Univ : Type} (XJ : Univ -> Type v) [DecidableEq Univ] {D1 D2 : Finset Univ}
  (val1 : (J : D1) -> XJ J)
  (val2 : (J : D2) -> XJ J)
  (joiner : {J : Univ} -> XJ J -> XJ J -> XJ J)
  (f : {J : Univ} -> XJ J -> NNReal)
  (Hjoiner : forall J (x1 : XJ J) (x2 : XJ J), f x1 + f x2 = f (joiner x1 x2))
  : sumJoining XJ D1 D2 val1 val2 f (sumJoiner XJ val1 val2 joiner) := by
  classical
  let g1 : Univ → NNReal := fun j =>
    if h : j ∈ D1 then f (val1 ⟨j, h⟩) else 0
  let g2 : Univ → NNReal := fun j =>
    if h : j ∈ D2 then f (val2 ⟨j, h⟩) else 0
  let g3 : Univ → NNReal := fun j =>
    if h : j ∈ finsetSum D1 D2 then
      f (sumJoiner XJ val1 val2 joiner ⟨j, h⟩)
    else 0
  have hval1 :
      (∑ j : D1, f (val1 j)) = ∑ j ∈ finsetSum D1 D2, g1 j := by
    calc
      (∑ j : D1, f (val1 j)) = ∑ j : D1, g1 j := by
        apply Fintype.sum_congr
        intro j
        simp [g1]
      _ = ∑ j ∈ D1, g1 j := (Finset.sum_subtype D1 (by simp) g1).symm
      _ = ∑ j ∈ finsetSum D1 D2, g1 j := by
        apply Finset.sum_subset
        · simp [finsetSum]
        · intro j _ hj
          simp [g1, hj]
  have hval2 :
      (∑ j : D2, f (val2 j)) = ∑ j ∈ finsetSum D1 D2, g2 j := by
    calc
      (∑ j : D2, f (val2 j)) = ∑ j : D2, g2 j := by
        apply Fintype.sum_congr
        intro j
        simp [g2]
      _ = ∑ j ∈ D2, g2 j := (Finset.sum_subtype D2 (by simp) g2).symm
      _ = ∑ j ∈ finsetSum D1 D2, g2 j := by
        apply Finset.sum_subset
        · simp [finsetSum]
        · intro j _ hj
          simp [g2, hj]
  have hval3 :
      (∑ j : finsetSum D1 D2, f (sumJoiner XJ val1 val2 joiner j)) =
        ∑ j ∈ finsetSum D1 D2, g3 j := by
    calc
      (∑ j : finsetSum D1 D2, f (sumJoiner XJ val1 val2 joiner j)) =
          ∑ j : finsetSum D1 D2, g3 j := by
        apply Fintype.sum_congr
        intro j
        simp [g3]
      _ = ∑ j ∈ finsetSum D1 D2, g3 j :=
        (Finset.sum_subtype (finsetSum D1 D2) (by simp) g3).symm
  simp only [sumJoining]
  rw [hval1, hval2, hval3, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h1 : j ∈ D1 <;> by_cases h2 : j ∈ D2
  · simpa [g1, g2, g3, sumJoiner, h1, h2, hj] using
      Hjoiner j (val1 ⟨j, h1⟩) (val2 ⟨j, h2⟩)
  · simp [g1, g2, g3, sumJoiner, h1, h2, hj]
  · simp [g1, g2, g3, sumJoiner, h1, h2, hj]
  · simp [finsetSum, h1, h2] at hj
