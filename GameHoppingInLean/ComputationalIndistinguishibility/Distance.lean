import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad


def absn (x : Real) : NNReal := ⟨abs x, abs_nonneg x⟩

def negl (f : ℕ -> NNReal) : Prop :=
  ∀ k, ∃ (B : ℝ), ∀ i, (f i) * (i^k) <= B

def pnegl (f : ℕ -> Real) : Prop :=
  negl (fun x => absn (f x))

def getPMF (r : PMF X) (x : X) : NNReal := (r x).toNNReal -- toNNReal map +inf to zero. Lemma below show that this is never happens here.
lemma pmf_non_inf (r : PMF X) (x : X) : getPMF r x = r x :=
  by
  simp [getPMF]
  have : r x ≠ ⊤ := by
    apply PMF.apply_ne_top
  exact ENNReal.coe_toNNReal this

def distance (x y : NNReal) : NNReal := ⟨dist x y, dist_nonneg⟩

noncomputable
def distancePMF (x y : PMF (Bool)) : NNReal :=
    distance (getPMF x (True)) (getPMF y (True))

noncomputable
def pdistancePMF (x y : PMF Bool) : Real :=
    (getPMF x (True)) - (getPMF y (True))


-- lemmas

lemma pdistancePMFTriangle {x : PMF Bool} (y : PMF Bool) {z : PMF Bool} :
  pdistancePMF x z = pdistancePMF x y + pdistancePMF y z := by
  simp [pdistancePMF]


-- This file proves basic properties of indistinguishability, such as transitivity and symmetry. It also includes the lemma `IndistinguishabilityByReduction`, which shows how to use reductions to prove indistinguishability.

lemma distSymm (x y : NNReal) : distance x y = distance y x := by
  simp [distance]
  simp [dist_comm]


lemma disPMFSymm (x y) : distancePMF x y = distancePMF y x := by
  simp [distancePMF, distSymm]

lemma pdisPMFSymm (x y) : pdistancePMF x y = - pdistancePMF y x := by
  simp [pdistancePMF]


lemma distTriangle {x : NNReal} (y : NNReal) {z : NNReal} : distance x z ≤ distance x y + distance y z := by
  simp [distance]
  apply dist_triangle

lemma distSelf (x : NNReal) : distance x x = 0 := by
  simp [distance]
  -- rfl

-- lemma pdistancePMFSelf (x : PMF Bool) : pdistancePMF x x = 0 := by
--   simp [pdistancePMF]


lemma neglSum (f1 f2 : (κ : ℕ) -> NNReal) : negl f1 -> negl f2 -> negl (fun κ => f1 κ + f2 κ) := by
  intro H1 H2
  simp [negl]
  intro k
  have ⟨w1, H1'⟩ := H1 k
  have ⟨w2, H2'⟩ := H2 k
  exists (w1 + w2)
  intro i
  rw [add_mul]
  apply add_le_add (H1' i) (H2' i)

lemma pneglSum (f1 f2 : (κ : ℕ) -> Real) : pnegl f1 -> pnegl f2 -> pnegl (fun κ => f1 κ + f2 κ) :=
by sorry


lemma neglMonotone (f1 f2 : (κ : ℕ) -> NNReal) (H : forall i, f1 i <= f2 i) : negl f2 -> negl f1 := by
  intro Hn
  simp [negl]
  intro k
  have ⟨w, Hn2⟩ := Hn k
  exists w
  intro i
  have Hn3 := Hn2 i
  trans (↑(f2 i) * ↑i ^ k)
  · have Z := H i
    exact mul_le_mul_left (H i) (↑i ^ k)
  · apply Hn3



lemma neglTriangle (f1 f2 f3 : (κ : ℕ) -> NNReal) (H : forall i, f1 i <= f2 i + f3 i) : negl f2 -> negl f3 -> negl f1 :=
  by
   intro H1 H2
   apply (neglMonotone f1 (fun i => f2 i + f3 i))
   · exact fun i ↦ H i
   apply neglSum <;> assumption

lemma pneglTriangle (f1 f2 f3 : (κ : ℕ) -> Real) (H : forall i, |f1 i| <= |f2 i + f3 i|) : pnegl f2 -> pnegl f3 -> pnegl f1 :=
by sorry

lemma neglTriangle2 (f1 f2 f3 : ℕ -> NNReal)
  (H1 : negl (fun i => distance (f1 i) (f2 i)))
  (H2 : negl (fun i => distance (f2 i) (f3 i)))
  : negl (fun i => distance (f1 i) (f3 i)) :=
  by
    apply neglTriangle _ (fun i => distance (f1 i) (f2 i)) (fun i => distance (f2 i) (f3 i)) <;> try assumption
    intro i
    apply distTriangle


lemma distanceOnBoolIrreflexive (x y : PMF Bool) (H : pdistancePMF x y = 0) : x = y := by
  simp [pdistancePMF] at H
  -- injection H with H
  -- simp [eq_of_dist_eq_zero] at H
  have htrue : x true = y true := by
    rw [← pmf_non_inf, ← pmf_non_inf]
    have H : (getPMF x true).toReal - ↑(getPMF y true) + ↑(getPMF y true) = ↑(getPMF y true) :=
      by
        rw [H]
        simp []
    simp at H
    rw [H]
  apply PMF.ext
  intro b
  cases b
  case true => exact htrue
  case false =>
    have hx := x.tsum_coe
    have hy := y.tsum_coe
    simp only [tsum_fintype, Fintype.sum_bool] at hx hy
    rw [htrue] at hx
    exact (ENNReal.add_right_inj (PMF.apply_ne_top y true)).mp (hx.trans hy.symm)

lemma obseEq_from_2_steps {A : Type _}
  (init : PMF A)
  (f g : A -> PMF Bool)
  (H : forall a : A, pdistancePMF (f a) (g a) = 0)
  :
  pdistancePMF (init.bind f) (init.bind g) = 0 := by
    have H : f=g := by
      ext1 c
      apply distanceOnBoolIrreflexive
      apply H
    rw [H]
    simp [pdistancePMF]
