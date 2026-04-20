import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleComp
import GameHoppingInLean.VCVio2.VCVio.OracleComp.SimSemantics.SimulateQ
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleSpec
import GameHoppingInLean.IndistinguishabilityDef
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Multiset.UnionInter
import GameHoppingInLean.VCVio2.ToMathlib.Control.FreeMonad

-- generic intro. move.

def negl (f : ℕ -> NNReal) : Prop :=
  ∀ k, ∃ (B : ℝ), ∀ i, (f i) * (i^k) <= B

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

-- noncomputable
-- def distanceFam (x y : ℕ → PMF (Bool)) : ℕ → NNReal :=
--   fun κ => distancePMF (x κ) (y κ)


-- proper code

def famOracle {I : Type} (Spec : ℕ -> OracleSpec I) := (κ : ℕ) -> RStateOracle (Spec κ)
def adversaryT {I : Type} (O : OracleSpec I) := OracleComp (withPMFSpec O) Bool

noncomputable def runDinstinguisher {I : Type} {O : OracleSpec I}
  (d : adversaryT O) (impl : RStateOracle O) : PMF Bool :=
  let comp := OracleComp.simulateQ (query_impl_convert (addPMFtoImpl impl.queries)) d
  do
    let init <- impl.initialState
    (comp init).map (fun x => x.1)


lemma goodDoubleAction {I1 I2: Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (dist : adversaryT O2) (r : ComplexInitReduction O1 O2) (o : RStateOracle O1) :
  runDinstinguisher dist (applyComplexInitReduction r o) =
  runDinstinguisher (applyComplexInitReduction2 r dist) o :=
by
  sorry

def compFamT {I : Type} (Spec : ℕ -> OracleSpec I) (Output : ℕ -> Type) := (κ : ℕ) -> OracleComp (withPMFSpec (Spec κ)) (Output κ)


noncomputable def runDinstinguisherFam {I : Type} {Spec : ℕ -> OracleSpec I}
  (d : compFamT Spec (fun _κ => Bool)) (impl : famOracle Spec) (κ : ℕ) : PMF Bool :=
  runDinstinguisher (d κ) (impl κ)

def PolyFamOracleCompPred : Type 1 :=
  {I : Type} -> {Spec : ℕ -> OracleSpec I} -> {Output : ℕ -> Type} -> (compFamT Spec Output) -> Prop

noncomputable
def advantage {I : Type} {O : OracleSpec I}
  (distinguisher : adversaryT O) (o1 o2 : RStateOracle O) : NNReal :=
  distancePMF (runDinstinguisher distinguisher o1) (runDinstinguisher distinguisher o2)

noncomputable
def advantageFam {I : Type} {Spec : ℕ -> OracleSpec I}
  (distinguisher : compFamT Spec (fun _κ => Bool)) (o1 o2 : famOracle Spec) (κ : ℕ) : NNReal :=
  advantage (distinguisher κ) (o1 κ) (o2 κ)

noncomputable
def CompIndistinguishabilitySeededOracle
  {I : Type} {Spec : ℕ -> OracleSpec I}
  (IsPolyTime : PolyFamOracleCompPred)
  (o1 o2 : famOracle Spec)
  : Prop :=
    -- All distinguishers ...
    ∀ distinguisher : compFamT Spec (fun _κ => Bool),
    -- ... that run in polynomial time ...
    (IsPolyTime distinguisher) ->
    -- ... only achieve negligible advantage.
    negl (advantageFam distinguisher o1 o2)


-- lemmas

-- This file proves basic properties of indistinguishability, such as transitivity and symmetry. It also includes the lemma `IndistinguishabilityByReduction`, which shows how to use reductions to prove indistinguishability.

lemma distSymm (x y : NNReal) : distance x y = distance y x := by
  simp [distance]
  simp [dist_comm]


lemma disPMFSymm (x y ) : distancePMF x y = distancePMF y x := by
  simp [distancePMF, distSymm]

lemma distTriangle (x y z : NNReal) : distance x z ≤ distance x y + distance y z := by
  simp [distance]
  apply dist_triangle


lemma distSelf (x : NNReal) : distance x x = 0 := by
  simp [distance]

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
    exact mul_le_mul_right' (H i) (↑i ^ k)
  · apply Hn3

lemma neglTriangle (f1 f2 f3 : (κ : ℕ) -> NNReal) (H : forall i, f1 i <= f2 i + f3 i) : negl f2 -> negl f3 -> negl f1 :=
  by
   intro H1 H2
   apply (neglMonotone f1 (fun i => f2 i + f3 i))
   exact fun i ↦ H i
   apply neglSum <;> assumption

lemma neglTriangle2 (f1 f2 f3: ℕ -> NNReal)
  (H1 : negl (fun i => distance (f1 i) (f2 i)))
  (H2 : negl (fun i => distance (f2 i) (f3 i)))
  : negl (fun i => distance (f1 i) (f3 i)) :=
  by
    apply neglTriangle _ (fun i => distance (f1 i) (f2 i)) (fun i => distance (f2 i) (f3 i)) <;> try assumption
    exact fun i ↦ distTriangle (f1 i) (f2 i) (f3 i)


lemma advatangeTriangle {I : Type} {Spec : ℕ -> OracleSpec I}
  (distinguisher : compFamT Spec (fun _κ => Bool)) (o1 o2 o3 : famOracle Spec) :
  forall κ, advantageFam distinguisher o1 o3 κ <= advantageFam distinguisher o1 o2 κ + advantageFam distinguisher o2 o3 κ :=
by
  intro κ
  apply distTriangle

-- def advantageO {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O) :=

-- SUM JOINIG
def finsetSum {X : Type} [DecidableEq X] (s1 s2 : Finset X) : Finset X :=
  s1 ∪ s2

def sumJoining {Univ : Type} {XJ : Univ -> Type} [DecidableEq Univ] (D1 D2 : Finset Univ)
  (val1 : (J : D1) -> XJ J)
  (val2 : (J : D2) -> XJ J)
  (f : {J : Univ} -> XJ J -> ℝ)
  (val3 : (J : finsetSum D1 D2) -> XJ J) : Prop :=
    (∑ j1, f (val1 j1)) + (∑ j2, f (val2 j2)) =
    (∑ j3, f (val3 j3))

def sumJoiner {Univ : Type} {XJ : Univ -> Type} [DecidableEq Univ] {D1 D2 : Finset Univ}
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

def sumJoinerCorrect {Univ : Type} {XJ : Univ -> Type} [DecidableEq Univ] {D1 D2 : Finset Univ}
  (val1 : (J : D1) -> XJ J)
  (val2 : (J : D2) -> XJ J)
  (joiner : {J : Univ} -> XJ J -> XJ J -> XJ J)
  (f : {J : Univ} -> XJ J -> ℝ)
  (Hjoiner : forall J (x1 : XJ J) (x2 : XJ J), f x1 + f x2 = f (joiner x1 x2))
  : sumJoining D1 D2 val1 val2 f (sumJoiner val1 val2 joiner) := sorry

 --

lemma obsEq_distinquishing (ro₁ ro₂ : RStateOracle O) (q_b : ENat) (obs_eq : ObsEqBounded ro₁ ro₂ q_b)
  (dist : adversaryT O) : FreeMonad.depth dist <= q_b ->
    advantage dist ro₁ ro₂ = 0 := by sorry


structure AssumptionsUseT (Assumptions : IndistinguishabilityAssumptions)
  {I : Type} (O : OracleSpec I) where
  subset : Finset Assumptions.Idx
  values : (J : subset) -> (
    ℕ × (ComplexInitReduction (Assumptions.assumptions J).O O)
  )

def advBound (Assumptions : IndistinguishabilityAssumptions) (q_b : ENat)
    {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
    (asc : AssumptionsUseT Assumptions O)

    [Fintype (Assumptions.Idx)]
    : Prop :=
    forall distinguisher,
      FreeMonad.depth distinguisher ≤ q_b ->
      (advantage distinguisher ro1 ro2) <= ∑ j,
        (asc.values j).1 *
        advantage
          (applyComplexInitReduction2 (asc.values j).2 distinguisher)
          (Assumptions.assumptions j).i.1 (Assumptions.assumptions j).i.2

def advantage_reduction {I1 I2: Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (dist : adversaryT O2) (o1 o2 : RStateOracle O1)
  (r : ComplexInitReduction O1 O2) :
  advantage dist (applyComplexInitReduction r o1) (applyComplexInitReduction r o2) =
  advantage (applyComplexInitReduction2 r dist) o1 o2 := by
    simp [advantage]
    rw [goodDoubleAction]
    rw [goodDoubleAction]

def symbolicSoundness {Assumptions : IndistinguishabilityAssumptions}
      [Fintype (Assumptions.Idx)]
      {Reductions : IndistinguishabilityReductions}
      {κ :  ℕ} {q_b : ENat}
      {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O} :
      (ind : IndistinguishableI Assumptions Reductions κ q_b O ro₁ ro₂) ->
      {asc : AssumptionsUseT Assumptions O // advBound Assumptions q_b O ro₁ ro₂ asc}
| IndistinguishableI.assumption idx =>
  ⟨{ subset := {idx}, values := fun xp => by
      cases xp
      case mk xp' Hxp =>
      simp []
      simp at Hxp
      rw [Hxp]
      exact (1, ComplexInitReduction.identity (Assumptions.assumptions idx).O) },
    by
      simp [advBound]
      intro dist Hdist
      rw [applyComplexInitReduction2_identity]
  ⟩
| IndistinguishableI.obsEqB a b =>
  ⟨{
    subset := {}
    values := fun Hneg => by
      exfalso
      simp at Hneg
      apply Hneg.2
    }, by
      simp [advBound]
      intro dist
      apply obsEq_distinquishing
      apply b
  ⟩
| IndistinguishableI.simpleReduction a b c d =>
    sorry
| IndistinguishableI.reduction a b c d =>
    sorry
| IndistinguishableI.randReduction a b c d =>
    sorry
| @IndistinguishableI.complexInitReduction Assumptions Reductions κ I1 I2 O1 O2 r ro1 ro2 b ind Hr => by
    clear ro₁ ro₂ O I
    let ⟨asc, Hasc⟩ := symbolicSoundness ind
    exact
      ⟨{
        subset := asc.subset
        values := fun x => ((asc.values x).1, ComplexInitReduction2_compose (asc.values x).2 r)
      },
      by
        simp [advBound]
        intro dist Hdist
        rw [advantage_reduction]
        simp [advBound] at Hasc
        apply le_trans (Hasc (applyComplexInitReduction2 r dist) (by
          exact sup_eq_left.mp rfl))
        apply le_of_eq
        congr
        ext j
        rw [ComplexInitReduction2_compose_apply]
      ⟩
| IndistinguishableI.symm q_b ind  =>
    let re := symbolicSoundness ind
    ⟨re.val, by
      simp [advBound]
      intro dist
      simp [advantage]
      rw [disPMFSymm]
      apply re.2
      ⟩
| IndistinguishableI.trans a b c =>
    sorry
| IndistinguishableI.longSequence a b c d e f g h =>
    sorry
