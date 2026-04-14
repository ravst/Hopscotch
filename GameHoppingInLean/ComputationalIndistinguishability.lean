import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleComp
import GameHoppingInLean.VCVio2.VCVio.OracleComp.SimSemantics.SimulateQ
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleSpec
import GameHoppingInLean.IndistinguishabilityDef


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

def AssumptionsUseT (Assumptions : IndistinguishabilityAssumptions)
  {I : Type} (O : OracleSpec I) :=
 (J : Assumptions.Idx) -> (ComplexInitReduction (Assumptions.Spec J) O)

def advBound (Assumptions : IndistinguishabilityAssumptions)
    {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
    (asc : AssumptionsUseT Assumptions O)
    [Fintype (Assumptions.Idx)]
    : Prop :=
    forall distinguisher, (advantage distinguisher ro1 ro2) <= ∑ I, advantage (applyComplexInitReduction2 (asc I) distinguisher ) (Assumptions.oraclesL I) (Assumptions.oraclesR I)

def symbolicSoundness {Assumptions : IndistinguishabilityAssumptions}
      [Fintype (Assumptions.Idx)]
      {Reductions : IndistinguishabilityReductions}
      (κ :  ℕ) (q_b : Option ℕ)
      {I : Type} {O : OracleSpec I} {ro₁ ro₂ : RStateOracle O}
      (ind : IndistinguishableI Assumptions Reductions κ q_b O ro₁ ro₂)
      :
      {asc : AssumptionsUseT Assumptions O // advBound Assumptions O ro₁ ro₂ asc} :=
by
  induction ind
  case assumption q_b' it =>
    clear q_b ro₁ ro₂
    -- let f : AssumptionsUseT Assumptions O := fun x =>
    --   if x = it then 1 else 0

    sorry
  case obsEq =>
    sorry
  case simpleReduction =>
    sorry
  case reduction =>
    sorry
  case complexInitReduction =>
    sorry
  case randReduction =>
    sorry
  case symm I' O' ro1' ro2' q_b' ind' asc' =>
    clear ro₁ ro₂ O I
    exact ⟨asc'.1, by
      simp [advBound]
      intro dist
      simp [advantage]
      rw [disPMFSymm]
      apply asc'.2
    ⟩
  case trans I' O' ro1' ro2' ro3' q_b' ind' ind'' asc' asc'' =>
    clear ro₁ ro₂ O I

    sorry
  case longSequence =>
    sorry
