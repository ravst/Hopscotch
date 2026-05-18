import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.ObservationalEquvialence
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.OracleSpec
import GameHoppingInLean.IndistinguishabilityDef
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Multiset.UnionInter
import VCVio.ToMathlib.Control.FreeMonad
import Mathlib.Data.Finset.Empty
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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


noncomputable def runDinstinguisher_inner {I stateType : Type _} {O : OracleSpec I}
  (d : OracleComp O Bool) (impl : QueryImpl3 O (RState stateType)) (init : stateType): PMF Bool :=
  let comp := OracleComp.simulateQ (query_impl_convert impl) d
  (comp init).map (fun x => x.1)

lemma runDinstinguisher_inner_bind {I stateType : Type _} {O : OracleSpec I}
  (ro : QueryImpl3 O (RState stateType)) (init : stateType)
  (q : O.OracleQuery β)
  (cont : β → FreeMonad O.OracleQuery Bool)
  : runDinstinguisher_inner (FreeMonad.roll q cont) ro init =
  (do
    let (out, state) <- (query_impl_convert ro).impl q init
    runDinstinguisher_inner (cont out) ro state
  )
:= by
  simp [runDinstinguisher_inner, OracleComp.simulateQ, PMF.map]
  congr 1

lemma runDinstinguisher2inner {I : Type} {O : OracleSpec I}
  (d : OracleComp (withPMFSpec O) Bool) (impl : RStateOracle O) :
  runDinstinguisher d impl =
  (do
    let init <- impl.initialState
    runDinstinguisher_inner d (addPMFtoImpl impl.queries) init)
:= by
  simp [runDinstinguisher, runDinstinguisher_inner]

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

lemma distTriangle {x : NNReal} (y : NNReal) {z : NNReal} : distance x z ≤ distance x y + distance y z := by
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
    intro i
    apply distTriangle

lemma advatangeTriangle {I : Type} {O : OracleSpec I}
  {distinguisher : adversaryT O} (o1 o2 o3 : RStateOracle O) :
  advantage distinguisher o1 o3 <= advantage distinguisher o1 o2 + advantage distinguisher o2 o3 :=
by
  apply distTriangle

lemma advantageRefl {I : Type} {O : OracleSpec I}
  {distinguisher : adversaryT O} (o : RStateOracle O) :
    advantage distinguisher o o = 0 :=
by
  simp [advantage, distancePMF, distSelf]


lemma advatangeTriangleFam {I : Type} {Spec : ℕ -> OracleSpec I}
  (distinguisher : compFamT Spec (fun _κ => Bool)) (o1 o2 o3 : famOracle Spec) :
  forall κ, advantageFam distinguisher o1 o3 κ <= advantageFam distinguisher o1 o2 κ + advantageFam distinguisher o2 o3 κ :=
by
  intro κ
  apply distTriangle

abbrev asUseType (Assumptions : IndistinguishabilityAssumptions) {I : Type} (O : OracleSpec I) (J : Assumptions.Idx) :=
  ℕ × (ComplexInitReduction (Assumptions.assumptions J).O O)
structure AssumptionsUseT (Assumptions : IndistinguishabilityAssumptions)
  {I : Type} (O : OracleSpec I) where
  subset : Finset Assumptions.Idx
  values : (J : subset) -> (
    ℕ × (ComplexInitReduction (Assumptions.assumptions J).O O)
  )

namespace AssumptionsUseT

def empty (Assumptions : IndistinguishabilityAssumptions) {I : Type} (O : OracleSpec I) :
  AssumptionsUseT Assumptions O :=
  {
    subset := ∅,
    values := fun ⟨x, x2⟩ => by
      exfalso
      exact (List.mem_nil_iff x).mp x2
  }

end AssumptionsUseT

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
  : sumJoining XJ D1 D2 val1 val2 f (sumJoiner XJ val1 val2 joiner) := sorry


def assumptionJoiner {Assumptions : IndistinguishabilityAssumptions} {I : Type} {O : OracleSpec I}
  (val1 val2 : AssumptionsUseT Assumptions O)
  (joiner :  {J : Assumptions.Idx} ->
    asUseType Assumptions O J ->
    asUseType Assumptions O J ->
    asUseType Assumptions O J
  )
  : AssumptionsUseT Assumptions O :=
  {
    subset := finsetSum val1.subset val2.subset
    values := sumJoiner (fun J => asUseType Assumptions O J) val1.values val2.values joiner
  }


-- def assumptionJoinerCorrect (Assumptions : IndistinguishabilityAssumptions) {I : Type} (O : OracleSpec I)
--   [DecidableEq Assumptions.Idx]
--   (val1 val2 : AssumptionsUseT Assumptions O)
--   (joiner :  {J : Assumptions.Idx} ->
--     asUseType Assumptions O J ->
--     asUseType Assumptions O J ->
--     asUseType Assumptions O J
--   )
--   (f : {J : Assumptions.Idx} -> asUseType Assumptions O J -> ℝ)
--   (Hjoiner : forall J (x1 x2: asUseType Assumptions O J), f x1 + f x2 = f (joiner x1 x2))
--   : sumJoining (fun J => asUseType Assumptions O J) D1 D2 val1.values val2.values f
--     (sumJoiner (fun J => asUseType Assumptions O J) val1.values val2.values joiner)
--     :=
--     by apply sumJoinerCorrect


-- -- both of this lemmas are probably false :-(
-- def psudo_prhl (f1 : A1 -> PMF B) (f2 : A2 -> PMF B) (x1 : PMF A1) (x2 : PMF A2)
--   (H : x1.bind f1 = x2.bind f2)
--   : { z : PMF (A1 × A2) //
--     z.map (fun x => x.1) = x1 /\
--     z.map (fun x => x.2) = x2 /\
--     z.support ⊆ {(a1, a2) | f1 a1 = f2 a2}
--   } := by sorry
-- def obseEqBoundedDecomp {I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
--   (q_b : ENat) (obs_eq : ObsEqBounded ro₁ ro₂ q_b) (q: QueryS O)
--   (Hq : q_b >= 1) :
--   { z : PMF ((O.range q.index) × ro₁.stateType × ro₂.stateType ) //
--     z.map (fun x => (x.1, x.2.1)) = ((ro₁.queries.impl q.index q.input).run ro₁.initialState) /\
--     z.map (fun x => (x.1, x.2.2)) = ((ro₂.queries.impl q.index q.input).run ro₂.initialState) /\
--     z.support ⊆ { x | ObsEqBounded {ro₁ with initialState := pure x.2.1} {ro₂ with initialState := pure x.2.2} (q_b-1) } /\
--     true
--   } := by sorry

lemma obseEq_from_2_steps {A : Type _}
  (init : PMF A)
  (f g : A -> PMF Bool)
  (H : forall a : A, distancePMF (f a) (g a) = 0)
  :
  distancePMF (init.bind f) (init.bind g) = 0 := by sorry

lemma correctAbstraction2ind_inner  {I : Type _} {O : OracleSpec I} {stateType₁ stateType₂: Type _} (dist : OracleComp O Bool)
  (ro₁ : QueryImpl3 O (RState stateType₁))
  (ro₂ : QueryImpl3 O (RState stateType₂))
  (f : stateType₁ → PMF stateType₂)
  (Habs : ∀ i (query : O.domain i),
      bindOutputState f (ro₁.impl i query) =
      bindInputState f (ro₂.impl i query)) :
  forall (init : stateType₁),
  distancePMF
    (runDinstinguisher_inner dist ro₁ init)
    (do
      let init_v <- f init
      runDinstinguisher_inner dist ro₂ init_v)= 0
  :=  by
  induction dist
  case pure v =>
    simp [advantage, runDinstinguisher_inner, query_impl_convert, OracleComp.simulateQ]
    simp [distancePMF, distSelf]
  case roll  β q cont Hind =>
    intro init
    simp [runDinstinguisher_inner_bind]
    cases q
    case query i t =>
    simp []
    have X := congr_fun (Habs i t) init
    simp [bindOutputState, bindInputState] at X
    simp [StateT.run] at X
    rw [<-PMF.bind_bind]
    rw [<-X]
    simp [bindSecond]
    apply obseEq_from_2_steps
    intro a
    apply Hind a.1

lemma correctAbstractionAfterwithPMFSpec {I : Type _} {stateType₁ stateType₂ : Type _} {O : OracleSpec I}
  (ro₁ : QueryImpl3 O (RState stateType₁)) (ro₂ : QueryImpl3 O (RState stateType₂))
  (f : stateType₁ → PMF stateType₂) (Habs : correctAbstractionBindDiag ro₁ ro₂ f)
  : correctAbstractionBindDiag (addPMFtoImpl ro₁) (addPMFtoImpl ro₂) f := by
  simp [correctAbstractionBindDiag] at Habs
  simp [correctAbstractionBindDiag]
  intro i q
  ext1 z
  simp [bindOutputState, bindInputState]
  simp [StateT.run, addPMFtoImpl]
  cases i
  case oracle x =>
    simp []
    have X := congr_fun (Habs x q)
    simp [bindOutputState, bindInputState, StateT.run] at X
    apply X
  case sample y =>
    simp []
    simp [bindSecond, Function.comp, PMF.map]
    simp only [GameHoppingSimplifyPMF]

    sorry

lemma correctAbstraction2ind {I : Type} {O : OracleSpec I} (dist : adversaryT O)
  (ro₁ ro₂ : RStateOracle O) (f : ro₁.stateType → PMF ro₂.stateType)
  (Habs : correctAbstractionBind ro₁ ro₂ f) :
  advantage dist ro₁ ro₂ = 0
:= by
    simp [advantage]
    simp [runDinstinguisher2inner]
    rw [<-Habs.1]
    simp []
    apply obseEq_from_2_steps
    intro a
    simp [adversaryT] at dist
    have X := correctAbstraction2ind_inner (O := withPMFSpec O) dist (addPMFtoImpl ro₁.queries) (addPMFtoImpl ro₂.queries) f
    apply X
    -- correct abstraction after addPMFtoIMPL, todo.
    apply correctAbstractionAfterwithPMFSpec
    apply Habs.2



lemma rState2Rstate_non_dist {I : Type} {O : OracleSpec I} (o : RStateOracle O) (q_b : ENat) (dist : adversaryT O) (Hdist : FreeMonad.depth dist <= q_b):
  advantage dist o (rState2Rstate q_b o) = 0 := by sorry

lemma behavioral_eq_from_obsEq (ro₁ ro₂ : RStateOracle O) (q_b : ENat) (obs_eq : ObsEqBounded ro₁ ro₂ q_b) :
  BehavioralOracle.into q_b ro₁ = BehavioralOracle.into q_b ro₂ := by sorry

lemma obsEq_distinquishing (ro₁ ro₂ : RStateOracle O) (q_b : ENat) (obs_eq : ObsEqBounded ro₁ ro₂ q_b)
  (dist : adversaryT O) (Hdist : FreeMonad.depth dist <= q_b) :
    advantage dist ro₁ ro₂ = 0 :=
by
  have H1 := rState2Rstate_non_dist ro₁ q_b dist Hdist
  have H2 := rState2Rstate_non_dist ro₂ q_b dist Hdist
  have H3p : BehavioralOracle.into q_b ro₁ = BehavioralOracle.into q_b ro₂ := behavioral_eq_from_obsEq ro₁ ro₂ q_b obs_eq
  have H3 : advantage dist (rState2Rstate q_b ro₁) (rState2Rstate q_b ro₂) = 0 := by
    simp [rState2Rstate]
    rw [H3p]
    apply advantageRefl
  rw [<-nonpos_iff_eq_zero]
  -- calc
  --   advantage dist ro₁ ro₂ <=
  -- have F : advantage dist ro₁ ro₂ <= 0 := by
    -- apply distancePMFtriangle
    -- sorry
  -- calc??
  sorry

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


noncomputable def ascToReal {I : Type} {O : OracleSpec I}
  (distinguisher : FreeMonad (withPMFSpec O).OracleQuery Bool)
  (assumption : SingleAssumption) (x :ℕ × (ComplexInitReduction assumption.O O)) : NNReal :=
  (x).1 *
    advantage
      (applyComplexInitReduction2 (x).2 distinguisher)
      assumption.i.1 assumption.i.2

def advBound2 (Assumptions : IndistinguishabilityAssumptions) (q_b : ENat)
    {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
    (asc : AssumptionsUseT Assumptions O)
    [Fintype (Assumptions.Idx)]
    : Prop :=
    forall distinguisher,
      FreeMonad.depth distinguisher ≤ q_b ->
      (advantage distinguisher ro1 ro2) <= ∑ j : { x // x ∈ asc.subset },
        ascToReal distinguisher (Assumptions.assumptions j) (asc.values j)

lemma advBoundEq (Assumptions : IndistinguishabilityAssumptions) (q_b : ENat)
    {I : Type} (O : OracleSpec I) (ro1 ro2 : RStateOracle O)
    (asc : AssumptionsUseT Assumptions O)
    [Fintype (Assumptions.Idx)] :
    advBound Assumptions q_b O ro1 ro2 asc = advBound2 Assumptions q_b O ro1 ro2 asc :=
by
  simp [advBound2 , advBound, ascToReal]


def advantage_reduction {I1 I2: Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (dist : adversaryT O2) (o1 o2 : RStateOracle O1)
  (r : ComplexInitReduction O1 O2) :
  advantage dist (applyComplexInitReduction r o1) (applyComplexInitReduction r o2) =
  advantage (applyComplexInitReduction2 r dist) o1 o2 := by
    simp [advantage]
    rw [goodDoubleAction]
    rw [goodDoubleAction]

noncomputable def reductionCombiner {I1 I2: Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (x1 x2 : ℕ × (ComplexInitReduction O1 O2)) : ℕ × (ComplexInitReduction O1 O2) :=
  (x1.1+x2.1, {
    stateType := (x1.2.stateType ⊕ x2.2.stateType)
    initialState := (do
      let x : Bool <- RReduction.sample (PMF.bernoulli (x1.1/(x1.1+x2.1)) (
        by
          have H : x1.1 <= x1.1 + x2.1 :=  by
            exact Nat.le_add_right x1.1 x2.1
          refine ENNReal.div_le_of_le_mul ?_
          simp
          )
        )
      if x then
        let init <- x1.2.initialState
        return Sum.inl init
      else
        let init <- x2.2.initialState
        return Sum.inr init
    )
    queries := {
      impl i q := (do
        let x <- srGet!
        match x with
        | Sum.inl s =>
          let x := (x1.2.queries.impl i q)
          SRReduction.addToStateL x _
        | Sum.inr s =>
          SRReduction.addToStateR (x2.2.queries.impl i q) _
      )
    }
  })

lemma reductionCombinerCorrect {I: Type} {O : OracleSpec I}
  (dist : FreeMonad (withPMFSpec O).OracleQuery Bool)
  (assumption : SingleAssumption)
  (x1 x2 : ℕ × (ComplexInitReduction assumption.O O))
  : ascToReal dist assumption x1 + ascToReal dist assumption x2 =
  ascToReal dist assumption (reductionCombiner x1 x2) :=
  by sorry


noncomputable def obse_eq_step
  {Assumptions : IndistinguishabilityAssumptions} [Fintype (Assumptions.Idx)]
  {a : ℕ∞} {I : Type} {O : OracleSpec I}
  (o₁ o₂ : RStateOracle O)
  (Hb : ObsEqBounded o₁ o₂ a)
  : { asc // advBound Assumptions a O o₁ o₂ asc } :=
  ⟨AssumptionsUseT.empty _ _, by
      simp [advBound, AssumptionsUseT.empty]
      intro dist
      apply obsEq_distinquishing
      apply Hb
  ⟩

noncomputable def transitive_step
  {Assumptions : IndistinguishabilityAssumptions} [Fintype (Assumptions.Idx)]
  {q_b : ℕ∞} {I : Type} {O : OracleSpec I}
  {o₁ o₂ : RStateOracle O} (rm : RStateOracle O)
  (as1 : {asc : AssumptionsUseT Assumptions O // advBound Assumptions q_b O o₁ rm asc})
  (as2 : {asc : AssumptionsUseT Assumptions O // advBound Assumptions q_b O rm o₂ asc})
  : {asc : AssumptionsUseT Assumptions O // advBound Assumptions q_b O o₁ o₂ asc} :=
    let ⟨asc1, Hasc1⟩ := as1
    let ⟨asc2, Hasc2⟩ := as2

    let joint : AssumptionsUseT Assumptions O := assumptionJoiner asc1 asc2 (fun a b => reductionCombiner a b)
    ⟨joint,
      (by
        rw [advBoundEq]
        simp [advBound2]
        intro dist Hdepth
        simp [joint, assumptionJoiner]
        have HHx := sumJoinerCorrect (fun J => asUseType Assumptions O J)
          asc1.values asc2.values (fun a b => reductionCombiner a b)
          (fun x => ascToReal dist _ x) (by
            intro j x1 x2
            simp []
            apply reductionCombinerCorrect
          )
        simp [sumJoining] at HHx
        rw [<-HHx]
        clear HHx
        apply le_trans (advatangeTriangle _ rm _)
        -- apply advatangeTriangle _ rm _
        rw [advBoundEq] at Hasc1 Hasc2
        simp [advBound2] at Hasc1 Hasc2
        have L1 := add_le_add (Hasc1 dist Hdepth) (Hasc2 dist Hdepth)
        apply L1
      )
    ⟩

lemma nextInRange {n : ℕ} {x : ℕ} ( H : x ∈ Finset.range n) : x ∈ Finset.range (n+1) :=
by
  refine Finset.mem_range_succ_iff.mpr ?_
  simp [Finset.range] at H
  exact Nat.le_of_succ_le H


def lengthOfIndI {Assumptions : IndistinguishabilityAssumptions}
      [Fintype (Assumptions.Idx)]
      {Reductions : IndistinguishabilityReductions}
      {κ :  ℕ} {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : RStateOracle O} :
      (ind : IndistinguishableI Assumptions Reductions κ q_b O o₁ o₂) -> ℕ
| IndistinguishableI.assumption idx =>
  0
| IndistinguishableI.obsEqB a b =>
  0
| IndistinguishableI.simpleReduction a b c d =>
  1 + lengthOfIndI c
| IndistinguishableI.reduction a b c d =>
  1 + lengthOfIndI c
| IndistinguishableI.randReduction a b c d =>
  1 + lengthOfIndI c
| @IndistinguishableI.complexInitReduction Assumptions Reductions κ I1 I2 O1 O2 r ro1 o₁ b ind Hr =>
  1 + lengthOfIndI ind
| IndistinguishableI.symm q_b ind  =>
  1 + lengthOfIndI ind
| IndistinguishableI.trans rm q_b ind1 ind2 =>
  1 + lengthOfIndI ind1 + lengthOfIndI ind2
| IndistinguishableI.longSequence a q_b ro Hseq =>
  1 + ∑ ⟨i, Hi⟩ : Finset.range a, lengthOfIndI (Hseq i (by
    simp [Finset.range] at Hi
    apply Hi
  ))


theorem sum_ge_entry {X : Type u} {s : Finset X} (a : X) (ha : a ∈ s) (f : X -> ℕ):
    f a ≤ ∑ x ∈ s, f x :=
by
  apply Finset.single_le_sum
  · intro i Hi
    exact Nat.zero_le (f i)
  assumption

theorem sum_ge_entry2 {y : ℕ} {X : Type u} {s : Finset X} (a : X) (ha : a ∈ s) (f : X -> ℕ) (Hle : y <= f a):
    y ≤ ∑ x ∈ s, f x :=
by
  apply Nat.le_trans
  apply Hle
  apply sum_ge_entry
  assumption

noncomputable def symbolicSoundness {Assumptions : IndistinguishabilityAssumptions}
      [Fintype (Assumptions.Idx)]
      {Reductions : IndistinguishabilityReductions}
      {κ :  ℕ} {q_b : ENat}
      {I : Type} {O : OracleSpec I} {o₁ o₂ : RStateOracle O} :
      (ind : IndistinguishableI Assumptions Reductions κ q_b O o₁ o₂) ->
      {asc : AssumptionsUseT Assumptions O // advBound Assumptions q_b O o₁ o₂ asc}
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
  obse_eq_step o₁ o₂ b
| IndistinguishableI.simpleReduction a b c d =>
    sorry
| IndistinguishableI.reduction a b c d =>
    sorry
| IndistinguishableI.randReduction a b c d =>
    sorry
| @IndistinguishableI.complexInitReduction Assumptions Reductions κ I1 I2 O1 O2 r ro1 o₁ b ind Hr => by
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
| IndistinguishableI.trans rm q_b ind1 ind2 =>
    transitive_step rm (symbolicSoundness ind1) (symbolicSoundness ind2)
| IndistinguishableI.longSequence a q_b ro Hseq => by
  have Hxx := fun (i : ℕ) (Hi : i < a) =>
    symbolicSoundness (Hseq i Hi)
  have HMain : forall (i : ℕ) (Hi : i < a+1),
    {asc : AssumptionsUseT Assumptions O //
      advBound Assumptions q_b O (ro ⟨0, zero_in_range _⟩) (ro ⟨i, Finset.mem_range.mpr Hi⟩) asc}
  := (by
    intro i Hi
    induction i
    · apply obse_eq_step
      exact fun queriesList ↦ congrFun rfl
    case succ n Hind =>
      have long := Hind (Nat.lt_of_succ_lt Hi)
      apply transitive_step _ long
      apply Hxx n
      exact Nat.succ_lt_succ_iff.mp Hi
  )
  apply HMain
  exact lt_add_one a
termination_by ind => lengthOfIndI ind
decreasing_by
  all_goals simp [lengthOfIndI]
  · apply Nat.lt_add_right (lengthOfIndI ind2)
    exact lt_one_add (lengthOfIndI ind1)
  · apply Nat.lt_one_add_iff.mpr
    apply sum_ge_entry2 ⟨i, by
      simp [Finset.range, Hi]⟩
    · simp [Finset.attach]
      simp [Multiset.attach, Finset.range]
      assumption
    · rfl
  -- sorry
