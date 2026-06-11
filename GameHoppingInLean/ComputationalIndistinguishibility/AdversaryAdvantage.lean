import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.ComputationalIndistinguishibility.Distance
import GameHoppingInLean.IndistinguishabilityAssumption

def famOracle {I : Type} (Spec : ℕ -> OracleSpec I) := (κ : ℕ) -> RStateOracle (Spec κ)
def adversaryT {I : Type} (O : OracleSpec I) := OracleComp (withPMFSpec O) Bool



noncomputable def runDinstinguisher {I : Type} {O : OracleSpec I}
  (d : adversaryT O) (impl : RStateOracle O) : PMF Bool :=
  let comp := simulateQ (addPMFtoImpl impl.queries) d
  do
    let init <- impl.initialState
    (comp init).map (fun x => x.1)


noncomputable def runDinstinguisher_inner {I stateType : Type _} {O : OracleSpec I}
  (d : OracleComp O Bool) (impl : QueryImpl O (RState stateType)) (init : stateType) : PMF Bool :=
  let comp := simulateQ impl d
  (comp init).map (fun x => x.1)

lemma runDinstinguisher_inner_bind {I stateType : Type _} {O : OracleSpec I}
  (ro : QueryImpl O (RState stateType)) (init : stateType)
  (q : O.Domain)
  (cont : O q → PFunctor.FreeM O.toPFunctor Bool)
  : @runDinstinguisher_inner I stateType O (PFunctor.FreeM.roll q cont) ro init =
  (do
    let (out, state) <- ro q init
    runDinstinguisher_inner (cont out) ro state
  )
:= by
  simp [runDinstinguisher_inner, simulateQ, PMF.map]
  congr 1

lemma runDinstinguisher2inner {I : Type} {O : OracleSpec I}
  (d : OracleComp (withPMFSpec O) Bool) (impl : RStateOracle O) :
  runDinstinguisher d impl =
  (do
    let init <- impl.initialState
    runDinstinguisher_inner d (addPMFtoImpl impl.queries) init)
:= by
  simp [runDinstinguisher, runDinstinguisher_inner]

lemma goodDoubleAction {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (dist : adversaryT O2) (r : OracleReduction O1 O2) (o : RStateOracle O1) :
  runDinstinguisher dist (OracleReduction.apply r o) =
  runDinstinguisher (OracleReduction.applyReductionToAdversary r dist) o :=
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


noncomputable def ascToReal {I : Type} {O : OracleSpec I}
  (distinguisher : OracleComp (withPMFSpec O) Bool)
  (assumption : SingleAssumption) (x : ℕ × (OracleReduction assumption.O O)) : NNReal :=
  (x).1 *
    advantage
      (OracleReduction.applyReductionToAdversary (x).2 distinguisher)
      assumption.i.1 assumption.i.2


def advantage_reduction {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (dist : adversaryT O2) (o1 o2 : RStateOracle O1)
  (r : OracleReduction O1 O2) :
  advantage dist (OracleReduction.apply r o1) (OracleReduction.apply r o2) =
  advantage (OracleReduction.applyReductionToAdversary r dist) o1 o2 := by
    simp [advantage]
    rw [goodDoubleAction]
    rw [goodDoubleAction]
