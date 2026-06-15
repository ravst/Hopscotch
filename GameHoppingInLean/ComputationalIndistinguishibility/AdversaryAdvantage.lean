import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.ComputationalIndistinguishibility.Distance
import GameHoppingInLean.IndistinguishabilityAssumption
import GameHoppingInLean.Misc.SimpAttrLemmas

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

/-- Equation lemma for the queries of an applied reduction, phrased so that it only
rewrites the *applied* form `(apply r o).queries i` (leaving the partially-applied
`(apply r o).queries` used as a simulation oracle intact, so the induction hypothesis
still matches). -/
private lemma apply_queries_apply {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
    (r : OracleReduction O1 O2) (o : RStateOracle O1) (i : I2) :
    (OracleReduction.apply r o).queries i =
      simulateQ (OracleReduction.liftWithPMFAndState o.queries r.stateType) (r.queries i) := rfl
open OracleReduction in
/-- Core state-commutation step: simulating a single `withPMFAndStateSpec` computation `c`
  against `o` with the joint reduction/oracle state (left) equals first threading the
  reduction state via `defaultImpl` and then simulating against `o` (right), up to a
  reshuffling of the state pair. -/
lemma goodDoubleAction_step {I1 : Type} {O1 : OracleSpec I1} {s X : Type}
    (o : RStateOracle O1)
    (c : OracleComp (withPMFAndStateSpec s O1) X) (sr : s) (so : o.stateType) :
    (simulateQ (liftWithPMFAndState o.queries s) c) (sr, so)
    =
    ((simulateQ (addPMFtoImpl o.queries)
        ((simulateQ defaultImpl c) sr)) so).map
      (fun p => (p.1.1, (p.1.2, p.2))) := by
  induction c using OracleComp.inductionOn generalizing sr so with
  | pure x =>
    simp [goodDoubleActionSimps, OracleReductionSimps, StateTSimps]
    simp [goodDoubleActionSimps, OracleReductionSimps, StateTSimps, pure]

  | query_bind t mx h =>
      rw [simulateQ_query_bind, simulateQ_query_bind]
      -- All four heads reduce by unfolding the simulation/state-threading plumbing with
      -- the `goodDoubleActionSimps` set and applying the induction hypothesis `h` to the
      -- tails.  The `setState` head additionally needs the `RState.modify` rewrite, which
      -- `simp` does not perform on its own here.
      cases t with
      | setState st =>
          simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, h, RStateSimplifier, pure]
      | _ =>
        simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, h, RStateSimplifier, pure] <;> try rfl


set_option maxHeartbeats 4000000 in
open OracleReduction in
/-- The distinguisher-level analogue of `goodDoubleAction_step`: simulating `dist`
against the combined oracle `apply r o` (threading the joint reduction/oracle state)
equals first threading the reduction state (via the reduction's own simulation and
`defaultImpl`) and then simulating against `o`. Proved by induction on `dist`, using
`goodDoubleAction_step` to discharge each underlying oracle query. -/
lemma goodDoubleAction_core {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2} {X : Type}
    (r : OracleReduction O1 O2) (o : RStateOracle O1)
    (dist : OracleComp (withPMFSpec O2) X) (sr : r.stateType) (so : o.stateType) :
    StateT.run (simulateQ (addPMFtoImpl (OracleReduction.apply r o).queries) dist) (sr, so)
    =
    (StateT.run (simulateQ (addPMFtoImpl o.queries)
        (StateT.run (simulateQ defaultImpl (simulateQ (addPMFtoImpl2 r.queries) dist)) sr)) so).map
      (fun p => (p.1.1, (p.1.2, p.2))) := by
  induction dist using OracleComp.inductionOn generalizing sr so with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    change pure (x, sr, so) = PMF.map (fun p => (p.1.1, p.1.2, p.2)) (PMF.pure ((x, sr), so))
    rw [PMF.map_pure_eq_pure]
    rfl
  | query_bind t mx h =>
    cases t with
    | oracle tt =>
      rw [simulateQ_query_bind, simulateQ_query_bind]
      simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier, pure,
        goodDoubleAction_step, addPMFtoImpl2]
      congr
      ext1 st
      simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier, pure,
       addPMFtoImpl2] at h
      apply h
    | sample p =>
      rw [simulateQ_query_bind, simulateQ_query_bind]
      simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier, pure,
        goodDoubleAction_step]
      simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier, pure,
       addPMFtoImpl2] at h
      conv =>
        lhs
        arg 2
        intro a
        rw [h]
      simp [addPMFtoImpl2]
      simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier, pure]
      simp [OracleQuery.input, OracleSpec.query]
      simp [goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier, pure]
      rfl

open OracleReduction in
lemma goodDoubleAction_core2 {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2} {X : Type}
    (r : OracleReduction O1 O2) (o : RStateOracle O1)
    (dist : OracleComp (withPMFSpec O2) X) (srt : r.stateType × o.stateType) :
    (simulateQ (addPMFtoImpl (OracleReduction.apply r o).queries) dist) srt
    =
    ( (simulateQ (addPMFtoImpl o.queries)
        ( (simulateQ defaultImpl (simulateQ (addPMFtoImpl2 r.queries) dist)) srt.1)) srt.2).map
      (fun p => (p.1.1, (p.1.2, p.2))) :=
    by
      apply goodDoubleAction_core

/-  probably could be proven by induction over dist -/
lemma goodDoubleAction {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (dist : adversaryT O2) (r : OracleReduction O1 O2) (o : RStateOracle O1) :
  runDinstinguisher dist (OracleReduction.apply r o) =
  runDinstinguisher (OracleReduction.applyReductionToAdversary r dist) o :=
by
  simp [runDinstinguisher]
  conv =>
    lhs
    arg 1
    simp [OracleReduction.apply]
  simp []
  congr
  ext1 initS
  conv =>
    lhs
    arg 2
    intro init
    arg 2
    rw [goodDoubleAction_core2]
  simp [StateT.run]
  simp [OracleReduction.applyReductionToAdversary]
  simp [StateT.run]
  simp [PMF.map_bind]
  congr
  ext1 init
  simp [PMF.monad_map_eq_map]
  simp [PMF.map_comp]
  unfold Function.comp
  simp []


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
