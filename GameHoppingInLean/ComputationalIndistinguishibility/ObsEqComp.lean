import GameHoppingInLean.ComputationalIndistinguishibility.AdversaryAdvantage
import GameHoppingInLean.ComputationalIndistinguishibility.BehavioralOracle
import GameHoppingInLean.ObservationalEquvialence
import Mathlib.Data.ENat.Lattice


lemma correctAbstraction2ind_inner {I : Type _} {O : OracleSpec I} {stateType₁ stateType₂ : Type _} (dist : OracleComp O Bool)
  (ro₁ : QueryImpl O (RState stateType₁))
  (ro₂ : QueryImpl O (RState stateType₂))
  (f : stateType₁ → PMF stateType₂)
  (Habs : ∀ (query : O.Domain),
      bindOutputState f (ro₁ query) =
      bindInputState f (ro₂ query)) :
  forall (init : stateType₁),
  pdistancePMF
    (runDinstinguisher_inner dist ro₁ init)
    (do
      let init_v <- f init
      runDinstinguisher_inner dist ro₂ init_v)= 0
  :=  by
  induction dist
  case pure v =>
    simp [advantage, runDinstinguisher_inner, simulateQ]
    simp [pdistancePMF, distSelf]
  case roll β cont Hind =>
    intro init
    simp [runDinstinguisher_inner_bind]
    have X := congr_fun (Habs β) init
    simp [bindOutputState, bindInputState] at X
    simp [StateT.run] at X
    rw [<-PMF.bind_bind]
    rw [<-X]
    simp [bindSecond]
    apply obseEq_from_2_steps
    intro a
    apply Hind a.1


lemma correctAbstractionAfterwithPMFSpec {I : Type _} {stateType₁ stateType₂ : Type _} {O : OracleSpec I}
  (ro₁ : QueryImpl O (RState stateType₁)) (ro₂ : QueryImpl O (RState stateType₂))
  (f : stateType₁ → PMF stateType₂) (Habs : correctAbstractionBindDiag ro₁ ro₂ f)
  : correctAbstractionBindDiag (addPMFtoImpl ro₁) (addPMFtoImpl ro₂) f := by
  simp [correctAbstractionBindDiag] at Habs
  simp [correctAbstractionBindDiag]
  intro q
  ext1 z
  simp [bindOutputState, bindInputState]
  simp [StateT.run, addPMFtoImpl]
  cases q
  case oracle x =>
    simp []
    have X := congr_fun (Habs x)
    simp [bindOutputState, bindInputState, StateT.run] at X
    apply X
  case sample y =>
    simp [bindSecond, Function.comp, PMF.map]
    conv =>
      rhs
      rw [PMF.bind_comm]
    congr

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


noncomputable def FreeM.depth.{uA, uB, uC} {P : PFunctor.{uA, uB}} {α : Type uC} : PFunctor.FreeM P α -> ℕ∞
| PFunctor.FreeM.pure _ => 0
| PFunctor.FreeM.roll _input cont =>
  1 + iSup (fun u => depth (cont u))

lemma rState2Rstate_non_dist {I : Type} {O : OracleSpec I} (o : RStateOracle O) (q_b : ENat) (dist : adversaryT O)
  (Hdist : FreeM.depth dist <= q_b):
  runDinstinguisher dist o = runDinstinguisher dist (rState2Rstate q_b o) := by sorry

lemma behavioral_eq_from_obsEq (ro₁ ro₂ : RStateOracle O) (q_b : ENat) (obs_eq : ObsEqBounded ro₁ ro₂ q_b) :
  BehavioralOracle.into q_b ro₁ = BehavioralOracle.into q_b ro₂ := by sorry



lemma obsEq_distinquishing (ro₁ ro₂ : RStateOracle O) (q_b : ENat) (obs_eq : ObsEqBounded ro₁ ro₂ q_b)
  (dist : adversaryT O) (Hdist : FreeM.depth dist <= q_b) :
    runDinstinguisher dist ro₁ = runDinstinguisher dist ro₂ :=
by
  have H1 := rState2Rstate_non_dist ro₁ q_b dist Hdist
  have H2 := rState2Rstate_non_dist ro₂ q_b dist Hdist
  have H3p : BehavioralOracle.into q_b ro₁ = BehavioralOracle.into q_b ro₂ := behavioral_eq_from_obsEq ro₁ ro₂ q_b obs_eq
  have H3 : runDinstinguisher dist (rState2Rstate q_b ro₁) = runDinstinguisher dist (rState2Rstate q_b ro₂)
  := by
    simp [rState2Rstate]
    rw [H3p]
  rw [H1, H2, H3]

lemma obsEq_distinquishing_adv (ro₁ ro₂ : RStateOracle O) (q_b : ENat) (obs_eq : ObsEqBounded ro₁ ro₂ q_b)
  (dist : adversaryT O) (Hdist : FreeM.depth dist <= q_b) :
    advantage dist ro₁ ro₂ = 0 :=
by
  simp [advantage, pdistancePMF]
  rw [obsEq_distinquishing ro₁ ro₂ q_b]
  ·  simp []
  · assumption
  · assumption

lemma obsEq_distinquishing_ub (ro₁ ro₂ : RStateOracle O) (obs_eq : ObsEq ro₁ ro₂)
  (dist : adversaryT O) :
    runDinstinguisher dist ro₁ = runDinstinguisher dist ro₂ :=
by
  apply obsEq_distinquishing (q_b := none)
  · exact (ObsEq_from_none ro₁ ro₂).mp obs_eq
  · exact le_of_sup_eq' rfl
