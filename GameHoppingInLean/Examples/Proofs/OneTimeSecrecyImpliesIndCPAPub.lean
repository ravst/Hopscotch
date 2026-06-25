import GameHoppingInLean.Examples.SecurityDefinitions.IndCPAPub
import GameHoppingInLean.Examples.SecurityDefinitions.OneTimeSecrecy
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.Normalization.PMF.Simprocs
import GameHoppingInLean.Normalization.BitVec.Simprocs

attribute [-simp] PMF.monad_bind_eq_bind PMF.monad_pure_eq_pure bind_pure_comp


noncomputable
def OTSToIndCpaReduction {PubK SecK M C : Type} (scheme : PubEncScheme PubK SecK M C) (i : ℕ) :
  SRReduction (IndCpaPubSpec PubK M C) (IndCpaPubSpec PubK M C) where
  stateType := ℕ
  initialState := pure 0
  queries := {
    impl := fun q input => match q, input with
      | .getPk, () => do
          srQuery(IndCpaPubQ.getPk, ())
      | .eavesdrop, (m₀, m₁) => do
          let n <- srGet!
          srSet(n + 1)
          if n > i then
            let pk <- srQuery(IndCpaPubQ.getPk, ())
            srSample(scheme.encrypt pk m₀)
          else if n = i then
            srQuery(IndCpaPubQ.eavesdrop, (m₀, m₁))
          else
            let pk <- srQuery(IndCpaPubQ.getPk, ())
            srSample(scheme.encrypt pk m₁)
  }

noncomputable
def OTSToIndCpaHybrid {PubK SecK M C : Type} (scheme : PubEncScheme PubK SecK M C) (i : ℕ) :
  RStateOracle (IndCpaPubSpec PubK M C) where
  stateType := ℕ × PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure (0, pk)
  queries := {
    impl := fun q input => match q, input with
      | .getPk, () => do
          let (_, pk) <- get
          pure pk
      | .eavesdrop, (m₀, m₁) => do
          let (n, pk) <- get
          modify (fun (_, pk) => (n + 1, pk))
          if n ≥ i then
            scheme.encrypt pk m₀
          else
            scheme.encrypt pk m₁
  }

def OTSHybridLeft {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) (i : ℕ) :
 ObsEq (applySRReduction (OTSToIndCpaReduction scheme i) (OneTimeSecrecyL scheme)) (OTSToIndCpaHybrid scheme i) := by
  apply ObsEq.symm
  refine correctAbstractionImpliesObsEq
    (OTSToIndCpaHybrid scheme i)
    (applySRReduction (OTSToIndCpaReduction scheme i) (OneTimeSecrecyL scheme))
    (fun st => (st.1, { pk := st.2, eavesdropDone := st.1 > i }))
    ?_
  constructor
  · simp only [OTSToIndCpaHybrid, OTSToIndCpaReduction, OneTimeSecrecyL, applySRReduction,
      GameHoppingSimplifyPMF, monad_norm, mapSecond]
    simp
  · intro q input
    ext1 st
    rcases st with ⟨n, pk⟩
    simp [IndCpaPubSpec, OracleSpec.domain] at input
    cases q with
    | getPk =>
        simp [mapOutputState, StateT.run, mapInputState, applySRReduction,
        OracleComp.simulateQ, FreeMonad.mapM, OTSToIndCpaReduction, FreeMonad.lift,
        GameHoppingSimplifyPMF, OTSToIndCpaHybrid, OneTimeSecrecyL]
    | eavesdrop =>
        rcases input with ⟨m₀, m₁⟩
        simp [mapOutputState, StateT.run, mapInputState, applySRReduction,
        OracleComp.simulateQ, FreeMonad.mapM, OTSToIndCpaReduction, FreeMonad.lift,
        GameHoppingSimplifyPMF, OTSToIndCpaHybrid, OneTimeSecrecyL]
        split_ifs with hlt hgt heq <;> try omega
        · simp [FreeMonad.roll, GameHoppingSimplifyPMF]
          rw [ite_cond_eq_true]
          rfl
          simp
          omega
        · simp [FreeMonad.roll, GameHoppingSimplifyPMF]
          rw [ite_cond_eq_true]
          rfl
          simp
          omega
        · simp [FreeMonad.roll, GameHoppingSimplifyPMF]
          rw [ite_cond_eq_false]
          rfl
          simp
          omega

def OTSHybridRight {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) (i : ℕ) :
 ObsEq (applySRReduction (OTSToIndCpaReduction scheme i) (OneTimeSecrecyR scheme)) (OTSToIndCpaHybrid scheme (i+1)) := by
  apply ObsEq.symm
  refine correctAbstractionImpliesObsEq
    (OTSToIndCpaHybrid scheme (i + 1))
    (applySRReduction (OTSToIndCpaReduction scheme i) (OneTimeSecrecyR scheme))
    (fun st => (st.1, { pk := st.2, eavesdropDone := st.1 > i }))
    ?_
  constructor
  · simp only [OTSToIndCpaHybrid, OTSToIndCpaReduction, OneTimeSecrecyR, applySRReduction,
      GameHoppingSimplifyPMF, monad_norm, mapSecond]
    simp
  · intro q input
    ext1 st
    rcases st with ⟨n, pk⟩
    simp [IndCpaPubSpec, OracleSpec.domain] at input
    cases q with
    | getPk =>
        simp [mapOutputState, StateT.run, mapInputState, applySRReduction,
        OracleComp.simulateQ, FreeMonad.mapM, OTSToIndCpaReduction, FreeMonad.lift,
        GameHoppingSimplifyPMF, OTSToIndCpaHybrid, OneTimeSecrecyR]
    | eavesdrop =>
        rcases input with ⟨m₀, m₁⟩
        simp [mapOutputState, StateT.run, mapInputState, applySRReduction,
        OracleComp.simulateQ, FreeMonad.mapM, OTSToIndCpaReduction, FreeMonad.lift,
        GameHoppingSimplifyPMF, OTSToIndCpaHybrid, OneTimeSecrecyR]
        split_ifs with hlt hgt heq <;> try omega
        · simp [FreeMonad.roll, GameHoppingSimplifyPMF]
          rw [ite_cond_eq_true]
          rfl
          simp
          omega
        · simp [FreeMonad.roll, GameHoppingSimplifyPMF]
          rw [ite_cond_eq_true]
          rfl
          simp
          omega
        · simp [FreeMonad.roll, GameHoppingSimplifyPMF]
          rw [ite_cond_eq_false]
          rfl
          simp
          omega

noncomputable def OTSToIndCpaHybridStep {PubK SecK M C : Type} [Inhabited C]
    (reductions : IndistinguishabilityReductions) (scheme : PubEncScheme PubK SecK M C) (i : ℕ)
  (hRed : (OTSToIndCpaReduction scheme i) ∈ (reductions.reductions (IndCpaPubSpec PubK M C) (IndCpaPubSpec PubK M C))) :
  Indistinguishable (OneTimeSecrecyAssumption' scheme) reductions (OTSToIndCpaHybrid scheme i) (OTSToIndCpaHybrid scheme (i+1)) := by
  intro κ
  let hLeft :
      IndistinguishableI (OneTimeSecrecyAssumption' scheme) reductions κ none
        (IndCpaPubSpec PubK M C)
        (OTSToIndCpaHybrid scheme i)
        (applySRReduction (OTSToIndCpaReduction scheme i) (OneTimeSecrecyL scheme)) :=
    Indistinguishable.symmetric <|
      Indistinguishable.of_ObsEq (OTSHybridLeft scheme i)
  let hOTS :
      IndistinguishableI (OneTimeSecrecyAssumption' scheme) reductions κ none
        (OneTimeSecrecySpec PubK M C)
        (OneTimeSecrecyL scheme)
        (OneTimeSecrecyR scheme) :=
    IndistinguishableI.assumption ()
  let hMiddle :
      IndistinguishableI (OneTimeSecrecyAssumption' scheme) reductions κ none
        (IndCpaPubSpec PubK M C)
        (applySRReduction (OTSToIndCpaReduction scheme i) (OneTimeSecrecyL scheme))
        (applySRReduction (OTSToIndCpaReduction scheme i) (OneTimeSecrecyR scheme)) :=
    IndistinguishableI.reduction (r := OTSToIndCpaReduction scheme i) none hOTS hRed
  let hRight :
      IndistinguishableI (OneTimeSecrecyAssumption' scheme) reductions κ none
        (IndCpaPubSpec PubK M C)
        (applySRReduction (OTSToIndCpaReduction scheme i) (OneTimeSecrecyR scheme))
        (OTSToIndCpaHybrid scheme (i + 1)) :=
    Indistinguishable.of_ObsEq (OTSHybridRight scheme i)
  exact Indistinguishable.transitive hLeft <|
    Indistinguishable.transitive hMiddle hRight

noncomputable
def OTSHybridsIndistinguishable {PubK SecK M C : Type} [Inhabited C]
    (Reductions : IndistinguishabilityReductions)
    (scheme : PubEncScheme PubK SecK M C)
    (i : ℕ)
    (hRed : forall i, (OTSToIndCpaReduction scheme i) ∈ (Reductions.reductions (IndCpaPubSpec PubK M C) (IndCpaPubSpec PubK M C))) :
    Indistinguishable (OneTimeSecrecyAssumption' scheme) Reductions
    (OTSToIndCpaHybrid scheme 0) (OTSToIndCpaHybrid scheme i) := by
    intro κ
    refine (Indistinguishable.long_step i (fun j => OTSToIndCpaHybrid scheme j) (OTSToIndCpaHybrid scheme 0) (OTSToIndCpaHybrid scheme i) (by rfl) (by rfl) ?_)
    intro i hi
    simp [ro_seq_fixed]
    apply OTSToIndCpaHybridStep
    apply hRed

def HybridZeroIndCpaL {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
  ObsEq (OTSToIndCpaHybrid scheme 0) (IndCpaPubL scheme) := by
  refine correctAbstractionImpliesObsEq
    (OTSToIndCpaHybrid scheme 0)
    (IndCpaPubL scheme)
    (fun st => st.2)
    ?_
  --simp [correctAbstraction]
  constructor
  · simp only [OTSToIndCpaHybrid, IndCpaPubL, applySRReduction,
      GameHoppingSimplifyPMF, monad_norm, mapSecond]
  · intro q input
    ext1 st
    rcases st with ⟨n, pk⟩
    simp [IndCpaPubSpec, OracleSpec.domain] at input
    cases q with
    | getPk =>
        simp [mapOutputState, StateT.run, mapInputState, applySRReduction,
        OracleComp.simulateQ, FreeMonad.mapM, OTSToIndCpaHybrid, IndCpaPubL]
    | eavesdrop =>
        rcases input with ⟨m₀, m₁⟩
        simp [mapOutputState, StateT.run, mapInputState, applySRReduction,
        OracleComp.simulateQ, FreeMonad.mapM, OTSToIndCpaHybrid, IndCpaPubL]
        simp [FreeMonad.roll, GameHoppingSimplifyPMF]

def HybridQIndCpaR {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) (q : ℕ) :
  ObsEqBounded (OTSToIndCpaHybrid scheme q) (IndCpaPubR scheme) q := by
  apply ObsEqBounded.symm
  refine correctAbstractionBImpliesObsEqBounded
    (IndCpaPubR scheme)
    (OTSToIndCpaHybrid scheme q)
    (fun n => fun st => ⟨q - n, st⟩ )
    q
    ?_
  constructor
  · simp only [OTSToIndCpaHybrid, IndCpaPubL, applySRReduction,
      GameHoppingSimplifyPMF, monad_norm, mapSecond, IndCpaPubR]
    simp
  · intro q input k
    cases q with
    | getPk =>
        apply Or.inr
        ext1 st
        simp [IndCpaPubR] at st
        simp [OracleSpec.domain, IndCpaPubSpec] at input
        simp [mapOutputState, StateT.run, mapInputState, applySRReduction,
        OracleComp.simulateQ, FreeMonad.mapM, OTSToIndCpaHybrid, IndCpaPubL,
        IndCpaPubR, GameHoppingSimplifyPMF]
    | eavesdrop =>
        rcases input with ⟨m₀, m₁⟩
        apply Or.inl
        ext1 st
        simp [IndCpaPubR] at st
        simp [mapOutputState, StateT.run, mapInputState, applySRReduction,
        OracleComp.simulateQ, FreeMonad.mapM, OTSToIndCpaHybrid, IndCpaPubL,
        IndCpaPubR, GameHoppingSimplifyPMF]
        rw [ite_cond_eq_false]
        simp[GameHoppingSimplifyPMF]
        · congr
          ext x
          congr
          omega
        · simp
          if h : q = 0 then
            apply Fin.elim0
            simp [h] at k
            assumption
          else
            exact Nat.zero_lt_of_ne_zero h

open scoped IndistinguishableI

/-- One-time secrecy implies public-key IND-CPA (for a fixed number of steps) -/
noncomputable def OneTimeSecrecyImpliesIndCPAPub
   (Reductions : IndistinguishabilityReductions)
    {PubK SecK M C : Type} (scheme : PubEncScheme PubK SecK M C) [Inhabited C]
    (hRed : ∀ i, (OTSToIndCpaReduction scheme i) ∈
      (Reductions.reductions (IndCpaPubSpec PubK M C) (IndCpaPubSpec PubK M C))) :
  IndCpaPubDefQ (OneTimeSecrecyAssumption' scheme) Reductions scheme := by
  intro κ q
  calc
    IndCpaPubL scheme
        ≈ᵢ[OneTimeSecrecyAssumption' scheme,Reductions,κ,q,IndCpaPubSpec PubK M C]
      OTSToIndCpaHybrid scheme 0 :=
        Indistinguishable.of_ObsEq (ObsEq.symm (HybridZeroIndCpaL scheme))
    _   ≈ᵢ[OneTimeSecrecyAssumption' scheme,Reductions,κ,none,IndCpaPubSpec PubK M C]
      OTSToIndCpaHybrid scheme q :=
        (OTSHybridsIndistinguishable Reductions scheme q hRed) κ
    _   ≈ᵢ[OneTimeSecrecyAssumption' scheme,Reductions,κ,q,IndCpaPubSpec PubK M C]
      IndCpaPubR scheme :=
        IndistinguishableI.obsEqB q (HybridQIndCpaR scheme q)
