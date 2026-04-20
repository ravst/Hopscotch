import GameHoppingInLean.Examples.SecurityDefinitions.IndCPAPub
import GameHoppingInLean.Examples.SecurityDefinitions.OneTimeSecrecy
import GameHoppingInLean.OracleReductions

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
          if n < i then
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
          if n < i then
            scheme.encrypt pk m₀
          else
            scheme.encrypt pk m₁
  }

def OTSHybridLeft {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) (i : ℕ) :
 ObsEq (applySRReduction (OTSToIndCpaReduction scheme i) (OneTimeSecrecyL scheme)) (OTSToIndCpaHybrid scheme i) := by
  sorry

def OTSHybridRight {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) (i : ℕ) :
 ObsEq (applySRReduction (OTSToIndCpaReduction scheme i) (OneTimeSecrecyR scheme)) (OTSToIndCpaHybrid scheme (i+1)) := by
  sorry

noncomputable def OTSToIndCpaHybridStep {PubK SecK M C : Type} [Inhabited C]
    (reductions : IndistinguishabilityReductions) (scheme : PubEncScheme PubK SecK M C) (i : ℕ)
  (hRed : (OTSToIndCpaReduction scheme i) ∈ (reductions.reductions (IndCpaPubSpec PubK M C) (IndCpaPubSpec PubK M C))) :
  Indistinguishable (OneTimeSecrecyAssumption' scheme) reductions (IndCpaPubSpec PubK M C) (OTSToIndCpaHybrid scheme i) (OTSToIndCpaHybrid scheme (i+1)) := by
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

/-- One-time secrecy implies public-key IND-CPA (for a fixed number of steps) -/
def OneTimeSecrecyImpliesIndCPAPub
   (Assumptions : IndistinguishabilityAssumptions)
   (Reductions : IndistinguishabilityReductions)
    {PubK SecK M C : Type} (scheme : PubEncScheme PubK SecK M C) [Inhabited C]
  (h : OneTimeSecrecyDef Assumptions Reductions scheme) :
  IndCpaPubDefQ Assumptions Reductions scheme := by sorry
