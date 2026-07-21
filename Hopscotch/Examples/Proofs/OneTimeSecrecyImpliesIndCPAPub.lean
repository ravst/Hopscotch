import Hopscotch.Examples.SecurityDefinitions.IndCPAPub
import Hopscotch.Examples.SecurityDefinitions.OneTimeSecrecy
import Hopscotch.Comp.OracleReductions
import Hopscotch.Tactic.Normalization.PMF.Simprocs
import Hopscotch.Tactic.Normalization.BitVec.Simprocs
import Hopscotch.Tactic.Defs
import Hopscotch.ObservationalEq.Defs

open scoped OracleReduction

noncomputable
def OTSToIndCpaReduction {PubK SecK M C : Type} (scheme : PubEncScheme PubK SecK M C) (i : ℕ) :
  OracleReduction (IndCpaPubSpec PubK M C) (IndCpaPubSpec PubK M C) where
  stateType := ℕ
  initialState := pure 0
  queries := fun input =>
      match input with
      | .getPk => do
          orQuery((IndCpaPubQ.getPk))
      | .eavesdrop (m₀, m₁) => do
          let n <- orGet!
          orSet(n + 1)
          if n > i then
            let pk <- orQuery(IndCpaPubQ.getPk)
            orSample(scheme.encrypt pk m₀)
          else if n = i then
            orQuery(IndCpaPubQ.eavesdrop (m₀, m₁))
          else
            let pk <- orQuery(IndCpaPubQ.getPk)
            orSample(scheme.encrypt pk m₁)


noncomputable
def OTSToIndCpaHybrid {PubK SecK M C : Type} (scheme : PubEncScheme PubK SecK M C) (i : ℕ) :
  OracleImpl (IndCpaPubSpec PubK M C) where
  stateType := ℕ × PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure (0, pk)
  queries := fun input => match input with
      | .getPk => do
          let (_, pk) <- get
          pure pk
      | .eavesdrop (m₀, m₁) => do
          let (n, pk) <- get
          set (n + 1, pk)
          if n > i then
            scheme.encrypt pk m₀
          else if n = i then
            scheme.encrypt pk m₀
          else
            scheme.encrypt pk m₁


attribute [local game_hopping_unfold]
  OTSToIndCpaHybrid
  OTSToIndCpaReduction
  OneTimeSecrecyL
  OneTimeSecrecyR
  IndCpaPubL
  IndCpaPubR
  PubEncScheme.encrypt

noncomputable
def OTSHybridsIndistinguishable {PubK SecK M C : Type} [Inhabited C]
    (scheme : PubEncScheme PubK SecK M C)
    (i : ℕ)
     :
    IndistinguishableSingle (OneTimeSecrecyAssumption' scheme)
    (OTSToIndCpaHybrid scheme 0) (OTSToIndCpaHybrid scheme i) := by
    refine (Indistinguishable.long_step i (fun j => OTSToIndCpaHybrid scheme j) (OTSToIndCpaHybrid scheme 0) (OTSToIndCpaHybrid scheme i) (by rfl) (by rfl) ?_)
    intro i hi
    game_hopping [
      OTSToIndCpaHybrid scheme i,
      (OTSToIndCpaReduction scheme i) ◇ (OneTimeSecrecyL scheme),
      (OTSToIndCpaReduction scheme i) ◇ (OneTimeSecrecyR scheme),
      OTSToIndCpaHybrid scheme (i + 1)
    ]
    · by_abstraction (fun st => (st.1, { pk := st.2, eavesdropDone := st.1 > i }))
      · congr; ext1 a; grind
      · congr; ext1 a; congr 4; grind
    · by_abstraction ← (fun st => (st.1, { pk := st.2, eavesdropDone := st.1 > i }))
      <;> try omega
      · congr 1; ext1 a; grind
      · congr 1; ext1 a; congr 4; grind

/-- Family version: one-time secrecy implies bounded public-key IND-CPA at every security parameter. -/
noncomputable def OneTimeSecrecyImpliesIndCPAPubQFam
    {PubK SecK M C : ℕ → Type}
    (schemeFam : PubEncSchemeFamily PubK SecK M C) [∀ κ, Inhabited (C κ)] :
    IndCpaPubBoundedIFam (OneTimeSecrecyAssumptionFam schemeFam) schemeFam := by
  intro q κ
  let scheme := schemeFam.scheme κ
  game_hopping [
    IndCpaPubL scheme,
    OTSToIndCpaHybrid scheme 0,
    OTSToIndCpaHybrid scheme q,
    IndCpaPubR scheme
  ]
  · by_abstraction ← (fun st => st.2)
  · apply Indistinguishable.indistinguishabilityIUnboundedToBounded q
    apply OTSHybridsIndistinguishable
  · apply IndistinguishableI.obsEqB
    symm
    refine (correctAbstractionBImpliesObsEqBounded _ _ (fun b => fun s => (q-b, s)) q ?_)
    constructor
    · simp [game_hopping_unfold, sPMF]
      rfl
    · intro q k
      cases q
      · apply Or.inr
        ext1 st
        simp [game_hopping_unfold, correctAbstractionDiagSimps, sRState, sPMF]
      · apply Or.inl
        ext1 st
        simp [game_hopping_unfold, correctAbstractionDiagSimps, sRState, sPMF]
        split_ifs <;> try grind
