import GameHoppingInLean.Examples.SecurityDefinitions.IndCPAPub
import GameHoppingInLean.Examples.SecurityDefinitions.OneTimeSecrecy
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.Normalization.PMF.Simprocs
import GameHoppingInLean.Normalization.BitVec.Simprocs
import GameHoppingInLean.IndistinguishabilityTactics
import GameHoppingInLean.ObservationalEquvialence

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
  RStateOracle (IndCpaPubSpec PubK M C) where
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
    Indistinguishable (OneTimeSecrecyAssumption' scheme)
    (OTSToIndCpaHybrid scheme 0) (OTSToIndCpaHybrid scheme i) := by
    intro κ
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
  intro κ q
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
    · simp [game_hopping_unfold, GameHoppingSimplifyPMF]
      rfl
    · intro q k
      cases q
      · apply Or.inr
        ext1 st
        simp [game_hopping_unfold, correctAbstractionDiagSimps, RStateSimplifier, GameHoppingSimplifyPMF]
      · apply Or.inl
        ext1 st
        simp [game_hopping_unfold, correctAbstractionDiagSimps, RStateSimplifier, GameHoppingSimplifyPMF]
        split_ifs <;> try grind



  -- · apply IndistinguishableI.obsEqB
  --   refine (correctAbstractionBoundImpliesObsEqBounded _ _ ?_  ?_ q ?_)
  --   · simp [game_hopping_unfold]
  --     exact (fun x => x.2)
  --   · simp [game_hopping_unfold]
  --     exact (fun x => q - x.1)
  --   · constructor
  --     · constructor
  --       · simp[game_hopping_unfold, GameHoppingSimplifyPMF]
  --       · constructor
  --         · simp [goodValuation, game_hopping_unfold]
  --           intro query
  --           cases query
  --           · intro a b
  --             simp [RStateSimplifier]
  --             have : q ≤ q - a + 1 + a := by omega
  --             exact_mod_cast this
  --           · intro a b
  --             simp [RStateSimplifier]
  --             split_ifs <;> try omega
  --             · intro x hx
  --               simp only [PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hx
  --               have ⟨a, ⟨b, c⟩ ⟩ := hx
  --               simp_all
  --               expose_names
  --               have : q ≤ q - (a_1 + 1) + 1 + a_1 := by omega
  --               exact_mod_cast this
  --             · intro x hx
  --               simp only [PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hx
  --               simp_all
  --             · intro x hx
  --               simp only [PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hx
  --               have ⟨a, ⟨b, c⟩ ⟩ := hx
  --               simp_all
  --               expose_names
  --               have : q ≤ q - (a_1 + 1) + 1 + a_1 := by omega
  --               exact_mod_cast this
  --         · intro q s hs
  --           simp at hs
  --           cases q
  --           · simp [game_hopping_unfold, correctAbstractionDiagSimps, RStateSimplifier, GameHoppingSimplifyPMF]
  --           · simp [game_hopping_unfold, correctAbstractionDiagSimps, RStateSimplifier, GameHoppingSimplifyPMF]
  --             split_ifs <;> try omega
  --             simp [GameHoppingSimplifyPMF]
  --     · simp only [game_hopping_unfold]
  --       intro x hx
  --       simp [GameHoppingSimplifyPMF]
  --       simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hx
  --       have ⟨a, ⟨ ha₁, ha₂⟩⟩ := hx
  --       simp_all
