import GameHoppingInLean.Examples.SecurityDefintions.DecisionalDH
import GameHoppingInLean.Examples.SecurityDefintions.OneTimeSecrecy
import GameHoppingInLean.Examples.SecurityDefintions.OneTimeSecrecyRand
import GameHoppingInLean.Examples.Constructions.ElGamal
import GameHoppingInLean.Misc.Isos
import GameHoppingInLean.Misc.PMFLemmas

open SRReduction
open RReduction

attribute [-simp] PMF.monad_bind_eq_bind PMF.monad_pure_eq_pure

section

local instance {G : Type} [One G] : Inhabited (G × G) := ⟨(1, 1)⟩

/-- State used in the DDH-to-ElGamal OTS-rand reduction and the nearby explicit games. -/
structure DDHElGamalOTSState (G : Type) where
  pk : G
  B : G
  C : G
  eavesdropCount : ℕ

/-- Reduction from DDH to ElGamal one-time secrecy-rand. It uses the DDH oracle during
initialization to obtain `(A, B, C)`, then publishes `A` as the public key and answers the first
message query with `(B, m * C)`. -/
noncomputable def DDHToElGamalOTSRandReduction {G : Type}
    [Group G] [Fintype G] [Nontrivial G] (_g : G) :
    ComplexInitReduction (DecisionalDHSpec G) (OneTimeSecrecyRandSpec G G (G × G)) where
  stateType := DDHElGamalOTSState G
  initialState := do
    let (A, B, C) <- RReduction.query DecisionalDHQ.querry ()
    pure { pk := A, B := B, C := C, eavesdropCount := 0 }
  queries := {
    impl i t := match i, t with
      | OneTimeSecrecyQ.getPk, () => do
          let st <- SRReduction.get
          pure st.pk
      | OneTimeSecrecyQ.eavesdrop, (m : G) => do
          let st <- SRReduction.get
          SRReduction.set { st with eavesdropCount := st.eavesdropCount + 1 }
          if st.eavesdropCount = 0 then
            pure (st.B, m * st.C)
          else
            pure (default : G × G)
  }

/-- Game `G1`: Computing B and C has been moved from eavsdrop to initialization  --/
noncomputable def ElGamalOTSRandG1 {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) :
    RStateOracle (OneTimeSecrecyRandSpec G G (G × G)) where
  stateType := DDHElGamalOTSState G
  initialState := do
    let a <- sampleExponent G
    let b <- sampleExponent G
    let A := g ^ a
    let B := g ^ b
    let C := A ^ b
    pure { pk := A, B := B, C := C, eavesdropCount := 0 }
  queries := {
    impl := fun
      | OneTimeSecrecyQ.getPk, () => do
          let st <- get
          pure st.pk
      | OneTimeSecrecyQ.eavesdrop, (m : G) => do
          let st <- get
          set { st with eavesdropCount := st.eavesdropCount + 1 }
          if st.eavesdropCount = 0 then
            pure (st.B, m * st.C)
          else
            pure (default : G × G)
  }

/-- Game `G3`: sample `a, b, c`, set `A = g^a`, `B = g^b`, `C = g^c`, then answer the first
message query with `(B, m * C)`. -/
noncomputable def ElGamalOTSRandG3 {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) :
    RStateOracle (OneTimeSecrecyRandSpec G G (G × G)) where
  stateType := DDHElGamalOTSState G
  initialState := do
    let a <- sampleExponent G
    let b <- sampleExponent G
    let c <- sampleExponent G
    pure { pk := g ^ a, B := g ^ b, C := g ^ c, eavesdropCount := 0 }
  queries := {
    impl := fun
      | OneTimeSecrecyQ.getPk, () => do
          let st <- get
          pure st.pk
      | OneTimeSecrecyQ.eavesdrop, (m : G) => do
          let st <- get
          set { st with eavesdropCount := st.eavesdropCount + 1 }
          if st.eavesdropCount = 0 then
            pure (st.B, m * st.C)
          else
            pure (default : G × G)
  }

/-- Game `G4`: sample the public key in initialization; on the first message query, sample
independent `b, c` and return `(g^b, m * g^c)`. -/
noncomputable def ElGamalOTSRandG4 {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) :
    RStateOracle (OneTimeSecrecyRandSpec G G (G × G)) where
  stateType := OneTimeSecrecyState G
  initialState := do
    let (pk, _sk) <- (ElGamal g).keyGen
    pure { pk := pk, eavesdropCount := 0 }
  queries := {
    impl := fun
      | OneTimeSecrecyQ.getPk, () => do
          let st <- get
          pure st.pk
      | OneTimeSecrecyQ.eavesdrop, (m : G) => do
          let st <- get
          set { st with eavesdropCount := st.eavesdropCount + 1 }
          if st.eavesdropCount = 0 then
            let b <- sampleExponent G
            let c <- sampleExponent G
            pure (g ^ b, m * g ^ c)
          else
            pure (default : G × G)
  }

/-- `OTSRandReal` for ElGamal is observationally equivalent to `G1`. -/
theorem obsEq_otsrRealElGamal_G1 {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) :
    ObsEq (OneTimeSecrecyRandReal (ElGamal g)) (ElGamalOTSRandG1 g) := by
  sorry

/-- `G1` is observationally equivalent to applying the DDH reduction to the real DDH oracle. -/
theorem obsEq_G1_applyComplexInit_dhReal
    {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) :
    ObsEq (ElGamalOTSRandG1 g)
      (applyComplexInitReduction (DDHToElGamalOTSRandReduction g) (dhReal g)) := by
  refine existsMapStateBijImpliesObsEq
    (ro₁ := ElGamalOTSRandG1 g)
    (ro₂ := applyComplexInitReduction (DDHToElGamalOTSRandReduction g) (dhReal g))
    ?_
  refine ⟨(Equiv.prodUnit _).symm, ?_, ?_⟩
  · simp [GameHoppingSimplifyPMF, ElGamalOTSRandG1, applyComplexInitReduction,
      DDHToElGamalOTSRandReduction, dhReal, OracleComp.simulateQ, FreeMonad.mapM,
      query_impl_convert, pow_mul]
  · intro i query
    cases i with
    | getPk =>
        cases query
        simp [DDHToElGamalOTSRandReduction]
        dsimp [applyComplexInitReduction]
        simp [query_impl_convert]
        simp [monad_norm, GameHoppingSimplifyPMF, OracleComp.simulateQ, FreeMonad.mapM,
          DDHToElGamalOTSRandReduction, dhReal, ElGamalOTSRandG1, RState.modify]
    | eavesdrop =>
        simp [DDHToElGamalOTSRandReduction]
        dsimp [applyComplexInitReduction]
        simp [query_impl_convert]
        simp [monad_norm, GameHoppingSimplifyPMF, OracleComp.simulateQ, FreeMonad.mapM,
          DDHToElGamalOTSRandReduction, dhReal, ElGamalOTSRandG1, RState.modify]

/-- Applying the DDH reduction to the random DDH oracle is observationally equivalent to `G3`. -/
theorem obsEq_applyComplexInit_dhRand_G3
    {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) :
    ObsEq (applyComplexInitReduction (DDHToElGamalOTSRandReduction g) (dhRand g))
      (ElGamalOTSRandG3 g) := by
  refine existsMapStateBijImpliesObsEq
    (ro₁ := applyComplexInitReduction (DDHToElGamalOTSRandReduction g) (dhRand g))
    (ro₂ := ElGamalOTSRandG3 g)
    ?_
  refine ⟨Equiv.prodUnit _, ?_, ?_⟩
  · simp [GameHoppingSimplifyPMF, ElGamalOTSRandG3, applyComplexInitReduction,
      DDHToElGamalOTSRandReduction, dhRand, OracleComp.simulateQ, FreeMonad.mapM,
      query_impl_convert]
  · intro i query
    cases i with
    | getPk =>
        cases query
        simp [DDHToElGamalOTSRandReduction]
        dsimp [applyComplexInitReduction]
        simp [query_impl_convert]
        simp [monad_norm, GameHoppingSimplifyPMF, OracleComp.simulateQ, FreeMonad.mapM,
          DDHToElGamalOTSRandReduction, dhRand, ElGamalOTSRandG3, RState.modify]
    | eavesdrop =>
        simp [DDHToElGamalOTSRandReduction]
        dsimp [applyComplexInitReduction]
        simp [query_impl_convert]
        simp [monad_norm, GameHoppingSimplifyPMF, OracleComp.simulateQ, FreeMonad.mapM,
          DDHToElGamalOTSRandReduction, dhRand, ElGamalOTSRandG3, RState.modify]

/-- `G3` is observationally equivalent to `G4`, where the computation of `B` and `C`
is moved back into the query implementation. -/
theorem obsEq_G3_G4 {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) :
    ObsEq (ElGamalOTSRandG3 g) (ElGamalOTSRandG4 g) := by
  sorry

/-- `G4` is observationally equivalent to the random OTS-rand oracle for ElGamal. -/
theorem obsEq_G4_otsrRandElGamal {G : Type} [Group G] [Fintype G] [Nontrivial G]
    (g : G) (hgen : IsGenerator g) :
    ObsEq (ElGamalOTSRandG4 g)
      (OneTimeSecrecyRandRand (ElGamal g)) := by
  apply obsEqReflexive
  simp [ElGamalOTSRandG4, OneTimeSecrecyRandRand, ElGamal]
  ext1 α
  cases α with
  | getPk =>
      ext1 q
      cases q
      simp
  | eavesdrop =>
      ext1 m
      simp [GameHoppingSimplifyPMF, GH_group_nom, hgen]
      ext1 st
      simp [GameHoppingSimplifyPMF, GH_group_nom, hgen]

/-- DDH implies one-time secrecy-rand for ElGamal via the DDH reduction and the game hops above. -/
theorem ddhImpliesElGamalOTSRand
    {Assumptions : IndistinguishabilityAssumptions}
    {Reductions : IndistinguishabilityReductions}
    {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G)
    (hgen : IsGenerator g)
    (hReduction : DDHToElGamalOTSRandReduction g ∈
      Reductions.complexInitReductions (DecisionalDHSpec G) (OneTimeSecrecyRandSpec G G (G × G)))
    (hDDH : DecisionalDHDef Assumptions Reductions g) :
    OneTimeSecrecyRandDef Assumptions Reductions (ElGamal g) := by
  have hRealRand :
      Indistinguishable Assumptions Reductions
        (DecisionalDHSpec G) (dhReal g) (dhRand g) := by
    simpa [DecisionalDHDef] using hDDH

  have h1 :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecyRandSpec G G (G × G))
        (OneTimeSecrecyRandReal (ElGamal g))
        (ElGamalOTSRandG1 g) :=
    Indistinguishable.of_ObsEq (obsEq_otsrRealElGamal_G1 g)

  have h2 :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecyRandSpec G G (G × G))
        (ElGamalOTSRandG1 g)
        (applyComplexInitReduction (DDHToElGamalOTSRandReduction g) (dhReal g)) :=
    Indistinguishable.of_ObsEq (obsEq_G1_applyComplexInit_dhReal g)

  have h3 :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecyRandSpec G G (G × G))
        (applyComplexInitReduction (DDHToElGamalOTSRandReduction g) (dhReal g))
        (applyComplexInitReduction (DDHToElGamalOTSRandReduction g) (dhRand g)) :=
    Indistinguishable.complexInitReduction
      (r := DDHToElGamalOTSRandReduction g) hRealRand hReduction

  have h4 :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecyRandSpec G G (G × G))
        (applyComplexInitReduction (DDHToElGamalOTSRandReduction g) (dhRand g))
        (ElGamalOTSRandG3 g) :=
    Indistinguishable.of_ObsEq (obsEq_applyComplexInit_dhRand_G3 g)

  have h5 :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecyRandSpec G G (G × G))
        (ElGamalOTSRandG3 g) (ElGamalOTSRandG4 g) :=
    Indistinguishable.of_ObsEq (obsEq_G3_G4 g)

  have h6 :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecyRandSpec G G (G × G))
        (ElGamalOTSRandG4 g)
        (OneTimeSecrecyRandRand (ElGamal g)) :=
    Indistinguishable.of_ObsEq (obsEq_G4_otsrRandElGamal g hgen)

  have h :
      Indistinguishable Assumptions Reductions
        (OneTimeSecrecyRandSpec G G (G × G))
        (OneTimeSecrecyRandReal (ElGamal g))
        (OneTimeSecrecyRandRand (ElGamal g)) :=
    Indistinguishable.trans h1 <|
      Indistinguishable.trans h2 <|
        Indistinguishable.trans h3 <|
          Indistinguishable.trans h4 <|
            Indistinguishable.trans h5 h6

  simpa [OneTimeSecrecyRandDef] using h

end
