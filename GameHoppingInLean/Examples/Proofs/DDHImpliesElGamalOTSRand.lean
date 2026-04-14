import GameHoppingInLean.Examples.SecurityDefintions.DecisionalDH
import GameHoppingInLean.Examples.SecurityDefintions.IndCpaRandPub
import GameHoppingInLean.Examples.SecurityDefintions.OneTimeSecrecy
import GameHoppingInLean.Examples.SecurityDefintions.OneTimeSecrecyRand
import GameHoppingInLean.Examples.Constructions.ElGamal
import GameHoppingInLean.Examples.Misc.Once
import GameHoppingInLean.FreeMonadLemmas
import GameHoppingInLean.PMFLiftOrder
import GameHoppingInLean.Misc.Isos
import GameHoppingInLean.Misc.PMFLemmas

open SRReduction
open RReduction

attribute [-simp] PMF.monad_bind_eq_bind PMF.monad_pure_eq_pure bind_pure_comp

section

def otsRandEavesdropIq : OneTimeSecrecyQ → Bool
  | .getPk => false
  | .eavesdrop => true

lemma obsEq_trans {I : Type} {O : OracleSpec I}
    {ro₁ ro₂ ro₃ : RStateOracle O} (h₁₂ : ObsEq ro₁ ro₂) (h₂₃ : ObsEq ro₂ ro₃) :
    ObsEq ro₁ ro₃ := by
  intro queriesList
  rw [h₁₂ queriesList, h₂₃ queriesList]

/-- The ElGamal randomness sampled on an `eavesdrop` query, factored out so it can
be moved between local and global scope. -/
noncomputable def elGamalLocalRandQuery {G : Type} [Group G] (g : G) (b : ℕ) :
    (i : OneTimeSecrecyQ) →
      (IndCpaRandPubSpec G G (G × G)).domain i →
      RState G ((IndCpaRandPubSpec G G (G × G)).range i)
  | .getPk, () => do
      get
  | .eavesdrop, (m : G) => do
      let pk <- get
      pure (g ^ b, m * pk ^ b)

/-- State used in the DDH-to-ElGamal OTS-rand reduction and the nearby explicit games. -/
structure DDHElGamalOTSState (G : Type) where
  pk : G
  B : G
  C : G
  eavesdropDone : Bool

def elGamalG0ToG1State {G : Type} [Group G] (g : G) :
    Bool × (ℕ × G) → DDHElGamalOTSState G × Unit
  | (eavesdropDone, (b, pk)) =>
      ({ pk := pk, B := g ^ b, C := pk ^ b, eavesdropDone := eavesdropDone }, ())

/-- Reduction from DDH to ElGamal one-time secrecy-rand. It uses the DDH oracle during
initialization to obtain `(A, B, C)`, then publishes `A` as the public key and answers the first
message query with `(B, m * C)`. -/
noncomputable def DDHToElGamalOTSRandReduction {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (_g : G) :
    ComplexInitReduction (DecisionalDHSpec G) (OneTimeSecrecyRandSpec G G (G × G)) where
  stateType := DDHElGamalOTSState G
  initialState := do
    let (A, B, C) <- RReduction.query DecisionalDHQ.querry ()
    pure { pk := A, B := B, C := C, eavesdropDone := false }
  queries := {
    impl i t := match i, t with
      | OneTimeSecrecyQ.getPk, () => do
          let st <- SRReduction.get
          pure st.pk
      | OneTimeSecrecyQ.eavesdrop, (m : G) => do
          let st <- SRReduction.get
          SRReduction.set { st with eavesdropDone := true }
          if !st.eavesdropDone then
            pure (st.B, m * st.C)
          else
            pure (default : G × G)
  }

/-- Game `G0`: the single ElGamal encryption randomness is sampled globally once and
reused through `once`, so this is definitionally the global-randomness hop. -/
noncomputable def ElGamalOTSRandG0 {G : Type} [Group G] [Fintype G] [Nontrivial G]
    [Inhabited G] (g : G) :
    RStateOracle (OneTimeSecrecyRandSpec G G (G × G)) :=
  once otsRandEavesdropIq
    (simpleGlobalRandomness
      (IndCpaRandPubReal (ElGamal g))
      otsRandEavesdropIq
      (sampleExponent G)
      (elGamalLocalRandQuery g))

/-- Game `G1`: compute `B` and `C` during initialization and answer the first
eavesdropping query with `(B, m * C)`. -/
noncomputable def ElGamalOTSRandG1 {G : Type} [Group G] [Fintype G] [Nontrivial G]
    [Inhabited G] (g : G) :
    RStateOracle (OneTimeSecrecyRandSpec G G (G × G)) where
  stateType := DDHElGamalOTSState G
  initialState := do
    let a <- sampleExponent G
    let b <- sampleExponent G
    let A := g ^ a
    let B := g ^ b
    let C := A ^ b
    pure { pk := A, B := B, C := C, eavesdropDone := false }
  queries := {
    impl := fun
      | OneTimeSecrecyQ.getPk, () => do
          let st <- get
          pure st.pk
      | OneTimeSecrecyQ.eavesdrop, (m : G) => do
          let st <- get
          set { st with eavesdropDone := true }
          if !st.eavesdropDone then
            pure (st.B, m * st.C)
          else
            pure (default : G × G)
  }

/-- Game `G3`: sample `a, b, c`, set `A = g^a`, `B = g^b`, `C = g^c`, then answer the first
message query with `(B, m * C)`. -/
noncomputable def ElGamalOTSRandG3 {G : Type} [Group G] [Fintype G] [Nontrivial G]
    [Inhabited G] (g : G) :
    RStateOracle (OneTimeSecrecyRandSpec G G (G × G)) where
  stateType := DDHElGamalOTSState G
  initialState := do
    let a <- sampleExponent G
    let b <- sampleExponent G
    let c <- sampleExponent G
    pure { pk := g ^ a, B := g ^ b, C := g ^ c, eavesdropDone := false }
  queries := {
    impl := fun
      | OneTimeSecrecyQ.getPk, () => do
          let st <- get
          pure st.pk
      | OneTimeSecrecyQ.eavesdrop, (m : G) => do
          let st <- get
          set { st with eavesdropDone := true }
          if !st.eavesdropDone then
            pure (st.B, m * st.C)
          else
            pure (default : G × G)
  }

/-- Game `G4`: sample the public key in initialization; on the first message query, sample
independent `b, c` and return `(g^b, m * g^c)`. -/
noncomputable def ElGamalOTSRandG4 {G : Type} [Group G] [Fintype G] [Nontrivial G]
    [Inhabited G] (g : G) :
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

/-- `OTSRandReal` for ElGamal is observationally equivalent to `G0`. -/
theorem obsEq_otsrRealElGamal_G0 {G : Type} [Group G] [Fintype G] [Nontrivial G]
    [Inhabited G] (g : G) :
    ObsEq (OneTimeSecrecyRandReal (ElGamal g)) (ElGamalOTSRandG0 g) := by
  have hCorrectAbstraction :
      correctAbstraction
        (OneTimeSecrecyRandReal (ElGamal g))
        (once otsRandEavesdropIq (IndCpaRandPubReal (ElGamal g)))
        (fun st => (st.eavesdropCount != 0, st.pk)) := by
    constructor
    · simp only [OneTimeSecrecyRandReal, once, OnceRed, IndCpaRandPubReal,
        applySRReduction, monad_norm, GameHoppingSimplifyPMF]
      rfl
    · intro i q
      ext1 st
      simp [once, OnceRed, applySRReduction, OneTimeSecrecyRandReal, mapInputState,
        mapOutputState, query_impl_convert, IndCpaRandPubReal]
      cases i
      case getPk =>
        cases q
        simp [otsRandEavesdropIq]
        simp [OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, RState.modify]
        simp only [GameHoppingSimplifyPMF, monad_norm, mapSecond]
      case eavesdrop =>
        simp [otsRandEavesdropIq]
        simp [OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, RState.modify]
        simp only [GameHoppingSimplifyPMF, monad_norm, mapSecond]
        split_ifs with h₁ <;> try simp [h₁]
        congr
        simp [h₁]

  have hObsEqRealOnce :
      ObsEq
        (OneTimeSecrecyRandReal (ElGamal g))
        (once otsRandEavesdropIq (IndCpaRandPubReal (ElGamal g))) := by
    exact correctAbstractionImpliesObsEq
      (OneTimeSecrecyRandReal (ElGamal g))
      (once otsRandEavesdropIq (IndCpaRandPubReal (ElGamal g)))
      (fun st => (st.eavesdropCount != 0, st.pk))
      hCorrectAbstraction

  have hOnceEq :
      once otsRandEavesdropIq (IndCpaRandPubReal (ElGamal g)) =
        once otsRandEavesdropIq
          (simpleLocalRandomness
            (IndCpaRandPubReal (ElGamal g))
            otsRandEavesdropIq
            (sampleExponent G)
            (elGamalLocalRandQuery g)) := by
    apply congr_arg
    simp [IndCpaRandPubReal, simpleLocalRandomness]
    ext q input
    congr 2
    split_ifs
    · simp
    · simp [elGamalLocalRandQuery]
      cases q
      case neg.getPk =>
        cases input
        simp
      case neg.eavesdrop =>
        simp [IndCpaRandPubSpec, OneTimeSecrecyRandSpec] at input
        symm
        simp [ElGamal]

  refine obsEq_trans
    hObsEqRealOnce
    (obsEq_trans
      (obsEqReflexive _ _ hOnceEq)
      ?_)
  simpa [ElGamalOTSRandG0] using
    (OnceRedSimpleRandomnesGlobalLocalObsEq
      otsRandEavesdropIq
      (IndCpaRandPubReal (ElGamal g))
      (sampleExponent G)
      (elGamalLocalRandQuery g))

/-- `G0` is observationally equivalent to the explicit initialization game `G1`. -/
theorem obsEq_G0_G1
    {G : Type} [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    ObsEq (ElGamalOTSRandG0 g) (ElGamalOTSRandG1 g) := by
  refine correctAbstractionImpliesObsEq
    (ElGamalOTSRandG0 g)
    (ElGamalOTSRandG1 g)
    (fun st => (elGamalG0ToG1State g st).1)
    ?_
  constructor
  · simp [ElGamalOTSRandG0, ElGamalOTSRandG1, once, OnceRed, simpleGlobalRandomness,
      IndCpaRandPubReal, ElGamal, applySRReduction, elGamalG0ToG1State,
      GameHoppingSimplifyPMF, monad_norm, mapSecond]
  · intro i query
    ext1 st
    rcases st with ⟨done, b, pk⟩
    cases i with
    | getPk =>
        cases query
        simp [ElGamalOTSRandG0, ElGamalOTSRandG1, once, OnceRed, simpleGlobalRandomness,
          IndCpaRandPubReal, ElGamal, applySRReduction, OracleComp.simulateQ,
          FreeMonad.mapM, FreeMonad.lift, query_impl_convert, elGamalLocalRandQuery,
          elGamalG0ToG1State, mapInputState, mapOutputState, otsRandEavesdropIq,
          RState.modify, GameHoppingSimplifyPMF, monad_norm, mapSecond]
    | eavesdrop =>
        cases done with
        | false =>
            simp [ElGamalOTSRandG0, ElGamalOTSRandG1, once, OnceRed, simpleGlobalRandomness,
            IndCpaRandPubReal, ElGamal, applySRReduction, OracleComp.simulateQ,
            FreeMonad.mapM, FreeMonad.lift, query_impl_convert, elGamalLocalRandQuery,
            elGamalG0ToG1State, mapInputState, mapOutputState, otsRandEavesdropIq,
            GameHoppingSimplifyPMF, monad_norm, mapSecond]
            rw [RState.run_modify]
            simp [GameHoppingSimplifyPMF]
        | true =>
            simp [ElGamalOTSRandG0, ElGamalOTSRandG1, once, OnceRed, simpleGlobalRandomness,
            IndCpaRandPubReal, ElGamal, applySRReduction, OracleComp.simulateQ,
            FreeMonad.mapM, FreeMonad.lift, query_impl_convert, elGamalLocalRandQuery,
            elGamalG0ToG1State, mapInputState, mapOutputState, otsRandEavesdropIq,
            RState.modify, GameHoppingSimplifyPMF, monad_norm, mapSecond]

/-- `OTSRandReal` for ElGamal is observationally equivalent to `G1`. -/
theorem obsEq_otsrRealElGamal_G1 {G : Type} [Group G] [Fintype G] [Nontrivial G]
    [Inhabited G] (g : G) :
    ObsEq (OneTimeSecrecyRandReal (ElGamal g)) (ElGamalOTSRandG1 g) := by
  exact obsEq_trans (obsEq_otsrRealElGamal_G0 g) (obsEq_G0_G1 g)

/-- `G1` is observationally equivalent to applying the DDH reduction to the real DDH oracle. -/
theorem obsEq_G1_applyComplexInit_dhReal
    {G : Type} [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
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
        simp [monad_norm, GameHoppingSimplifyPMF,
          OracleComp.simulateQ, FreeMonad.mapM, DDHToElGamalOTSRandReduction, dhReal,
          ElGamalOTSRandG1, RState.modify]
    | eavesdrop =>
        simp [DDHToElGamalOTSRandReduction]
        dsimp [applyComplexInitReduction]
        simp [query_impl_convert]
        simp [monad_norm, GameHoppingSimplifyPMF, OracleComp.simulateQ, FreeMonad.mapM,
          DDHToElGamalOTSRandReduction, dhReal, ElGamalOTSRandG1, RState.modify]

/-- Applying the DDH reduction to the random DDH oracle is observationally equivalent to `G3`. -/
theorem obsEq_applyComplexInit_dhRand_G3
    {G : Type} [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
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
        simp [monad_norm, GameHoppingSimplifyPMF,
          OracleComp.simulateQ, FreeMonad.mapM, DDHToElGamalOTSRandReduction, dhRand,
          ElGamalOTSRandG3, RState.modify]
    | eavesdrop =>
        simp [DDHToElGamalOTSRandReduction]
        dsimp [applyComplexInitReduction]
        simp [query_impl_convert]
        simp [monad_norm, GameHoppingSimplifyPMF, OracleComp.simulateQ, FreeMonad.mapM,
          DDHToElGamalOTSRandReduction, dhRand, ElGamalOTSRandG3, RState.modify]

private noncomputable def elGamalG3G4Rand {G : Type} [Group G] [Fintype G] [Nontrivial G]
    (g : G) : PMF (G × G) := do
  let b <- sampleExponent G
  let c <- sampleExponent G
  pure (g ^ b, g ^ c)

private noncomputable def elGamalG3G4LocalRandQuery {G : Type} [Group G]
    (bc : G × G) :
    (i : OneTimeSecrecyQ) →
      (IndCpaRandPubSpec G G (G × G)).domain i →
      RState G ((IndCpaRandPubSpec G G (G × G)).range i)
  | .getPk, () => do
      get
  | .eavesdrop, (m : G) => do
      pure (bc.1, m * bc.2)

private noncomputable def ElGamalOTSRandG3Global {G : Type} [Group G] [Fintype G] [Nontrivial G]
    [Inhabited G] (g : G) :
    RStateOracle (OneTimeSecrecyRandSpec G G (G × G)) :=
  once otsRandEavesdropIq
    (simpleGlobalRandomness
      (IndCpaRandPubReal (ElGamal g))
      otsRandEavesdropIq
      (elGamalG3G4Rand g)
      elGamalG3G4LocalRandQuery)

private noncomputable def ElGamalOTSRandG4Local {G : Type} [Group G] [Fintype G] [Nontrivial G]
    [Inhabited G] (g : G) :
    RStateOracle (OneTimeSecrecyRandSpec G G (G × G)) :=
  once otsRandEavesdropIq
    (simpleLocalRandomness
      (IndCpaRandPubReal (ElGamal g))
      otsRandEavesdropIq
      (elGamalG3G4Rand g)
      elGamalG3G4LocalRandQuery)

/-- Internal helper: `G3Global` is observationally equivalent to `G3`. -/
private theorem obsEq_G3Global_G3 {G : Type} [Group G] [Fintype G] [Nontrivial G]
    [Inhabited G] (g : G) :
    ObsEq (ElGamalOTSRandG3Global g) (ElGamalOTSRandG3 g) := by
  refine correctAbstractionImpliesObsEq
    (ElGamalOTSRandG3Global g)
    (ElGamalOTSRandG3 g)
    (fun st => { pk := st.2.2, B := st.2.1.1, C := st.2.1.2, eavesdropDone := st.1 })
    ?_
  constructor
  · simp [ElGamalOTSRandG3Global, ElGamalOTSRandG3, once, OnceRed, simpleGlobalRandomness,
      IndCpaRandPubReal, ElGamal, elGamalG3G4Rand, applySRReduction,
      GameHoppingSimplifyPMF, monad_norm, mapSecond]
  · intro i query
    ext1 st
    simp [once, OnceRed, applySRReduction, ElGamalOTSRandG3Global, ElGamalOTSRandG3,
      mapInputState, mapOutputState, query_impl_convert, simpleGlobalRandomness,
      IndCpaRandPubReal, elGamalG3G4LocalRandQuery]
    cases i
    case getPk =>
      cases query
      simp [otsRandEavesdropIq]
      simp [OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, RState.modify]
      simp only [GameHoppingSimplifyPMF, monad_norm, mapSecond]
    case eavesdrop =>
      cases h₁ : st.1 <;>
        simp [h₁, otsRandEavesdropIq, OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift,
          RState.modify, GameHoppingSimplifyPMF, monad_norm, mapSecond]

/-- Internal helper: `G4` is observationally equivalent to `G4Local`. -/
private theorem obsEq_G4_G4Local {G : Type} [Group G] [Fintype G] [Nontrivial G]
    [Inhabited G] (g : G) :
    ObsEq (ElGamalOTSRandG4 g) (ElGamalOTSRandG4Local g) := by
  refine correctAbstractionImpliesObsEq
    (ElGamalOTSRandG4 g)
    (ElGamalOTSRandG4Local g)
    (fun st => (st.eavesdropCount != 0, st.pk))
    ?_
  constructor
  · simp [ElGamalOTSRandG4, ElGamalOTSRandG4Local, once, OnceRed, simpleLocalRandomness,
      IndCpaRandPubReal, ElGamal, elGamalG3G4Rand, applySRReduction,
      GameHoppingSimplifyPMF, monad_norm, mapSecond]
  · intro i query
    ext1 st
    simp [once, OnceRed, applySRReduction, ElGamalOTSRandG4, ElGamalOTSRandG4Local,
      mapInputState, mapOutputState, query_impl_convert, IndCpaRandPubReal,
      simpleLocalRandomness, elGamalG3G4LocalRandQuery]
    cases i
    case getPk =>
      cases query
      simp [otsRandEavesdropIq]
      simp [OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, RState.modify]
      simp only [GameHoppingSimplifyPMF, monad_norm, mapSecond]
    case eavesdrop =>
      cases h₁ : st.eavesdropCount <;>
        simp [h₁, otsRandEavesdropIq, OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift,
          RState.modify, GameHoppingSimplifyPMF, monad_norm, mapSecond, elGamalG3G4Rand]

/-- `G3` is observationally equivalent to `G4`, where the computation of `B` and `C`
is moved back into the query implementation. -/
theorem obsEq_G3_G4 {G : Type} [Group G] [Fintype G] [Nontrivial G]
    [Inhabited G] (g : G) :
    ObsEq (ElGamalOTSRandG3 g) (ElGamalOTSRandG4 g) := by
  have hG3G3Global : ObsEq (ElGamalOTSRandG3 g) (ElGamalOTSRandG3Global g) := by
    intro queriesList
    symm
    exact (obsEq_G3Global_G3 g) queriesList
  have hGlobalLocal : ObsEq (ElGamalOTSRandG3Global g) (ElGamalOTSRandG4Local g) := by
    intro queriesList
    symm
    exact
      (OnceRedSimpleRandomnesGlobalLocalObsEq
        otsRandEavesdropIq
        (IndCpaRandPubReal (ElGamal g))
        (elGamalG3G4Rand g)
        elGamalG3G4LocalRandQuery) queriesList
  have hLocalG4 : ObsEq (ElGamalOTSRandG4Local g) (ElGamalOTSRandG4 g) := by
    intro queriesList
    symm
    exact (obsEq_G4_G4Local g) queriesList
  exact obsEq_trans hG3G3Global (obsEq_trans hGlobalLocal hLocalG4)

/-- `G4` is observationally equivalent to the random OTS-rand oracle for ElGamal. -/
theorem obsEq_G4_otsrRandElGamal {G : Type} [Group G] [Fintype G] [Nontrivial G]
    [Inhabited G] (g : G) (hgen : IsGenerator g) :
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

/-- DDH implies one-time secrecy-rand for ElGamal via the DDH reduction and the game hops above. -/
noncomputable def ddhImpliesElGamalOTSRand
    {Reductions : IndistinguishabilityReductions}
    {G : Type} [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G)
    (hgen : IsGenerator g)
    (hReduction : DDHToElGamalOTSRandReduction g ∈
      Reductions.complexInitReductions (DecisionalDHSpec G) (OneTimeSecrecyRandSpec G G (G × G)))
    : OneTimeSecrecyRandDef (DecisionalDHAssumption' g) Reductions (ElGamal g) := by
  intro κ
  have hRealRand :
      IndistinguishableI (DecisionalDHAssumption' g) Reductions κ none
        (DecisionalDHSpec G) (dhReal g) (dhRand g) := by
    simpa [DecisionalDHAssumption', DecisionalDHAssumptionFull, DecisionalDHAssumption] using
      (IndistinguishableI.assumption
        (Assumptions := DecisionalDHAssumption' g)
        (Reductions := Reductions) (κ := κ) (q_b := none) ())

  have h1 :
      IndistinguishableI (DecisionalDHAssumption' g) Reductions κ none
        (OneTimeSecrecyRandSpec G G (G × G))
        (OneTimeSecrecyRandReal (ElGamal g))
        (ElGamalOTSRandG1 g) :=
    Indistinguishable.of_ObsEq (obsEq_otsrRealElGamal_G1 g)

  have h2 :
      IndistinguishableI (DecisionalDHAssumption' g) Reductions κ none
        (OneTimeSecrecyRandSpec G G (G × G))
        (ElGamalOTSRandG1 g)
        (applyComplexInitReduction (DDHToElGamalOTSRandReduction g) (dhReal g)) :=
    Indistinguishable.of_ObsEq (obsEq_G1_applyComplexInit_dhReal g)

  have h3 :
      IndistinguishableI (DecisionalDHAssumption' g) Reductions κ none
        (OneTimeSecrecyRandSpec G G (G × G))
        (applyComplexInitReduction (DDHToElGamalOTSRandReduction g) (dhReal g))
        (applyComplexInitReduction (DDHToElGamalOTSRandReduction g) (dhRand g)) :=
    IndistinguishableI.complexInitReduction
      (r := DDHToElGamalOTSRandReduction g) none hRealRand hReduction

  have h4 :
      IndistinguishableI (DecisionalDHAssumption' g) Reductions κ none
        (OneTimeSecrecyRandSpec G G (G × G))
        (applyComplexInitReduction (DDHToElGamalOTSRandReduction g) (dhRand g))
        (ElGamalOTSRandG3 g) :=
    Indistinguishable.of_ObsEq (obsEq_applyComplexInit_dhRand_G3 g)

  have h5 :
      IndistinguishableI (DecisionalDHAssumption' g) Reductions κ none
        (OneTimeSecrecyRandSpec G G (G × G))
        (ElGamalOTSRandG3 g) (ElGamalOTSRandG4 g) :=
    Indistinguishable.of_ObsEq (obsEq_G3_G4 g)

  have h6 :
      IndistinguishableI (DecisionalDHAssumption' g) Reductions κ none
        (OneTimeSecrecyRandSpec G G (G × G))
        (ElGamalOTSRandG4 g)
        (OneTimeSecrecyRandRand (ElGamal g)) :=
    Indistinguishable.of_ObsEq (obsEq_G4_otsrRandElGamal g hgen)

  have h :
      IndistinguishableI (DecisionalDHAssumption' g) Reductions κ none
        (OneTimeSecrecyRandSpec G G (G × G))
        (OneTimeSecrecyRandReal (ElGamal g))
        (OneTimeSecrecyRandRand (ElGamal g)) :=
    Indistinguishable.transitive h1 <|
      Indistinguishable.transitive h2 <|
        Indistinguishable.transitive h3 <|
          Indistinguishable.transitive h4 <|
            Indistinguishable.transitive h5 h6

  simpa [OneTimeSecrecyRandDef] using h

end
