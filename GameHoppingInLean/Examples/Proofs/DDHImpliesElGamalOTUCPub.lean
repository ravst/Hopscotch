import GameHoppingInLean.Examples.SecurityDefinitions.DecisionalDH
import GameHoppingInLean.Examples.SecurityDefinitions.OneTimeUniformCyphertextsPub
import GameHoppingInLean.Examples.Constructions.ElGamal

import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.IndistinguishabilityTactics
import GameHoppingInLean.Normalization.PMF.Simprocs
import GameHoppingInLean.Normalization.Group.Simprocs

open OracleReduction

attribute [-simp] PMF.monad_bind_eq_bind PMF.monad_pure_eq_pure bind_pure_comp

section

/-- State for the query-initialized ElGamal games.  The public key is optional
because initialization is delayed until the first oracle query.  The encryption
randomness is optional in the first bridge game so the correctness abstraction can
fill it with a fresh random value and then forget it in the next hop. -/
structure ElGamalQueryInitWithRandState (G : Type) where
  pk? : Option G
  eavesdropDone : Bool
  rand? : Option ℕ

/-- The same query-initialized state after the stored randomness has been erased. -/
structure ElGamalQueryInitState (G : Type) where
  pk? : Option G
  eavesdropDone : Bool

/-- State used by the DDH-backed reduction.  The DDH triple is requested lazily,
when the public-key or ciphertext query first needs it. -/
structure DDHElGamalLazyState (G : Type) where
  triple? : Option (G × G × G)
  eavesdropDone : Bool

/-- State for explicit games where the DDH-looking values are already materialized. -/
structure DDHElGamalState (G : Type) where
  pk : G
  B : G
  C : G
  eavesdropDone : Bool

private def ElGamalQueryInitWithRandState.forget {G : Type}
    (st : ElGamalQueryInitWithRandState G) : ElGamalQueryInitState G :=
  { pk? := st.pk?, eavesdropDone := st.eavesdropDone }

private def DDHElGamalLazyState.materialize {G : Type} [Inhabited G]
    (st : DDHElGamalLazyState G) : DDHElGamalState G :=
  match st.triple? with
  | some (A, B, C) => { pk := A, B := B, C := C, eavesdropDone := st.eavesdropDone }
  | none => { pk := default, B := default, C := default, eavesdropDone := st.eavesdropDone }

/-- ElGamal one-time uniform-ciphertexts real game, but with key generation delayed
until the first query and the first encryption randomness remembered in an
optional field. -/
noncomputable def ElGamalOTUCPubQueryInitWithRand {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    RStateOracle (OneTimeUniformCyphertextsPubSpec G G (G × G)) where
  stateType := ElGamalQueryInitWithRandState G
  initialState := pure { pk? := none, eavesdropDone := false, rand? := none }
  queries := fun
    | .getPk => do
        let st ← get
        match st.pk? with
        | some pk =>
            pure pk
        | none =>
            let a ← sampleExponent G
            let pk := g ^ a
            set { st with pk? := some pk }
            pure pk
    | .eavesdrop m => do
        let st ← get
        let pk ←
          match st.pk? with
          | some pk => pure pk
          | none => do
              let a ← sampleExponent G
              let pk := g ^ a
              set { st with pk? := some pk }
              pure pk
        let st ← get
        set { st with eavesdropDone := true }
        if !st.eavesdropDone then
          let r ← sampleExponent G
          set { st with eavesdropDone := true, rand? := some r }
          pure (g ^ r, m * pk ^ r)
        else
          pure (default : G × G)

/-- The same delayed-initialization ElGamal game, after the remembered
randomness has been erased. -/
noncomputable def ElGamalOTUCPubQueryInit {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    RStateOracle (OneTimeUniformCyphertextsPubSpec G G (G × G)) where
  stateType := ElGamalQueryInitState G
  initialState := pure { pk? := none, eavesdropDone := false }
  queries := fun
    | .getPk => do
        let st ← get
        match st.pk? with
        | some pk =>
            pure pk
        | none =>
            let a ← sampleExponent G
            let pk := g ^ a
            set { st with pk? := some pk }
            pure pk
    | .eavesdrop m => do
        let st ← get
        let pk ←
          match st.pk? with
          | some pk => pure pk
          | none => do
              let a ← sampleExponent G
              let pk := g ^ a
              set { st with pk? := some pk }
              pure pk
        let st ← get
        set { st with eavesdropDone := true }
        if !st.eavesdropDone then
          let r ← sampleExponent G
          pure (g ^ r, m * pk ^ r)
        else
          pure (default : G × G)

/-- Reduction from DDH to ElGamal OTUC public-key security.  Unlike the old
proof, this reduction does not use complex initialization to fetch the DDH tuple:
it asks the DDH oracle lazily inside the first public-key or message query. -/
noncomputable def DDHToElGamalOTUCPubReduction {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (_g : G) :
    OracleReduction (DecisionalDHSpec G) (OneTimeUniformCyphertextsPubSpec G G (G × G)) where
  stateType := DDHElGamalLazyState G
  initialState := pure { triple? := none, eavesdropDone := false }
  queries := fun
    | .getPk => do
        let st ← OracleReduction.get
        match st.triple? with
        | some (A, _B, _C) =>
            pure A
        | none => do
            let triple ← OracleReduction.query .query
            OracleReduction.set { st with triple? := some triple }
            pure triple.1
    | .eavesdrop m => do
        let st ← OracleReduction.get
        let triple ←
          match st.triple? with
          | some triple => pure triple
          | none => do
              let triple ← OracleReduction.query .query
              OracleReduction.set { st with triple? := some triple }
              pure triple
        let st ← OracleReduction.get
        OracleReduction.set { st with eavesdropDone := true }
        if !st.eavesdropDone then
          pure (triple.2.1, m * triple.2.2)
        else
          pure (default : G × G)

/-- Explicit real-DDH game corresponding to the lazy reduction applied to
`dhReal`. -/
noncomputable def ElGamalOTUCPubDDHRealGame {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    RStateOracle (OneTimeUniformCyphertextsPubSpec G G (G × G)) where
  stateType := DDHElGamalState G
  initialState := do
    let a ← sampleExponent G
    let b ← sampleExponent G
    let A := g ^ a
    pure { pk := A, B := g ^ b, C := A ^ b, eavesdropDone := false }
  queries := fun
    | .getPk => do
        let st ← get
        pure st.pk
    | .eavesdrop m => do
        let st ← get
        set { st with eavesdropDone := true }
        if !st.eavesdropDone then
          pure (st.B, m * st.C)
        else
          pure (default : G × G)

/-- Explicit random-DDH game corresponding to the lazy reduction applied to
`dhRand`. -/
noncomputable def ElGamalOTUCPubDDHRandGame {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    RStateOracle (OneTimeUniformCyphertextsPubSpec G G (G × G)) where
  stateType := DDHElGamalState G
  initialState := do
    let a ← sampleExponent G
    let b ← sampleExponent G
    let c ← sampleExponent G
    pure { pk := g ^ a, B := g ^ b, C := g ^ c, eavesdropDone := false }
  queries := fun
    | .getPk => do
        let st ← get
        pure st.pk
    | .eavesdrop m => do
        let st ← get
        set { st with eavesdropDone := true }
        if !st.eavesdropDone then
          pure (st.B, m * st.C)
        else
          pure (default : G × G)

/-- Game with random ciphertext components sampled in the query, matching the
shape of `OneTimeUniformCyphertextsPubRand (ElGamal g)`. -/
noncomputable def ElGamalOTUCPubRandQueryGame {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    RStateOracle (OneTimeUniformCyphertextsPubSpec G G (G × G)) where
  stateType := ElGamalQueryInitState G
  initialState := pure { pk? := none, eavesdropDone := false }
  queries := fun
    | .getPk => do
        let st ← get
        match st.pk? with
        | some pk =>
            pure pk
        | none =>
            let a ← sampleExponent G
            let pk := g ^ a
            set { st with pk? := some pk }
            pure pk
    | .eavesdrop m => do
        let st ← get
        set { st with eavesdropDone := true }
        if !st.eavesdropDone then
          let b ← sampleExponent G
          let c ← sampleExponent G
          pure (g ^ b, m * g ^ c)
        else
          pure (default : G × G)

/-- First bridge: delay key generation into the query layer and remember the
first encryption randomness. -/
theorem obsEq_real_queryInitWithRand {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    ObsEq (OneTimeUniformCyphertextsPubReal (ElGamal g))
      (ElGamalOTUCPubQueryInitWithRand g) := by
  sorry

/-- Correct-abstraction bridge: fill the optional randomness field with a fresh
random value and then erase it. -/
theorem obsEq_queryInitWithRand_queryInit {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    ObsEq (ElGamalOTUCPubQueryInitWithRand g)
      (ElGamalOTUCPubQueryInit g) := by
  sorry

/-- The delayed-initialization ElGamal game is the lazy DDH reduction applied to
the real DDH oracle. -/
theorem obsEq_queryInit_applyReduction_dhReal {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    ObsEq (ElGamalOTUCPubQueryInit g)
      (OracleReduction.apply (DDHToElGamalOTUCPubReduction g) (dhReal g)) := by
  sorry

/-- Expanding the lazy reduction over the random DDH oracle gives the explicit
random-DDH game. -/
theorem obsEq_applyReduction_dhRand_DDHRandGame {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    ObsEq (OracleReduction.apply (DDHToElGamalOTUCPubReduction g) (dhRand g))
      (ElGamalOTUCPubDDHRandGame g) := by
  sorry

/-- Move the random DDH components from initialization back into the first
message query. -/
theorem obsEq_DDHRandGame_randQueryGame {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    ObsEq (ElGamalOTUCPubDDHRandGame g)
      (ElGamalOTUCPubRandQueryGame g) := by
  sorry

/-- The query-random game is the random one-time uniform-ciphertexts public-key
oracle for ElGamal. -/
theorem obsEq_randQueryGame_rand {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) (hgen : IsGenerator g) :
    ObsEq (ElGamalOTUCPubRandQueryGame g)
      (OneTimeUniformCyphertextsPubRand (ElGamal g)) := by
  sorry

attribute [local game_hopping_unfold]
  OneTimeUniformCyphertextsPubDef
  OneTimeUniformCyphertextsPubReal
  OneTimeUniformCyphertextsPubRand
  OneTimeUniformCyphertextsPubSpec
  DecisionalDHSpec
  dhReal
  dhRand
  ElGamal
  ElGamalOTUCPubQueryInitWithRand
  ElGamalOTUCPubQueryInit
  DDHToElGamalOTUCPubReduction
  ElGamalOTUCPubDDHRealGame
  ElGamalOTUCPubDDHRandGame
  ElGamalOTUCPubRandQueryGame

/-- DDH implies one-time uniform-ciphertexts public-key security for ElGamal,
via the lazy-query DDH reduction and the no-`once` game chain above. -/
noncomputable def ddhImpliesElGamalOTUCPub
    {G : Type} [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G)
    (hgen : IsGenerator g) :
    OneTimeUniformCyphertextsPubDef (DecisionalDHAssumption' g) (ElGamal g) := by
  intro κ
  game_hopping [
    OneTimeUniformCyphertextsPubReal (ElGamal g),
    ElGamalOTUCPubQueryInitWithRand g,
    ElGamalOTUCPubQueryInit g,
    OracleReduction.apply (DDHToElGamalOTUCPubReduction g) (dhReal g),
    OracleReduction.apply (DDHToElGamalOTUCPubReduction g) (dhRand g),
    ElGamalOTUCPubDDHRandGame g,
    ElGamalOTUCPubRandQueryGame g,
    OneTimeUniformCyphertextsPubRand (ElGamal g)
  ] using GH_group_nom
  · by_rand_abstraction ← (fun st =>
      match st.pk? with
      | some pk =>
          pure
            ({ pk := pk, eavesdropCount := if st.eavesdropDone then 1 else 0 } :
              OneTimeSecrecyState G)
      | none => do
          let (pk, _sk) ← (ElGamal g).keyGen
          pure
            ({ pk := pk, eavesdropCount := if st.eavesdropDone then 1 else 0 } :
              OneTimeSecrecyState G))
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  · exact Indistinguishable.of_ObsEq (obsEq_queryInitWithRand_queryInit g)
  · exact Indistinguishable.of_ObsEq (obsEq_queryInit_applyReduction_dhReal g)
  · exact Indistinguishable.of_ObsEq (obsEq_applyReduction_dhRand_DDHRandGame g)
  · exact Indistinguishable.of_ObsEq (obsEq_DDHRandGame_randQueryGame g)
  · exact Indistinguishable.of_ObsEq (obsEq_randQueryGame_rand g hgen)

end
