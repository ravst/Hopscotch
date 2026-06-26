import GameHoppingInLean.Examples.SecurityDefinitions.DecisionalDH
import GameHoppingInLean.Examples.SecurityDefinitions.OneTimeUniformCyphertextsPub
import GameHoppingInLean.Examples.Constructions.ElGamal

import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.IndistinguishabilityTactics
import GameHoppingInLean.Normalization.PMF.Simprocs
import GameHoppingInLean.Normalization.Group.Simprocs

open OracleReduction

structure ElGamalRealState (G : Type) where
  (a b : ℕ)
  (A B C : G)
  eavesdropDone : Bool

noncomputable def G1 {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    RStateOracle (OneTimeUniformCyphertextsPubSpec G G (G × G)) where
  stateType := ElGamalRealState G
  initialState := do
    let a <- sampleExponent G
    pure {
      a := a
      b := default
      A := g ^ a
      B := default
      C := default
      eavesdropDone := false
    }
  queries:= fun
    | .getPk => do
      let st <- get
      pure st.A
    | .eavesdrop m => do
      let st <- get
      if not st.eavesdropDone then
        let b <- sampleExponent G
        let B := g ^ b
        let C := st.A ^ b
        set {st with eavesdropDone := true, b := b, B := B, C := C}
        pure (B, m * C)
      else
        pure default


noncomputable def G2 {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    RStateOracle (OneTimeUniformCyphertextsPubSpec G G (G × G)) where
  stateType := ElGamalRealState G
  initialState := do
    let a <- sampleExponent G
    let b <- sampleExponent G
    pure {
      a := a
      b := b
      A := g ^ a
      B := g ^ b
      C := (g ^ a)^b
      eavesdropDone := false
    }
  queries:= fun
    | .getPk => do
      let st <- get
      pure st.A
    | .eavesdrop m => do
      let st <- get
      if not st.eavesdropDone then
        set {st with eavesdropDone := true}
        pure (st.B, m * st.C)
      else
        pure default

noncomputable
def G1toG2Abstraction {G : Type} [Group G] [Fintype G] [Inhabited G] [Nontrivial G] (g : G) (s : ElGamalRealState G) : PMF (ElGamalRealState G) :=
  if s.eavesdropDone then pure s else do
    let b ← sampleExponent G
    pure { s with
      b := b
      B := g ^ b
      C := (s.A)^b
    }

structure ElGamalToDDHReductionState (G : Type) where
  (A B C : G)
  eavesdropDone : Bool

/-- Reduction from DDH to ElGamal OTUC public-key security.  Unlike the old
proof, this reduction does not use complex initialization to fetch the DDH tuple:
it asks the DDH oracle lazily inside the first public-key or message query. -/
noncomputable def DDHToElGamalOTUCPubReduction (G : Type)
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] :
    OracleReduction (DecisionalDHSpec G) (OneTimeUniformCyphertextsPubSpec G G (G × G)) where
  stateType := ElGamalToDDHReductionState G
  initialState := do
    let (A, B, C) ← initQuery DecisionalDHQ.query
    pure {A := A, B := B, C := C, eavesdropDone := false}
  queries := fun
    | .getPk => do
        let st ← OracleReduction.get
        pure st.A
    | .eavesdrop m => do
      let st <- get
      if not st.eavesdropDone then
        set {st with eavesdropDone := true}
        pure (st.B, m * st.C)
      else
        pure default

structure ElGamalRandState (G : Type) where
  (a b c : ℕ)
  (A B C : G)
  eavesdropDone : Bool

noncomputable def G3 {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    RStateOracle (OneTimeUniformCyphertextsPubSpec G G (G × G)) where
  stateType := ElGamalRandState G
  initialState := do
    let a <- sampleExponent G
    let b <- sampleExponent G
    let c <- sampleExponent G
    pure {
      a := a
      b := b
      c := c
      A := g ^ a
      B := g ^ b
      C := g ^ c
      eavesdropDone := false
    }
  queries:= fun
    | .getPk => do
      let st <- get
      pure st.A
    | .eavesdrop m => do
      let st <- get
      if not st.eavesdropDone then
        set {st with eavesdropDone := true}
        pure (st.B, m * st.C)
      else
        pure default

noncomputable def G4 {G : Type}
    [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G) :
    RStateOracle (OneTimeUniformCyphertextsPubSpec G G (G × G)) where
  stateType := ElGamalRandState G
  initialState := do
    let a <- sampleExponent G
    pure {
      a := a
      b := default
      c := default
      A := g ^ a
      B := default
      C := default
      eavesdropDone := false
    }
  queries:= fun
    | .getPk => do
      let st <- get
      pure st.A
    | .eavesdrop m => do
      let st <- get
      if not st.eavesdropDone then
        let b <- sampleExponent G
        let c <- sampleExponent G
        let B := g ^ b
        let C := g ^ c
        set {st with eavesdropDone := true, B := B, C := C, b := b, c := c}
        pure (B, m * C)
      else
        pure default

noncomputable
def G4toG3Abstraction {G : Type} [Group G] [Fintype G] [Inhabited G] [Nontrivial G] (g : G) (s : ElGamalRandState G) : PMF (ElGamalRandState G) :=
  if s.eavesdropDone then pure s else do
    let b ← sampleExponent G
    let c ← sampleExponent G
    pure { s with
      b := b
      c := c
      B := g ^ b
      C := g ^ c
    }

attribute [local game_hopping_unfold]
  OneTimeUniformCyphertextsPubDef
  OneTimeUniformCyphertextsPubReal
  OneTimeUniformCyphertextsPubRand
  OneTimeUniformCyphertextsPubSpec
  DecisionalDHSpec
  dhReal
  dhRand
  ElGamal
  G1 G2 G3 G4
  DDHToElGamalOTUCPubReduction
  G1toG2Abstraction
  G4toG3Abstraction

/-- DDH implies one-time uniform-ciphertexts public-key security for ElGamal,
via the lazy-query DDH reduction and the no-`once` game chain above. -/
noncomputable def ddhImpliesElGamalOTUCPub
    {G : Type} [Group G] [Fintype G] [Nontrivial G] [Inhabited G] (g : G)
    (hgen : IsGenerator g) :
    OneTimeUniformCyphertextsPubDef (DecisionalDHAssumption' g) (ElGamal g) := by
  intro κ
  game_hopping [
    OneTimeUniformCyphertextsPubReal (ElGamal g),
    G1 g,
    G2 g,
    (DDHToElGamalOTUCPubReduction G) ◇ (dhReal g),
    (DDHToElGamalOTUCPubReduction G) ◇ (dhRand g),
    G3 g,
    G4 g,
    OneTimeUniformCyphertextsPubRand (ElGamal g)
  ] using GH_group_norm
  · by_abstraction ← (fun x => ⟨x.A, x.eavesdropDone⟩)
  · by_rand_abstraction (G1toG2Abstraction g)
  · by_abstraction (fun x => ({A := x.A, B := x.B, C := x.C, eavesdropDone := x.eavesdropDone}, ()))
    simp [GH_group_norm]
  · by_abstraction ← (fun x => ({A := x.A, B := x.B, C := x.C, eavesdropDone := x.eavesdropDone}, ()))
  · by_rand_abstraction ← (G4toG3Abstraction g)
  · by_abstraction (fun x => ⟨x.A, x.eavesdropDone⟩)
    simp [GH_group_random_exp, GH_group_norm]
