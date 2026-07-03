import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.SecurityDefinitions.OneTimeUniformCyphertextsPub

/-- Public-key IND-CPA-rand oracle spec with a public-key reveal query and a
single-message ciphertext query. This is definitionally the same interface as
`OneTimeUniformCyphertextsPubSpec`, but without the one-query restriction. -/
abbrev IndCpaRandPubSpec (PubK M C : Type) : OracleSpec (OneTimeUniformCyphertextsPubQ M) :=
  OneTimeUniformCyphertextsPubSpec PubK M C

/-- Convenience query constructor for revealing the public key. -/
@[reducible, inline] def indCpaRandPubGetPk {PubK M C : Type} :
    OracleComp (IndCpaRandPubSpec PubK M C) PubK :=
  otucPubGetPk

/-- Convenience query constructor for the public-key IND-CPA-rand ciphertext query. -/
@[reducible, inline] def indCpaRandPubCtxt {PubK M C : Type} (m : M) :
    OracleComp (IndCpaRandPubSpec PubK M C) C :=
  otucPubCtxt m

/-- Real public-key IND-CPA-rand oracle:
* `getPk` returns the public key
* `eavesdrop(m)` returns `Enc_pk(m)` for every query. -/
noncomputable def IndCpaRandPubReal {PubK SecK M C : Type}
    (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (IndCpaRandPubSpec PubK M C) where
  stateType := PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure pk
  queries := fun
      | .getPk => do
          get
      | .eavesdrop m => do
          let pk <- get
          scheme.encrypt pk m

/-- Random public-key IND-CPA-rand oracle:
* `getPk` returns the public key
* `eavesdrop(m)` ignores the message and returns a uniform ciphertext. -/
noncomputable def IndCpaRandPubRand {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (IndCpaRandPubSpec PubK M C) where
  stateType := PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure pk
  queries := fun
      | .getPk => do
          get
      | .eavesdrop _m => do
          PMF.uniformOfFintype C

/-- The oracle pair corresponding to the public-key IND-CPA-rand assumption, for
use in an `Assumptions` set. -/
noncomputable def IndCpaRandPubAssumption {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (IndCpaRandPubSpec PubK M C) ×
      RStateOracle (IndCpaRandPubSpec PubK M C) :=
  (IndCpaRandPubReal scheme, IndCpaRandPubRand scheme)

noncomputable def IndCpaRandPubAssumptionFull {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    SingleAssumption where
  I := OneTimeUniformCyphertextsPubQ M
  O := IndCpaRandPubSpec PubK M C
  i := IndCpaRandPubAssumption scheme

noncomputable def IndCpaRandPubAssumption' {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    IndistinguishabilityAssumptions where
  Idx := Unit
  assumptions := fun _ => IndCpaRandPubAssumptionFull scheme

noncomputable def IndCpaRandPubAssumptionFam
    {PubK SecK M C : ℕ → Type}
    [∀ κ, Fintype (C κ)] [∀ κ, Inhabited (C κ)]
    (schemeFam : PubEncSchemeFamily PubK SecK M C) (κ : ℕ) :
    IndistinguishabilityAssumptions :=
  IndCpaRandPubAssumption' (schemeFam.scheme κ)

/-- Public-key IND-CPA-rand security definition as an instance of
`Indistinguishable`. -/
def IndCpaRandPubDef
    (Assumptions : IndistinguishabilityAssumptions)
    {PubK SecK M C : Type} [Fintype C] [Inhabited C]
    (scheme : PubEncScheme PubK SecK M C) : Type 1 :=
  Indistinguishable Assumptions
    (IndCpaRandPubReal scheme)
    (IndCpaRandPubRand scheme)

def IndCpaRandPubIFam
    (Assumptions : (κ : ℕ) → IndistinguishabilityAssumptions)
    {PubK SecK M C : ℕ → Type} [∀ κ, Fintype (C κ)] [∀ κ, Inhabited (C κ)]
    (schemeFam : PubEncSchemeFamily PubK SecK M C) : Type 1 :=
  ∀ κ,
    IndistinguishableI (Assumptions κ) none
      (IndCpaRandPubReal (schemeFam.scheme κ))
      (IndCpaRandPubRand (schemeFam.scheme κ))
