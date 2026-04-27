import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.SecurityDefinitions.OneTimeUniformCyphertextsPub

/-- Public-key IND-CPA-rand oracle spec with a public-key reveal query and a
single-message ciphertext query. This is definitionally the same interface as
`OneTimeUniformCyphertextsPubSpec`, but without the one-query restriction. -/
abbrev IndCpaRandPubSpec (PubK M C : Type) : OracleSpec IndCpaPubQ :=
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
  queries := {
    impl := fun q input => match q, input with
      | .getPk, () => do
          get
      | .eavesdrop, m => do
          let pk <- get
          scheme.encrypt pk m
  }

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
  queries := {
    impl := fun q input => match q, input with
      | .getPk, () => do
          get
      | .eavesdrop, _m => do
          PMF.uniformOfFintype C
  }

/-- The oracle pair corresponding to the public-key IND-CPA-rand assumption, for
use in an `Assumptions` set. -/
noncomputable def IndCpaRandPubAssumption {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (IndCpaRandPubSpec PubK M C) ×
      RStateOracle (IndCpaRandPubSpec PubK M C) :=
  (IndCpaRandPubReal scheme, IndCpaRandPubRand scheme)

/-- Public-key IND-CPA-rand security definition as an instance of
`Indistinguishable`. -/
def IndCpaRandPubDef
    (Assumptions : IndistinguishabilityAssumptions)
    (Reductions : IndistinguishabilityReductions)
    {PubK SecK M C : Type} [Fintype C] [Inhabited C]
    (scheme : PubEncScheme PubK SecK M C) : Type 1 :=
  Indistinguishable Assumptions Reductions
    (IndCpaRandPubReal scheme)
    (IndCpaRandPubRand scheme)
