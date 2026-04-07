import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.SecurityDefintions.OneTimeSecrecy

/-- One-time secrecy "real vs random ciphertext" oracle spec:
* `getPk`: no arguments, returns the public key
* `eavesdrop`: input a single message and return a ciphertext -/
def OneTimeSecrecyRandSpec (PubK M C : Type) : OracleSpec OneTimeSecrecyQ
  | .getPk => (Unit, PubK)
  | .eavesdrop => (M, C)

instance instInhabitedOneTimeSecrecyRandRange {PubK M C : Type}
    [Inhabited PubK] [Inhabited C] :
    ∀ q, Inhabited ((OneTimeSecrecyRandSpec PubK M C).range q)
  | .getPk => by simpa [OneTimeSecrecyRandSpec] using (inferInstance : Inhabited PubK)
  | .eavesdrop => by simpa [OneTimeSecrecyRandSpec] using (inferInstance : Inhabited C)

/-- Convenience query constructor for requesting the public key. -/
@[reducible, inline] def otsRandGetPk {PubK M C : Type} :
    OracleComp (OneTimeSecrecyRandSpec PubK M C) PubK :=
  (OneTimeSecrecyRandSpec PubK M C).query .getPk ()

/-- Convenience query constructor for the one-time secrecy-rand ciphertext query. -/
@[reducible, inline] def otsRandCtxt {PubK M C : Type} (m : M) :
    OracleComp (OneTimeSecrecyRandSpec PubK M C) C :=
  (OneTimeSecrecyRandSpec PubK M C).query .eavesdrop m

/-- Real one-time secrecy-rand oracle:
* `getPk` returns the public key
* the first `eavesdrop(m)` returns `Enc_pk(m)`
* every later `eavesdrop` query returns a fixed default ciphertext -/
noncomputable def OneTimeSecrecyRandReal {PubK SecK M C : Type}
    [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (OneTimeSecrecyRandSpec PubK M C) where
  stateType := OneTimeSecrecyState PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure { pk := pk, eavesdropCount := 0 }
  queries := {
    impl := fun q input => match q, input with
      | .getPk, () => do
          let st <- get
          pure st.pk
      | .eavesdrop, m => do
          let st <- get
          set { st with eavesdropCount := st.eavesdropCount + 1 }
          if st.eavesdropCount = 0 then
            scheme.encrypt st.pk m
          else
            pure (default : C)
  }

/-- Random one-time secrecy-rand oracle:
* `getPk` returns the public key
* the first `eavesdrop(m)` ignores the message and samples uniformly from the ciphertext space
* every later `eavesdrop` query returns a fixed default ciphertext -/
noncomputable def OneTimeSecrecyRandRand {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (OneTimeSecrecyRandSpec PubK M C) where
  stateType := OneTimeSecrecyState PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure { pk := pk, eavesdropCount := 0 }
  queries := {
    impl := fun q input => match q, input with
      | .getPk, () => do
          let st <- get
          pure st.pk
      | .eavesdrop, _m => do
          let st <- get
          set { st with eavesdropCount := st.eavesdropCount + 1 }
          if st.eavesdropCount = 0 then
            PMF.uniformOfFintype C
          else
            pure (default : C)
  }

/-- The oracle pair corresponding to the one-time secrecy-rand assumption, for use in an
`Assumptions` set. -/
noncomputable def OneTimeSecrecyRandAssumption {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (OneTimeSecrecyRandSpec PubK M C) ×
      RStateOracle (OneTimeSecrecyRandSpec PubK M C) :=
  (OneTimeSecrecyRandReal scheme, OneTimeSecrecyRandRand scheme)

/-- One-time secrecy-rand security definition as an instance of `Indistinguishable`. -/
def OneTimeSecrecyRandDef
    (Assumptions : IndistinguishabilityAssumptions)
    (Reductions : IndistinguishabilityReductions)
    {PubK SecK M C : Type} [Fintype C] [Inhabited C]
    (scheme : PubEncScheme PubK SecK M C) : Type 1 :=
  Indistinguishable Assumptions Reductions
    (OneTimeSecrecyRandSpec PubK M C)
    (OneTimeSecrecyRandReal scheme)
    (OneTimeSecrecyRandRand scheme)
