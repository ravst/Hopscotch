import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.SecurityDefinitions.OneTimeSecrecy

/-- Query indices for the one-time public-key uniform-ciphertexts interface. -/
inductive OneTimeUniformCyphertextsPubQ (M : Type) where
  | getPk
  | eavesdrop (msg : M)

/-- One-time uniform-ciphertexts public-key oracle spec:
* `getPk`: no arguments, returns the public key
* `eavesdrop`: input a single message and return a ciphertext -/
def OneTimeUniformCyphertextsPubSpec (PubK M C : Type) :
    OracleSpec (OneTimeUniformCyphertextsPubQ M)
  | .getPk => PubK
  | .eavesdrop _ => C

instance instInhabitedOneTimeUniformCyphertextsPubRange {PubK M C : Type}
    [Inhabited PubK] [Inhabited C] :
    ∀ q, Inhabited ((OneTimeUniformCyphertextsPubSpec PubK M C) q)
  | .getPk => by simpa [OneTimeUniformCyphertextsPubSpec] using (inferInstance : Inhabited PubK)
  | .eavesdrop _ => by simpa [OneTimeUniformCyphertextsPubSpec] using (inferInstance : Inhabited C)

/-- Convenience query constructor for requesting the public key. -/
@[reducible, inline] def otucPubGetPk {PubK M C : Type} :
    OracleComp (OneTimeUniformCyphertextsPubSpec PubK M C) PubK :=
  (OneTimeUniformCyphertextsPubSpec PubK M C).query .getPk

/-- Convenience query constructor for the one-time uniform-ciphertexts public-key ciphertext query. -/
@[reducible, inline] def otucPubCtxt {PubK M C : Type} (m : M) :
    OracleComp (OneTimeUniformCyphertextsPubSpec PubK M C) C :=
  (OneTimeUniformCyphertextsPubSpec PubK M C).query (.eavesdrop m)

/-- Real one-time uniform-ciphertexts public-key oracle:
* `getPk` returns the public key
* the first `eavesdrop(m)` returns `Enc_pk(m)`
* every later `eavesdrop` query returns a fixed default ciphertext -/
noncomputable def OneTimeUniformCyphertextsPubReal {PubK SecK M C : Type}
    [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (OneTimeUniformCyphertextsPubSpec PubK M C) where
  stateType := OneTimeSecrecyState PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure { pk := pk, eavesdropDone := false }
  queries := fun
      | .getPk => do
          let st <- get
          pure st.pk
      | .eavesdrop m => do
          let st <- get
          if not st.eavesdropDone then
            set { st with eavesdropDone := true }
            scheme.encrypt st.pk m
          else
            pure (default : C)

/-- Random one-time uniform-ciphertexts public-key oracle:
* `getPk` returns the public key
* the first `eavesdrop(m)` ignores the message and samples uniformly from the ciphertext space
* every later `eavesdrop` query returns a fixed default ciphertext -/
noncomputable def OneTimeUniformCyphertextsPubRand {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (OneTimeUniformCyphertextsPubSpec PubK M C) where
  stateType := OneTimeSecrecyState PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure { pk := pk, eavesdropDone := false }
  queries := fun
      | .getPk => do
          let st <- get
          pure st.pk
      | .eavesdrop _m => do
          let st <- get
          set { st with eavesdropDone := true }
          if not st.eavesdropDone then
            PMF.uniformOfFintype C
          else
            pure (default : C)

/-- The oracle pair corresponding to the one-time uniform-ciphertexts public-key assumption, for use in an
`Assumptions` set. -/
noncomputable def OneTimeUniformCyphertextsPubAssumption {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (OneTimeUniformCyphertextsPubSpec PubK M C) ×
      RStateOracle (OneTimeUniformCyphertextsPubSpec PubK M C) :=
  (OneTimeUniformCyphertextsPubReal scheme, OneTimeUniformCyphertextsPubRand scheme)

noncomputable def OneTimeUniformCyphertextsPubAssumptionFull {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    SingleAssumption where
  i := OneTimeUniformCyphertextsPubAssumption scheme

noncomputable def OneTimeUniformCyphertextsPubAssumption' {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    IndAssumptions Unit where
  assumptions := fun _ => OneTimeUniformCyphertextsPubAssumptionFull scheme

noncomputable def OneTimeUniformCyphertextsPubAssumptionFam
    {PubK SecK M C : ℕ → Type}
    [∀ κ, Fintype (C κ)] [∀ κ, Inhabited (C κ)]
    (schemeFam : PubEncSchemeFamily PubK SecK M C) (κ : ℕ) :
    IndAssumptions Unit :=
  OneTimeUniformCyphertextsPubAssumption' (schemeFam.scheme κ)

/-- One-time uniform-ciphertexts public-key security definition as an instance of `Indistinguishable`. -/
def OneTimeUniformCyphertextsPubDef
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    {PubK SecK M C : Type} [Fintype C] [Inhabited C]
    (scheme : PubEncScheme PubK SecK M C) : Type 1 :=
  IndistinguishableSingle Assumptions
    (OneTimeUniformCyphertextsPubReal scheme)
    (OneTimeUniformCyphertextsPubRand scheme)

def OneTimeUniformCyphertextsPubIFam
    {Idx : Type} (Assumptions : (κ : ℕ) → IndAssumptions Idx)
    {PubK SecK M C : ℕ → Type} [∀ κ, Fintype (C κ)] [∀ κ, Inhabited (C κ)]
    (schemeFam : PubEncSchemeFamily PubK SecK M C) : Type 1 :=
  ∀ κ,
    IndistinguishableI (Assumptions κ) none
      (OneTimeUniformCyphertextsPubReal (schemeFam.scheme κ))
      (OneTimeUniformCyphertextsPubRand (schemeFam.scheme κ))
