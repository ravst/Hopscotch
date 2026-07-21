import Hopscotch.Indistinguishability.Def
import Hopscotch.Examples.SecurityDefinitions.OneTimeSecrecy

/-- Query indices for the one-time public-key uniform-ciphertexts interface. -/
inductive OneTimeUniformCiphertextsPubQ (M : Type) where
  | getPk
  | eavesdrop (msg : M)

/-- One-time uniform-ciphertexts public-key oracle spec:
* `getPk`: no arguments, returns the public key
* `eavesdrop`: input a single message and return a ciphertext -/
def OneTimeUniformCiphertextsPubSpec (PubK M C : Type) :
    OracleSpec (OneTimeUniformCiphertextsPubQ M)
  | .getPk => PubK
  | .eavesdrop _ => C

instance instInhabitedOneTimeUniformCiphertextsPubRange {PubK M C : Type}
    [Inhabited PubK] [Inhabited C] :
    ∀ q, Inhabited ((OneTimeUniformCiphertextsPubSpec PubK M C) q)
  | .getPk => by simpa [OneTimeUniformCiphertextsPubSpec] using (inferInstance : Inhabited PubK)
  | .eavesdrop _ => by simpa [OneTimeUniformCiphertextsPubSpec] using (inferInstance : Inhabited C)

/-- Convenience query constructor for requesting the public key. -/
@[reducible, inline] def otucPubGetPk {PubK M C : Type} :
    OracleComp (OneTimeUniformCiphertextsPubSpec PubK M C) PubK :=
  (OneTimeUniformCiphertextsPubSpec PubK M C).query .getPk

/-- Convenience query constructor for the one-time uniform-ciphertexts public-key ciphertext query. -/
@[reducible, inline] def otucPubCtxt {PubK M C : Type} (m : M) :
    OracleComp (OneTimeUniformCiphertextsPubSpec PubK M C) C :=
  (OneTimeUniformCiphertextsPubSpec PubK M C).query (.eavesdrop m)

/-- Real one-time uniform-ciphertexts public-key oracle:
* `getPk` returns the public key
* the first `eavesdrop(m)` returns `Enc_pk(m)`
* every later `eavesdrop` query returns a fixed default ciphertext -/
noncomputable def OneTimeUniformCiphertextsPubReal {PubK SecK M C : Type}
    [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    OracleImpl (OneTimeUniformCiphertextsPubSpec PubK M C) where
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
noncomputable def OneTimeUniformCiphertextsPubRand {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    OracleImpl (OneTimeUniformCiphertextsPubSpec PubK M C) where
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
noncomputable def OneTimeUniformCiphertextsPubAssumptionFull {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    SingleAssumption where
  i := (OneTimeUniformCiphertextsPubReal scheme, OneTimeUniformCiphertextsPubRand scheme)

noncomputable def OneTimeUniformCiphertextsPubAssumption' {PubK SecK M C : Type}
    [Fintype C] [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    IndAssumptions Unit where
  assumptions := fun _ => OneTimeUniformCiphertextsPubAssumptionFull scheme

noncomputable def OneTimeUniformCiphertextsPubAssumptionFam
    {PubK SecK M C : ℕ → Type}
    [∀ κ, Fintype (C κ)] [∀ κ, Inhabited (C κ)]
    (schemeFam : PubEncSchemeFamily PubK SecK M C) :
    IndAssumptionsFam where
    Idx := Unit
    val κ := OneTimeUniformCiphertextsPubAssumption' (schemeFam.scheme κ)

/-- One-time uniform-ciphertexts public-key security definition as an instance of `Indistinguishable`. -/
def OneTimeUniformCiphertextsPubDef
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    {PubK SecK M C : Type} [Fintype C] [Inhabited C]
    (scheme : PubEncScheme PubK SecK M C) : Type 1 :=
  IndistinguishableSingle Assumptions
    (OneTimeUniformCiphertextsPubReal scheme)
    (OneTimeUniformCiphertextsPubRand scheme)

def OneTimeUniformCiphertextsPubIFam
    (Assumptions : IndAssumptionsFam)
    {PubK SecK M C : ℕ → Type} [∀ κ, Fintype (C κ)] [∀ κ, Inhabited (C κ)]
    (schemeFam : PubEncSchemeFamily PubK SecK M C) : Type 1 :=
    Indistinguishable (Assumptions)
      (fun κ => OneTimeUniformCiphertextsPubReal (schemeFam.scheme κ))
      (fun κ => OneTimeUniformCiphertextsPubRand (schemeFam.scheme κ))
