import GameHoppingInLean.Examples.SecurityDefinitions.IndCPAPub

/-- State carried by the one-time secrecy oracles: the public key and whether an
eavesdrop query has already been answered. -/
structure OneTimeSecrecyState (PubK : Type) where
  pk : PubK
  eavesdropDone : Bool

/-- One-time secrecy oracle spec:
* `getPk`: no arguments, returns the public key
* `eavesdrop`: input `(m₀, m₁)` and output a ciphertext -/
abbrev OneTimeSecrecySpec (PubK M C : Type) : OracleSpec (IndCpaPubQ M) :=
  IndCpaPubSpec PubK M C

/-- Convenience query constructor for requesting the public key. -/
@[reducible, inline] def otsGetPk {PubK M C : Type} :
    OracleComp (OneTimeSecrecySpec PubK M C) PubK :=
  indCpaPubGetPk

/-- Convenience query constructor for the one-time secrecy eavesdropping oracle. -/
@[reducible, inline] def otsEavesdrop {PubK M C : Type} (m₀ m₁ : M) :
    OracleComp (OneTimeSecrecySpec PubK M C) C :=
  indCpaPubEavesdrop m₀ m₁

/-- Left one-time secrecy oracle:
* `getPk` returns the public key
* the first `eavesdrop(m₀, m₁)` returns `Enc_pk(m₀)`
* every later `eavesdrop` query returns `default : C` -/
noncomputable def OneTimeSecrecyL {PubK SecK M C : Type}
    [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (OneTimeSecrecySpec PubK M C) where
  stateType := OneTimeSecrecyState PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure { pk := pk, eavesdropDone := false }
  queries := fun input => match input with
      | .getPk => do
          let st <- get
          pure st.pk
      | .eavesdrop (m₀, _m₁) => do
          let st <- get
          set { st with eavesdropDone := true }
          if not st.eavesdropDone then
            scheme.encrypt st.pk m₀
          else
            pure (default : C)

/-- Right one-time secrecy oracle:
* `getPk` returns the public key
* the first `eavesdrop(m₀, m₁)` returns `Enc_pk(m₁)`
* every later `eavesdrop` query returns `default : C` -/
noncomputable def OneTimeSecrecyR {PubK SecK M C : Type}
    [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (OneTimeSecrecySpec PubK M C) where
  stateType := OneTimeSecrecyState PubK
  initialState := do
    let (pk, _sk) <- scheme.keyGen
    pure { pk := pk, eavesdropDone := false }
  queries := fun input => match input with
      | .getPk => do
          let st <- get
          pure st.pk
      | .eavesdrop (_m₀, m₁) => do
          let st <- get
          set { st with eavesdropDone := true }
          if not st.eavesdropDone then
            scheme.encrypt st.pk m₁
          else
            pure (default : C)

/-- The oracle pair corresponding to the one-time secrecy assumption, for use in an
`Assumptions` set. -/
noncomputable def OneTimeSecrecyAssumption {PubK SecK M C : Type}
    [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    RStateOracle (OneTimeSecrecySpec PubK M C) × RStateOracle (OneTimeSecrecySpec PubK M C) :=
  (OneTimeSecrecyL scheme, OneTimeSecrecyR scheme)

noncomputable def OneTimeSecrecyAssumptionFull {PubK SecK M C : Type}
    [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
  SingleAssumption where
  I := IndCpaPubQ M
  O := OneTimeSecrecySpec PubK M C
  i := OneTimeSecrecyAssumption scheme

noncomputable def OneTimeSecrecyAssumption' {PubK SecK M C : Type}
    [Inhabited C] (scheme : PubEncScheme PubK SecK M C) :
    IndistinguishabilityAssumptions where
  Idx := Unit
  assumptions := fun _ => OneTimeSecrecyAssumptionFull scheme

noncomputable def OneTimeSecrecyAssumptionFam
    {PubK SecK M C : ℕ → Type}
    [∀ κ, Inhabited (C κ)]
    (schemeFam : PubEncSchemeFamily PubK SecK M C) (κ : ℕ) :
    IndistinguishabilityAssumptions :=
  OneTimeSecrecyAssumption' (schemeFam.scheme κ)

/-- One-time secrecy security definition as an instance of `Indistinguishable`. -/
def OneTimeSecrecyDef
    (Assumptions : IndistinguishabilityAssumptions)
    {PubK SecK M C : Type} [Inhabited C] (scheme : PubEncScheme PubK SecK M C) : Type 1 :=
  Indistinguishable Assumptions
    (OneTimeSecrecyL scheme)
    (OneTimeSecrecyR scheme)

def OneTimeSecrecyIFam
    (Assumptions : (κ : ℕ) → IndistinguishabilityAssumptions)
    {PubK SecK M C : ℕ → Type} [∀ κ, Inhabited (C κ)]
    (schemeFam : PubEncSchemeFamily PubK SecK M C) : Type 1 :=
  ∀ κ,
    IndistinguishableI (Assumptions κ) κ none _
      (OneTimeSecrecyL (schemeFam.scheme κ))
      (OneTimeSecrecyR (schemeFam.scheme κ))
