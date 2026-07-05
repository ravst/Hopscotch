import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.SymEnc
import GameHoppingInLean.Misc.SimpAttrs

/-- IND-CPA eavesdropping oracle spec.
The query indexed by `n` takes a pair of `n`-bit messages and returns an `n`-bit ciphertext. -/
inductive IndCpaDomain : Type
| eavesdrop (n : ℕ) (msgs : (BitVec n) × (BitVec n))

def IndCpaSpec (C : ℕ → Type) : OracleSpec IndCpaDomain :=
  fun ⟨n, _m⟩ => C n

/-- Convenience query constructor for the IND-CPA eavesdropping oracle. -/
@[reducible, inline] def eavesdrop {C : ℕ → Type} {n : ℕ} (m₀ m₁ : BitVec n) :
    OracleComp (IndCpaSpec C) (C n) :=
  (IndCpaSpec C).query ⟨n, (m₀, m₁)⟩

/-- Left IND-CPA oracle: encrypts the left message `m₀`. -/
noncomputable def IndCpaL {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    RStateOracle (IndCpaSpec C) where
  stateType := K
  initialState := scheme.keyGen
  queries := fun ⟨_n, (m₀, _m₁)⟩ => do
          let key <- get
          scheme.encrypt key m₀

/-- Right IND-CPA oracle: encrypts the right message `m₁`. -/
noncomputable def IndCpaR {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    RStateOracle (IndCpaSpec C) where
  stateType := K
  initialState := scheme.keyGen
  queries := fun  ⟨_n, (_m₀, m₁)⟩ => do
          let key <- get
          scheme.encrypt key m₁


/-- The oracle pair corresponding to the IND-CPA security definition, for use in an
`Assumptions` set. -/
noncomputable def IndCpaAssumption {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    RStateOracle (IndCpaSpec C) × RStateOracle (IndCpaSpec C) :=
  (IndCpaL scheme, IndCpaR scheme)

noncomputable def IndCpaAssumptionFull {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    SingleAssumption :=
  ⟨IndCpaDomain, IndCpaSpec C, IndCpaAssumption scheme⟩

noncomputable def IndCpaAssumptionFam {K : ℕ → Type} {C : ℕ → ℕ → Type}
    (schemeFam : SymEncSchemeFamily K C) : IndAssumptionsFam :=
  fun κ =>
  {
  Idx := Unit
  assumptions := fun _ => IndCpaAssumptionFull (schemeFam.scheme κ)
  }

/-- IND-CPA security definition as an instance of `Indistinguishable`. -/
def IndCpaDef
    (Assumptions : IndAssumptions)
    {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) : Type 1 :=
  IndistinguishableSingle Assumptions
    (IndCpaL scheme) (IndCpaR scheme)


/-- IND-CPA security definition as an instance of `Indistinguishable`. -/
def IndCpaDefF
    (Assumptions : IndAssumptionsFam)
    {K : ℕ → Type} {C : ℕ → ℕ → Type} (schemeFam : SymEncSchemeFamily K C) : Type 1 :=
  Indistinguishable
    Assumptions
    (fun κ => (IndCpaL (schemeFam.scheme κ) ))
    (fun κ => (IndCpaR (schemeFam.scheme κ) ))
