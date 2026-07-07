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

noncomputable def IndCpaRFam {K : ℕ → Type} {C : ℕ → ℕ → Type} (schemeFam : SymEncSchemeFamily K C) :
    (κ : ℕ) → RStateOracle (IndCpaSpec (C κ)) :=
  fun κ => IndCpaR (schemeFam.scheme κ)

noncomputable def IndCpaLFam {K : ℕ → Type} {C : ℕ → ℕ → Type} (schemeFam : SymEncSchemeFamily K C) :
    (κ : ℕ) → RStateOracle (IndCpaSpec (C κ)) :=
  fun κ => IndCpaL (schemeFam.scheme κ)

noncomputable def IndCpaAssumptionFam {K : ℕ → Type} {C : ℕ → ℕ → Type}
    (schemeFam : SymEncSchemeFamily K C) : IndAssumptionsFam := {
  Idx := Unit
  val := fun κ => {
  assumptions := fun _ =>
    ⟨ (IndCpaL (schemeFam.scheme κ), IndCpaR (schemeFam.scheme κ))⟩
  }
}
