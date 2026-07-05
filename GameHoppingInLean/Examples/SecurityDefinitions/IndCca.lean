import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.SymEnc
import GameHoppingInLean.Misc.SimpAttrs

/-- Ciphertexts tracked by the IND-CCA oracles, bundled with their bit-length. -/
abbrev IndCcaCiphertext (C : ℕ → Type) := Σ n : ℕ, C n

/-- Coerce a length-indexed ciphertext into the bundled IND-CCA ciphertext type. -/
instance {C : ℕ → Type} {n : ℕ} : CoeOut (C n) (IndCcaCiphertext C) where
  coe c := ⟨n, c⟩

/-- State carried by IND-CCA oracles: secret key and set of challenge ciphertexts. -/
structure IndCcaState (K : Type) (C : ℕ → Type) where
  key : K
  seen : Finset (IndCcaCiphertext C)

/-- Query domain for the IND-CCA interface. -/
inductive IndCcaQ (C : ℕ → Type) where
  | eavesdrop (n : ℕ) (msgs : BitVec n × BitVec n)
  | decrypt (n : ℕ) (c : C n)

/-- IND-CCA oracle spec with two query kinds:
* `eavesdrop n (m₀, m₁)`: output a ciphertext `c : C n`
* `decrypt n c`: output `Option (BitVec n)` -/
def IndCcaSpec (C : ℕ → Type) : OracleSpec (IndCcaQ C)
  | .eavesdrop n _ => C n
  | .decrypt n _ => Option (BitVec n)

/-- Convenience query constructor for IND-CCA `eavesdrop(m₀, m₁)`. -/
@[reducible, inline] def ccaEavesdrop {C : ℕ → Type} {n : ℕ} (m₀ m₁ : BitVec n) :
    OracleComp (IndCcaSpec C) (C n) :=
  (IndCcaSpec C).query (.eavesdrop n (m₀, m₁))

/-- Convenience query constructor for IND-CCA `decrypt(c)`. -/
@[reducible, inline] def ccaDecrypt {C : ℕ → Type} {n : ℕ} (c : C n) :
    OracleComp (IndCcaSpec C) (Option (BitVec n)) :=
  (IndCcaSpec C).query (.decrypt n c)

/-- Left IND-CCA oracle:
* `eavesdrop(m₀, m₁)` returns `Enc_k(m₀)` and records the ciphertext
* `decrypt(c)` returns `none` iff `c` was previously returned by `eavesdrop`,
  otherwise returns `some (Dec_k(c))`. -/
noncomputable def IndCcaL {K : Type} {C : ℕ → Type} [∀ n, DecidableEq (C n)]
    (scheme : SymEncScheme K C) : RStateOracle (IndCcaSpec C) where
  stateType := IndCcaState K C
  initialState := do
    let k ← scheme.keyGen
    pure { key := k, seen := ∅ }
  queries := fun
    | IndCcaQ.eavesdrop _ (m₀, _m₁) => do
        let st ← get
        let c ← scheme.encrypt st.key m₀
        set { st with seen := insert (c : IndCcaCiphertext C) st.seen }
        pure c
    | IndCcaQ.decrypt _ c => do
        let st ← get
        if (c : IndCcaCiphertext C) ∈ st.seen then
          pure none
        else
          pure (some (scheme.decrypt st.key c))

/-- Right IND-CCA oracle:
* `eavesdrop(m₀, m₁)` returns `Enc_k(m₁)` and records the ciphertext
* `decrypt(c)` returns `none` iff `c` was previously returned by `eavesdrop`,
  otherwise returns `some (Dec_k(c))`. -/
noncomputable def IndCcaR {K : Type} {C : ℕ → Type} [∀ n, DecidableEq (C n)]
    (scheme : SymEncScheme K C) : RStateOracle (IndCcaSpec C) where
  stateType := IndCcaState K C
  initialState := do
    let k ← scheme.keyGen
    pure { key := k, seen := ∅ }
  queries := fun
    | IndCcaQ.eavesdrop _ (_m₀, m₁) => do
        let st ← get
        let c ← scheme.encrypt st.key m₁
        set { st with seen := insert (c : IndCcaCiphertext C) st.seen }
        pure c
    | IndCcaQ.decrypt _ c => do
        let st ← get
        if (c : IndCcaCiphertext C) ∈ st.seen then
          pure none
        else
          pure (some (scheme.decrypt st.key c))

/-- The oracle pair corresponding to the IND-CCA assumption. -/
noncomputable def IndCcaAssumption {K : Type} {C : ℕ → Type} [∀ n, DecidableEq (C n)]
    (scheme : SymEncScheme K C) : RStateOracle (IndCcaSpec C) × RStateOracle (IndCcaSpec C) :=
  (IndCcaL scheme, IndCcaR scheme)

noncomputable def IndCcaAssumptionFull {K : Type} {C : ℕ → Type} [∀ n, DecidableEq (C n)]
    (scheme : SymEncScheme K C) : SingleAssumption :=
  { i := IndCcaAssumption scheme }

noncomputable def IndCcaAssumption' {K : Type} {C : ℕ → Type} [∀ n, DecidableEq (C n)]
    (scheme : SymEncScheme K C) : IndAssumptions where
  Idx := Unit
  assumptions := fun _ => IndCcaAssumptionFull scheme

/-- IND-CCA security definition as an instance of `Indistinguishable`. -/
def IndCcaDef
    (Assumptions : IndAssumptions)
    {K : Type} {C : ℕ → Type} [∀ n, DecidableEq (C n)] (scheme : SymEncScheme K C) : Type 1 :=
  IndistinguishableSingle Assumptions
    (IndCcaL scheme) (IndCcaR scheme)

/-- Pointwise IND-CCA assumptions for a symmetric-encryption scheme family. -/
noncomputable def IndCcaAssumptionFam {K : ℕ → Type} {C : ℕ → ℕ → Type}
    [∀ κ n, DecidableEq (C κ n)]
    (schemeFam : SymEncSchemeFamily K C) (κ : ℕ) :
    IndAssumptions :=
  IndCcaAssumption' (schemeFam.scheme κ)

/-- IND-CCA security for a symmetric-encryption scheme family. -/
def IndCcaIFam
    (Assumptions : (κ : ℕ) → IndAssumptions)
    {K : ℕ → Type} {C : ℕ → ℕ → Type}
    [∀ κ n, DecidableEq (C κ n)] (schemeFam : SymEncSchemeFamily K C) : Type 1 :=
  ∀ κ,
    IndistinguishableI (Assumptions κ) none
      (IndCcaL (schemeFam.scheme κ)) (IndCcaR (schemeFam.scheme κ))
