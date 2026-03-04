import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.SymEnc

/-- Query indices for the IND-CCA interface. -/
inductive IndCcaQ where
  | eavesdrop (n : ℕ)
  | decrypt (n : ℕ)

/-- Ciphertexts tracked by the IND-CCA oracles, bundled with their bit-length. -/
abbrev IndCcaCiphertext := Σ n : ℕ, BitVec n

/-- Coerce a length-indexed ciphertext into the bundled IND-CCA ciphertext type. -/
instance {n : ℕ} : CoeOut (BitVec n) IndCcaCiphertext where
  coe c := ⟨n, c⟩

/-- State carried by IND-CCA oracles: secret key and set of challenge ciphertexts. -/
abbrev IndCcaState (K : Type) := K × Finset IndCcaCiphertext

/-- IND-CCA oracle spec with two query kinds:
* `eavesdrop n`: input `(m₀, m₁)` and output a ciphertext `c : BitVec n`
* `decrypt n`: input ciphertext `c : BitVec n` and output `Option (BitVec n)` -/
def IndCcaSpec : OracleSpec IndCcaQ
  | .eavesdrop n => (BitVec n × BitVec n, BitVec n)
  | .decrypt n => (BitVec n, Option (BitVec n))

/-- Coerce decrypt-query domain values into bundled IND-CCA ciphertexts. -/
instance {n : ℕ} : CoeOut (IndCcaSpec.domain (IndCcaQ.decrypt n)) IndCcaCiphertext where
  coe c := ⟨n, c⟩

/-- Convenience query constructor for IND-CCA `eavesdrop(m₀, m₁)`. -/
@[reducible, inline] def ccaEavesdrop {n : ℕ} (m₀ m₁ : BitVec n) :
    OracleComp IndCcaSpec (BitVec n) :=
  IndCcaSpec.query (.eavesdrop n) (m₀, m₁)

/-- Convenience query constructor for IND-CCA `decrypt(c)`. -/
@[reducible, inline] def ccaDecrypt {n : ℕ} (c : BitVec n) :
    OracleComp IndCcaSpec (Option (BitVec n)) :=
  IndCcaSpec.query (.decrypt n) c

/-- Left IND-CCA oracle:
* `eavesdrop(m₀, m₁)` returns `Enc_k(m₀)` and records the ciphertext
* `decrypt(c)` returns `none` iff `c` was previously returned by `eavesdrop`,
  otherwise returns `some (Dec_k(c))`. -/
noncomputable def IndCcaL {K : Type} (scheme : SymEncScheme K) : RStateOracle IndCcaSpec where
  stateType := IndCcaState K
  initialState := do
    let k ← scheme.keyGen
    pure (k, ∅)
  queries := {
    impl := fun
      | OracleSpec.query (IndCcaQ.eavesdrop _) (m₀, _m₁) => do
          let (key, seen) ← get
          let c ← scheme.encrypt key m₀
          set (key, insert ↑c seen)
          pure c
      | OracleSpec.query (IndCcaQ.decrypt _) c => do
          let (key, seen) ← get
          if ↑c ∈ seen then
            pure none
          else
            pure (some (scheme.decrypt key c))
  }

/-- Right IND-CCA oracle:
* `eavesdrop(m₀, m₁)` returns `Enc_k(m₁)` and records the ciphertext
* `decrypt(c)` returns `none` iff `c` was previously returned by `eavesdrop`,
  otherwise returns `some (Dec_k(c))`. -/
noncomputable def IndCcaR {K : Type} (scheme : SymEncScheme K) : RStateOracle IndCcaSpec where
  stateType := IndCcaState K
  initialState := do
    let k ← scheme.keyGen
    pure (k, ∅)
  queries := {
    impl := fun
      | OracleSpec.query (IndCcaQ.eavesdrop _) (_m₀, m₁) => do
          let (key, seen) ← get
          let c ← scheme.encrypt key m₁
          set (key, insert ↑c seen)
          pure c
      | OracleSpec.query (IndCcaQ.decrypt n) c => do
          let (key, seen) ← get
          if ↑c ∈ seen then
            pure none
          else
            pure (some (scheme.decrypt key c))
  }

/-- The oracle pair corresponding to the IND-CCA assumption, for use in an `Assumptions` set. -/
noncomputable def IndCcaAssumption {K : Type} (scheme : SymEncScheme K) :
    RStateOracle IndCcaSpec × RStateOracle IndCcaSpec :=
  (IndCcaL scheme, IndCcaR scheme)

/-- IND-CCA security definition as an instance of `Indistinguishable`. -/
def IndCcaDef
    (Assumptions : IndistinguishabilityAssumptions)
    (Reductions : IndistinguishabilityReductions)
    {K : Type} (scheme : SymEncScheme K) : Prop :=
  Indistinguishable Assumptions Reductions
    IndCcaSpec (IndCcaL scheme) (IndCcaR scheme)
