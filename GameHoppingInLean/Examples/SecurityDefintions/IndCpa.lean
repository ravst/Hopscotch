import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.SymEnc

/-- IND-CPA eavesdropping oracle spec.
The query indexed by `n` takes a pair of `n`-bit messages and returns an `n`-bit ciphertext. -/
def IndCpaSpec : OracleSpec ℕ :=
  fun n => (BitVec n × BitVec n, BitVec n)

/-- Convenience query constructor for the IND-CPA eavesdropping oracle. -/
@[reducible, inline] def eavesdrop {n : ℕ} (m₀ m₁ : BitVec n) : OracleComp IndCpaSpec (BitVec n) :=
  IndCpaSpec.query n (m₀, m₁)

/-- Left IND-CPA oracle: encrypts the left message `m₀`. -/
noncomputable def IndCpaL {K : Type} (scheme : SymEncScheme K) : RStateOracle IndCpaSpec where
  stateType := K
  initialState := scheme.keyGen
  queries := {
    impl := fun
      | OracleSpec.query _ (m₀, _m₁) => do
          let key <- get
          scheme.encrypt key m₀
  }

/-- Right IND-CPA oracle: encrypts the right message `m₁`. -/
noncomputable def IndCpaR {K : Type} (scheme : SymEncScheme K) : RStateOracle IndCpaSpec where
  stateType := K
  initialState := scheme.keyGen
  queries := {
    impl := fun
      | OracleSpec.query _ (_m₀, m₁) => do
          let key <- get
          scheme.encrypt key m₁
  }

/-- The oracle pair corresponding to the IND-CPA security definition, for use in an
`Assumptions` set. -/
noncomputable def IndCpaAssumption {K : Type} (scheme : SymEncScheme K) :
    RStateOracle IndCpaSpec × RStateOracle IndCpaSpec :=
  (IndCpaL scheme, IndCpaR scheme)

/-- IND-CPA security definition as an instance of `Indistinguishable`. -/
def IndCpaDef
    (Assumptions : IndistinguishabilityAssumptions)
    (Reductions : IndistinguishabilityReductions)
    {K : Type} (scheme : SymEncScheme K) : Prop :=
  Indistinguishable Assumptions Reductions
    IndCpaSpec (IndCpaL scheme) (IndCpaR scheme)
