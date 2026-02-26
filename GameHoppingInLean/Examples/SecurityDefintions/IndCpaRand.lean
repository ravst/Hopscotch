import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.SymEnc

/-- IND-CPA "real vs random ciphertext" oracle spec.
The query indexed by `n` takes a single `n`-bit message and returns an `n`-bit ciphertext. -/
def IndCpaRandSpec : OracleSpec ℕ :=
  fun n => (BitVec n, BitVec n)

/-- Convenience query constructor for the `ctxt(m)` oracle query. -/
@[reducible, inline] def ctxt {n : ℕ} (m : BitVec n) : OracleComp IndCpaRandSpec (BitVec n) :=
  IndCpaRandSpec.query n m

/-- IND-CPA "real ciphertext" oracle for the `ctxt(m)` interface. Returns `Enc_k(m)`. -/
noncomputable def IndCpaRandReal {K : Type} (scheme : SymEncScheme K) :
    RStateOracle IndCpaRandSpec where
  stateType := K
  initialState := scheme.keyGen
  queries := {
    impl := fun
      | OracleSpec.query n m => fun key =>
          (fun c => (c, key)) <$> scheme.encrypt (n := n) key m
  }

/-- IND-CPA "random ciphertext" oracle for the `ctxt(m)` interface.
Ignores the message and returns a uniformly random `n`-bit ciphertext. -/
noncomputable def IndCpaRandRand {K : Type} (_scheme : SymEncScheme K) :
    RStateOracle IndCpaRandSpec where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun
      | OracleSpec.query n _m => fun st =>
          (fun c => (c, st)) <$> PMF.uniformOfFintype (BitVec n)
  }

/-- The oracle pair corresponding to the IND-CPA-rand security definition, for use in an
`Assumptions` set. -/
noncomputable def IndCpaRandAssumption {K : Type} (scheme : SymEncScheme K) :
    RStateOracle IndCpaRandSpec × RStateOracle IndCpaRandSpec :=
  (IndCpaRandReal scheme, IndCpaRandRand scheme)

/-- IND-CPA-rand security definition as an instance of `Indistinguishable`. -/
def IndCpaRandDef
    (Assumptions : IndistinguishabilityAssumptions)
    (SimpleReductions : IndistinguishabilitySimpleReductions)
    (Reductions : IndistinguishabilityReductions)
    {K : Type} (scheme : SymEncScheme K) : Prop :=
  Indistinguishable Assumptions SimpleReductions Reductions
    IndCpaRandSpec (IndCpaRandReal scheme) (IndCpaRandRand scheme)
