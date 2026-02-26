import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.SymEnc

/-- One-time uniform ciphertext (OTUC) oracle spec.
The query indexed by `n` takes an `n`-bit message and returns an `n`-bit ciphertext. -/
def OTUCSpec : OracleSpec ℕ :=
  fun n => (BitVec n, BitVec n)

/-- Convenience query constructor for the OTUC `ctxt(m)` query. -/
@[reducible, inline] def otucCtxt {n : ℕ} (m : BitVec n) : OracleComp OTUCSpec (BitVec n) :=
  OTUCSpec.query n m

/-- OTUC real oracle: on each query, sample a fresh key from the scheme and encrypt the message. -/
noncomputable def OTUC_Real {K : Type} (scheme : SymEncScheme K) : RStateOracle OTUCSpec where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun
      | OracleSpec.query n m => do
          let k ← scheme.keyGen
          let c ← scheme.encrypt k m
          pure c
  }

/-- OTUC random oracle: ignore the message and return a uniformly random `n`-bit ciphertext. -/
noncomputable def OTUC_Rand {K : Type} (_scheme : SymEncScheme K) : RStateOracle OTUCSpec where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun
      | OracleSpec.query n _m => do
          let c ← PMF.uniformOfFintype (BitVec n)
          pure c
  }

/-- The oracle pair corresponding to the OTUC assumption, for use in an `Assumptions` set. -/
noncomputable def OTUCAssumption {K : Type} (scheme : SymEncScheme K) :
    RStateOracle OTUCSpec × RStateOracle OTUCSpec :=
  (OTUC_Real scheme, OTUC_Rand scheme)

/-- OTUC indistinguishability definition as an instance of `Indistinguishable`. -/
def OTUCDef
    (Assumptions : IndistinguishabilityAssumptions)
    (SimpleReductions : IndistinguishabilitySimpleReductions)
    (Reductions : IndistinguishabilityReductions)
    {K : Type} (scheme : SymEncScheme K) : Prop :=
  Indistinguishable Assumptions SimpleReductions Reductions
    OTUCSpec (OTUC_Real scheme) (OTUC_Rand scheme)
