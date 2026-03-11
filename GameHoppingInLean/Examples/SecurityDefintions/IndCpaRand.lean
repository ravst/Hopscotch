import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.SymEnc

/-- IND-CPA "real vs random ciphertext" oracle spec.
The query indexed by `n` takes a single `n`-bit message and returns an `n`-bit ciphertext. -/
def IndCpaRandSpec (C : ℕ → Type) : OracleSpec ℕ :=
  fun n => (BitVec n, C n)

/-- Convenience query constructor for the `ctxt(m)` oracle query. -/
@[reducible, inline] def ctxt {C : ℕ → Type} {n : ℕ} (m : BitVec n) :
    OracleComp (IndCpaRandSpec C) (C n) :=
  (IndCpaRandSpec C).query n m

/-- IND-CPA "real ciphertext" oracle for the `ctxt(m)` interface. Returns `Enc_k(m)`. -/
noncomputable def IndCpaRandReal {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    RStateOracle (IndCpaRandSpec C) where
  stateType := K
  initialState := scheme.keyGen
  queries := {
    impl := fun  _ m => do
           let key <- get
           scheme.encrypt key m
  }

/-- IND-CPA "random ciphertext" oracle for the `ctxt(m)` interface.
Ignores the message and returns a uniformly random `n`-bit ciphertext. -/
noncomputable def IndCpaRandRand {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (_scheme : SymEncScheme K C) :
    RStateOracle (IndCpaRandSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun n _m => do
          PMF.uniformOfFintype (C n)
  }

/-- The oracle pair corresponding to the IND-CPA-rand security definition, for use in an
`Assumptions` set. -/
noncomputable def IndCpaRandAssumption {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) :
    RStateOracle (IndCpaRandSpec C) × RStateOracle (IndCpaRandSpec C) :=
  (IndCpaRandReal scheme, IndCpaRandRand scheme)

/-- IND-CPA-rand security definition as an instance of `Indistinguishable`. -/
def IndCpaRandDef
    (Assumptions : IndistinguishabilityAssumptions)
    (Reductions : IndistinguishabilityReductions)
    {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) : Prop :=
  Indistinguishable Assumptions Reductions
    (IndCpaRandSpec C) (IndCpaRandReal scheme) (IndCpaRandRand scheme)
