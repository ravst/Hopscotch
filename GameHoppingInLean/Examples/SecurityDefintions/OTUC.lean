import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.SymEnc

/-- One-time uniform ciphertext (OTUC) oracle spec.
The query indexed by `n` takes an `n`-bit message and returns an `n`-bit ciphertext. -/
def OTUCSpec (C : ℕ → Type) : OracleSpec ℕ :=
  fun n => (BitVec n, C n)

/-- Convenience query constructor for the OTUC `ctxt(m)` query. -/
@[reducible, inline] def otucCtxt {C : ℕ → Type} {n : ℕ} (m : BitVec n) :
    OracleComp (OTUCSpec C) (C n) :=
  (OTUCSpec C).query n m

/-- OTUC real oracle: on each query, sample a fresh key from the scheme and encrypt the message. -/
noncomputable def OTUC_Real {K : Type} {C : ℕ → Type} (scheme : SymEncScheme K C) :
    RStateOracle (OTUCSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun _n m => do
          let k ← scheme.keyGen
          let c ← scheme.encrypt k m
          pure c
  }

/-- OTUC random oracle: ignore the message and return a uniformly random `n`-bit ciphertext. -/
noncomputable def OTUC_Rand {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (_scheme : SymEncScheme K C) :
    RStateOracle (OTUCSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun
       n _m => do
          let c ← PMF.uniformOfFintype (C n)
          pure c
  }

/-- The oracle pair corresponding to the OTUC assumption, for use in an `Assumptions` set. -/
noncomputable def OTUCAssumption {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) :
    RStateOracle (OTUCSpec C) × RStateOracle (OTUCSpec C) :=
  (OTUC_Real scheme, OTUC_Rand scheme)

noncomputable def OTUCAssumptionFull {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) :
    ((I : Type) × (O : OracleSpec I) × (RStateOracle O × RStateOracle O)) :=
  ⟨ℕ, OTUCSpec C, OTUCAssumption scheme⟩

noncomputable def OTUCAssumption' {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) :
    IndistinguishabilityAssumptions where
  Idx := Unit
  assumptions := fun _ => OTUCAssumptionFull scheme

/-- OTUC indistinguishability definition as an instance of `Indistinguishable`. -/
def OTUCDef
    (Assumptions : IndistinguishabilityAssumptions)
    (Reductions : IndistinguishabilityReductions)
    {K : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)] (scheme : SymEncScheme K C) : Type 1 :=
  Indistinguishable Assumptions Reductions
    (OTUCSpec C) (OTUC_Real scheme) (OTUC_Rand scheme)
