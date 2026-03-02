import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.PRG

/-- PRG security oracle spec.
Single query returns a `(k + l)`-bit output. -/
def SecurePRGSpec (k l : ℕ) : OracleSpec Unit :=
  fun _ => (Unit, BitVec (k + l))

/-- Convenience query constructor for requesting one PRG output sample. -/
@[reducible, inline] def prgOut {k l : ℕ} :
    OracleComp (SecurePRGSpec k l) (BitVec (k + l)) :=
  (SecurePRGSpec k l).query () ()

/-- Real PRG oracle.
Stateless: samples a fresh uniform seed on each query, then returns `prg.draw seed`. -/
noncomputable def PRG_real {k l : ℕ} (prg : PRG k l) :
    RStateOracle (SecurePRGSpec k l) where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun
      | OracleSpec.query _ _ => do
          let seed ← PMF.uniformOfFintype (BitVec k)
          pure (prg.draw seed)
  }

/-- Random oracle baseline for PRG security.
Ignores the query input and returns a uniformly random `(k + l)`-bit string. -/
noncomputable def PRG_rand (k l : ℕ) : RStateOracle (SecurePRGSpec k l) where
  stateType := Unit
  initialState := pure ()
  queries := {
    impl := fun
      | OracleSpec.query _ _ => do
          PMF.uniformOfFintype (BitVec (k + l))
  }

/-- The oracle pair corresponding to the PRG security definition, for use in an
`Assumptions` set. -/
noncomputable def SecurePRGAssumption {k l : ℕ} (prg : PRG k l) :
    RStateOracle (SecurePRGSpec k l) × RStateOracle (SecurePRGSpec k l) :=
  (PRG_real prg, PRG_rand k l)

/-- PRG security definition as an instance of `Indistinguishable`. -/
def SecurePRGDef
    (Assumptions : IndistinguishabilityAssumptions)
    (Reductions : IndistinguishabilityReductions)
    {k l : ℕ} (prg : PRG k l) : Prop :=
  Indistinguishable Assumptions Reductions
    (SecurePRGSpec k l) (PRG_real prg) (PRG_rand k l)
