import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.PRG
import GameHoppingInLean.Misc.SimpAttrs

/-- PRG security oracle spec.
Single query returns a `(k + l)`-bit output. -/
def SecurePRGSpec (k l : ℕ) : OracleSpec Unit :=
  fun _ => BitVec (k + l)

/-- Convenience query constructor for requesting one PRG output sample. -/
@[reducible, inline] def prgOut {k l : ℕ} :
    OracleComp (SecurePRGSpec k l) (BitVec (k + l)) :=
  (SecurePRGSpec k l).query ()

/-- Real PRG oracle.
Stateless: samples a fresh uniform seed on each query, then returns `prg.draw seed`. -/
noncomputable def PRG_real {k l : ℕ} (prg : PRG k l) :
    RStateOracle (SecurePRGSpec k l) where
  stateType := Unit
  initialState := pure ()
  queries := fun _ => do
          let seed ← PMF.uniformOfFintype (BitVec k)
          pure (prg.draw seed)

/-- Random oracle baseline for PRG security.
Ignores the query input and returns a uniformly random `(k + l)`-bit string. -/
noncomputable def PRG_rand (k l : ℕ) : RStateOracle (SecurePRGSpec k l) where
  stateType := Unit
  initialState := pure ()
  queries := fun _ => do
          PMF.uniformOfFintype (BitVec (k + l))

/-- The oracle pair corresponding to the PRG security definition, for use in an
`Assumptions` set. -/
noncomputable def SecurePRGAssumption {k l : ℕ} (prg : PRG k l) :
    RStateOracle (SecurePRGSpec k l) × RStateOracle (SecurePRGSpec k l) :=
  (PRG_real prg, PRG_rand k l)

noncomputable def SecurePRGAssumptionFull {k l : ℕ} (prg : PRG k l) :
    SingleAssumption :=
  { i := SecurePRGAssumption prg }

noncomputable def SecurePRGAssumption' {k l : ℕ} (prg : PRG k l) :
    IndAssumptions Unit where
  assumptions := fun _ => SecurePRGAssumptionFull prg

/-- PRG security definition as an instance of `Indistinguishable`. -/
def SecurePRGDef
    {Idx : Type} (Assumptions : IndAssumptions Idx)
    {k l : ℕ} (prg : PRG k l) : Type 1 :=
  IndistinguishableSingle Assumptions
    (PRG_real prg) (PRG_rand k l)

/-- Pointwise PRG assumptions for a PRG family. -/
noncomputable def SecurePRGAssumptionFam {k l : ℕ → ℕ}
    (prgFam : PRGFamily k l) (κ : ℕ) : IndAssumptions Unit :=
  SecurePRGAssumption' (prgFam.prg κ)

/-- PRG security for a PRG family. -/
def SecurePRGIFam
    {Idx : Type} (Assumptions : (κ : ℕ) → IndAssumptions Idx)
    {k l : ℕ → ℕ} (prgFam : PRGFamily k l) : Type 1 :=
  ∀ κ,
    IndistinguishableI (Assumptions κ) none
      (PRG_real (prgFam.prg κ)) (PRG_rand (k κ) (l κ))
