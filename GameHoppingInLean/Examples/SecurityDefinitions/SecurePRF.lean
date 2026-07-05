import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Distributions.Uniform
import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.PRF

/-- PRF security oracle spec.
The single query `ask(x)` takes an input `x : X` and returns an output `y : Y`. -/
def SecurePRFSpec (X Y : Type) : OracleSpec X :=
  fun _ => Y

/-- Convenience query constructor for the PRF oracle query `ask(x)`. -/
@[reducible, inline] def ask {X Y : Type} (x : X) :
    OracleComp (SecurePRFSpec X Y) Y :=
  (SecurePRFSpec X Y).query x

/-- Real PRF oracle.
It samples a key once during initialization and answers each query with `F_k(x)`. -/
noncomputable def PRF_real {K X Y : Type} (prf : PRF K X Y) :
    RStateOracle (SecurePRFSpec X Y) where
  stateType := K
  initialState := prf.keyGen
  queries x := do
      let key <- get
      pure (prf.mkFun key x)


/-- Ideal random-function oracle.
It samples a uniformly random function `X → Y` once during initialization and answers
each query by applying that sampled function. -/
noncomputable def PRF_ideal (X Y : Type) [Fintype X] [Fintype Y] [Nonempty Y] :
    RStateOracle (SecurePRFSpec X Y) where
  stateType := X → Y
  initialState := by
    classical -- to get decidable equality for X
    exact PMF.uniformOfFintype (X → Y)
  queries x := do
      let f <- get
      pure (f x)


/-- The oracle pair corresponding to the PRF security definition, for use in an
`Assumptions` set. -/
noncomputable def SecurePRFAssumption {K X Y : Type}
    [Fintype X] [Fintype Y] [Nonempty Y] (prf : PRF K X Y) :
    RStateOracle (SecurePRFSpec X Y) × RStateOracle (SecurePRFSpec X Y) :=
  (PRF_real prf, PRF_ideal X Y)

noncomputable def SecurePRFAssumptionFull {K X Y : Type}
    [Fintype X] [Fintype Y] [Nonempty Y] (prf : PRF K X Y) :
    SingleAssumption :=
  { i := SecurePRFAssumption prf }

noncomputable def SecurePRFAssumption' {K X Y : Type}
    [Fintype X] [Fintype Y] [Nonempty Y] (prf : PRF K X Y) :
    IndAssumptions where
  Idx := Unit
  assumptions := fun _ => SecurePRFAssumptionFull prf

/-- PRF security definition as an instance of `Indistinguishable`. -/
def SecurePRFDef
    (Assumptions : IndAssumptions)
    -- (Reductions : IndistinguishabilityReductions)
    {K X Y : Type} [Fintype X] [Fintype Y] [Nonempty Y] (prf : PRF K X Y) : Type 1 :=
  IndistinguishableSingle Assumptions
    (PRF_real prf) (PRF_ideal X Y)
