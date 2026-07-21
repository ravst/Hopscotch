import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Distributions.Uniform
import Hopscotch.Indistinguishability.Def
import Hopscotch.Examples.Schemes.PRF

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
    OracleImpl (SecurePRFSpec X Y) where
  stateType := K
  initialState := prf.keyGen
  queries x := do
      let key <- get
      pure (prf.mkFun key x)


/-- Ideal random-function oracle.
It samples a uniformly random function `X → Y` once during initialization and answers
each query by applying that sampled function. -/
noncomputable def PRF_ideal (X Y : Type) [Fintype X] [Fintype Y] [Nonempty Y] :
    OracleImpl (SecurePRFSpec X Y) where
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
    OracleImpl (SecurePRFSpec X Y) × OracleImpl (SecurePRFSpec X Y) :=
  (PRF_real prf, PRF_ideal X Y)

noncomputable def SecurePRFAssumptionFull {K X Y : Type}
    [Fintype X] [Fintype Y] [Nonempty Y] (prf : PRF K X Y) :
    SingleAssumption :=
  { i := SecurePRFAssumption prf }

noncomputable def SecurePRFAssumption' {K X Y : Type}
    [Fintype X] [Fintype Y] [Nonempty Y] (prf : PRF K X Y) :
    IndAssumptions Unit where
  assumptions := fun _ => SecurePRFAssumptionFull prf


noncomputable def SecurePRFAssumptionFam {K X Y : (κ : ℕ) -> Type}
    [forall κ, Fintype (X κ)]
    [forall κ, Fintype (Y κ)]
    [forall κ, Nonempty (Y κ)]
    (prf : (κ : ℕ) -> PRF (K κ) (X κ) (Y κ)) :
    IndAssumptionsFam where
    Idx := Unit
    val κ := {assumptions := fun _ => SecurePRFAssumptionFull (prf κ)}

/-- PRF security definition as an instance of `Indistinguishable`. -/
@[reducible] def SecurePRFDef
    (Assumptions : IndAssumptionsFam)
    {K X Y : (κ : ℕ) -> Type}
    [forall κ, Fintype (X κ)]
    [forall κ, Fintype (Y κ)]
    [forall κ, Nonempty (Y κ)]
    (prf : (κ : ℕ) -> PRF (K κ) (X κ) (Y κ)) : Type 1 :=
  Indistinguishable Assumptions
    (fun κ => PRF_real (prf κ)) (fun κ => PRF_ideal (X κ) (Y κ))
