import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Distributions.Uniform
import GameHoppingInLean.IndistinguishabilityDef
import GameHoppingInLean.Examples.Schemes.PRF
import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRF

import Mathlib.Data.Finmap


/-- Ideal random-function oracle.
It samples a uniformly random function `X → Y` once during initialization and answers
each query by applying that sampled function. -/
noncomputable def PRF_ideal2 (X Y : Type) [DecidableEq X] [Fintype Y] [Nonempty Y] :
    RStateOracle (SecurePRFSpec X Y) where
  stateType := Finmap (fun _x : X => Y)
  initialState := pure ∅
  queries := {
    impl := fun _ x => do
      let c <- get
      match c.lookup x with
      | Option.some y => return y
      | Option.none =>
          let newVal ← PMF.uniformOfFintype Y
          StateT.set (c.insert x newVal)
          pure newVal
  }

/-- The eagerly sampled random-function oracle and its lazy cached implementation are
observationally equivalent. -/
theorem obsEq_PRF_ideal_PRF_ideal2 (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    ObsEq (PRF_ideal X Y) (PRF_ideal2 X Y) := by
  sorry

/-- Lift the cached random-function equivalence to indistinguishability. -/
noncomputable def indistinguishable_PRF_ideal_PRF_ideal2
    {Reductions : IndistinguishabilityReductions} (X Y : Type)
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    Indistinguishable IndistinguishabilityAssumptions.empty Reductions
      (PRF_ideal X Y) (PRF_ideal2 X Y) := by
  intro κ
  exact Indistinguishable.of_ObsEq (obsEq_PRF_ideal_PRF_ideal2 X Y)
