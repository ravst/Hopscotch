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
  stateType := Finmap (fun x : X => Y)
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
