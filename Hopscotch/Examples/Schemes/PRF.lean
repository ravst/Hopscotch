import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-- Pseudorandom function family indexed by a seed/key type `K`.
`keyGen` samples a seed, and `mkFun k` is the function indexed by that seed. -/
structure PRF (K X Y : Type) where
  keyGen : PMF K
  mkFun : K → X → Y
