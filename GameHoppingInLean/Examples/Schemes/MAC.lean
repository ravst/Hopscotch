import GameHoppingInLean.Comp.StatefulRandomOracle

/-- Message authentication code (MAC) scheme with abstract key and tag types.
Messages are length-indexed bitvectors, key generation is probabilistic,
while tagging is deterministic. -/
structure MACScheme (K Tag : Type) where
  keyGen : PMF K
  tag : {n : ℕ} → K → BitVec n → Tag

structure MACSchemeFamily (K Tag : ℕ → Type) where
  scheme : (κ : ℕ) → MACScheme (K κ) (Tag κ)

/-- Deterministic verification derived from `tag`. -/
def MACScheme.check {K Tag : Type} (scheme : MACScheme K Tag) [DecidableEq Tag]
    {n : ℕ} (key : K) (msg : BitVec n) (tg : Tag) : Bool :=
  decide (scheme.tag key msg = tg)
