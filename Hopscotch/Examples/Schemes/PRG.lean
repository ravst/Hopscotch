
import Hopscotch.Comp.StatefulRandomOracle

structure PRG (k l : ℕ) where
  draw : (seed : BitVec k) -> BitVec (k + l)

def lengthDoublingPRG (k : ℕ) := PRG k k

structure PRGFamily (k l : ℕ → ℕ) where
  prg : (κ : ℕ) → PRG (k κ) (l κ)

def lengthDoublingPRGFamily (k : ℕ → ℕ) := PRGFamily k k
