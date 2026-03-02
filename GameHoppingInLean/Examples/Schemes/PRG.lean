
import GameHoppingInLean.StatefulRandomOracle

structure PRG (k l : ℕ) where
  draw : (seed : BitVec k) -> BitVec (k + l)

def lengthDoublingPRG (k : ℕ) := PRG k k
