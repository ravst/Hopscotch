import GameHoppingInLean.Examples.Schemes.PRG
import GameHoppingInLean.Examples.Schemes.PRF

-- Construction of a PRG from a length-doubling PRG, following the GGM construction.

/-- First we need to define the first half and the second half of the PRG function -/
def PRG.chooseHalfI {k : ℕ} (arg : BitVec (k + k)) (choose : Bool) : BitVec k :=
  if choose then
    BitVec.extractLsb' k k arg
  else
    BitVec.extractLsb' 0 k arg

def applyPRGs {k : ℕ} (prg : PRG k k) (seed : BitVec k) : {n : ℕ} → BitVec n → BitVec k
  | 0, _ => seed
  | n + 1, bits =>
      let nextSeed := PRG.chooseHalfI (prg.draw seed) (bits.getLsbD 0)
      applyPRGs prg nextSeed (BitVec.extractLsb' 1 n bits)

/-- The GGM construction of a PRG from a length-doubling PRG. -/
noncomputable def GGM {k : ℕ} (prg : PRG k k) (n : ℕ) : PRF (BitVec k) (BitVec n) (BitVec k) where
  keyGen := PMF.uniformOfFintype (BitVec k)
  mkFun := fun k x =>
    applyPRGs prg k x
