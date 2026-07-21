import Hopscotch.Examples.Schemes.PRG

def LengthTriplingPRG {k : ℕ} (inPRG : lengthDoublingPRG k) : PRG k (2*k) where
  draw seed :=
    let rd1 := inPRG.draw seed
    let firstHalf : BitVec k := BitVec.extractLsb' k k rd1
    let secondHalf : BitVec k := BitVec.extractLsb' 0 k rd1
    let rd2 := inPRG.draw secondHalf
    let rd2' : BitVec (2 * k) := cast (by simp [two_mul]) rd2
    BitVec.append firstHalf rd2'

def LengthTriplingPRGFamily {k : ℕ → ℕ}
    (inPRG : lengthDoublingPRGFamily k) : PRGFamily k (fun κ => 2 * k κ) where
  prg κ := LengthTriplingPRG (inPRG.prg κ)
