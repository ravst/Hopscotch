import GameHoppingInLean.StatefulRandomOracle

/-- Symmetric encryption scheme with abstract key type `K`.
Encryption/decryption preserve message length by type. -/
structure SymEncScheme (K : Type) where
  keyGen : PMF K
  encrypt : {n : ℕ} → K → BitVec n → PMF (BitVec n)
  decrypt : {n : ℕ} → K → BitVec n → BitVec n
