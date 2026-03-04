import GameHoppingInLean.StatefulRandomOracle

/-- Symmetric encryption scheme with abstract key type `K`.
Encryption/decryption preserve message length by type. -/
structure SymEncScheme (K : Type) (C : ℕ → Type) where
  keyGen : PMF K
  encrypt : {n : ℕ} → K → BitVec n → PMF (C n)
  decrypt : {n : ℕ} → K → C n → BitVec n
