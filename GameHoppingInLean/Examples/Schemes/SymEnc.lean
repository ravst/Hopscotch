import GameHoppingInLean.StatefulRandomOracle

/-- Symmetric encryption scheme with abstract key type `K`.
Encryption/decryption preserve message length by type. -/
structure SymEncScheme (K : Type) (C : (msg_len : ℕ) → Type) where
  keyGen : PMF K
  encrypt : {msg_len : ℕ} → K → BitVec msg_len → PMF (C msg_len)
  decrypt : {msg_len : ℕ} → K → C msg_len → BitVec msg_len

structure SymEncSchemeFamily (K : ℕ → Type) (C : (κ : ℕ) → (msg_len : ℕ) → Type) where
  scheme : (κ : ℕ) → SymEncScheme (K κ) (C κ)
