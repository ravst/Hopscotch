import GameHoppingInLean.Comp.StatefulRandomOracle

/-- Public-key encryption scheme with abstract public/secret key, message,
and ciphertext types. -/
structure PubEncScheme (PubK SecK M C : Type) where
  keyGen : PMF (PubK × SecK)
  encrypt : PubK → M → PMF C
  decrypt : SecK → C → M

/-- Family of public-key encryption schemes indexed by a security parameter. -/
structure PubEncSchemeFamily
    (PubK SecK M C : ℕ → Type) where
  scheme : (κ : ℕ) → PubEncScheme (PubK κ) (SecK κ) (M κ) (C κ)
