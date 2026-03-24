import GameHoppingInLean.StatefulRandomOracle

/-- Public-key encryption scheme with abstract public/secret key, message,
and ciphertext types. -/
structure PubEncScheme (PubK SecK M C : Type) where
  keyGen : PMF (PubK × SecK)
  encrypt : PubK → M → PMF C
  decrypt : SecK → C → M
