import Hopscotch.Indistinguishability.Def

/-!
# Single-challenge public-key IND-CCA

The interface reveals the public key, permits one left/right challenge, and
provides decryption queries. Implementations return `none` for repeated
challenges, decryption of the challenge ciphertext, and invalid ciphertexts.
-/

/-- Queries of the single-challenge public-key IND-CCA experiment. -/
inductive IndCcaPubQ (M C : Type) where
  | getPublicKey
  | challenge (m0 m1 : M)
  | decrypt (ct : C)

/-- Public-key IND-CCA interface, independent of the encryption construction. -/
def IndCcaPubSpec (PubK M C : Type) : OracleSpec (IndCcaPubQ M C)
  | .getPublicKey => PubK
  | .challenge _ _ => Option C
  | .decrypt _ => Option M
