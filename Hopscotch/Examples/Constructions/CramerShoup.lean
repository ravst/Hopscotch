import Hopscotch.Comp.StatefulRandomOracle

/-!
# Cramer--Shoup public-key encryption

The cyclic group is represented additively as a module `V` over a finite
field `F`. Thus a textbook power `g ^ x` is written `x • g`, multiplication
of group elements is addition, and inversion is negation.

This file contains only the cryptographic construction. The proof-specific
simulators, ghost state, bad events, and intermediate games live in
`Hopscotch.Examples.Proofs.CramerShoupIndCca`.
-/

namespace Hopscotch.CramerShoup

/-- A keyed hash family for the first three components of a ciphertext. -/
structure HashFamily (F V HashKey : Type) where
  keyGen : PMF HashKey
  hash : HashKey → V → V → V → F

/-- Secret exponents together with the hash key. -/
structure SecretKey (F HashKey : Type) where
  hashKey : HashKey
  x1 : F
  x2 : F
  y1 : F
  y2 : F
  z1 : F
  z2 : F
deriving Repr

/-- The public key `(hk, g₁, g₂, c, d, h)` in additive notation. -/
structure PublicKey (F V HashKey : Type) where
  hashKey : HashKey
  g1 : V
  g2 : V
  c : V
  d : V
  h : V
deriving Repr

/-- A ciphertext `(u₁, u₂, e, v)` in additive notation. -/
structure Ciphertext (V : Type) where
  u1 : V
  u2 : V
  e : V
  v : V
deriving DecidableEq, Repr

/-- Derive the public key from the generators and secret key. -/
def publicKey
    {F V HashKey : Type} [Semiring F] [AddCommMonoid V] [Module F V]
    (g1 g2 : V) (sk : SecretKey F HashKey) : PublicKey F V HashKey :=
  { hashKey := sk.hashKey
    g1 := g1
    g2 := g2
    c := sk.x1 • g1 + sk.x2 • g2
    d := sk.y1 • g1 + sk.y2 • g2
    h := sk.z1 • g1 + sk.z2 • g2 }

/-- Sample a Cramer--Shoup key pair for fixed public generators. -/
noncomputable def keyGen
    {F V HashKey : Type} [Field F] [Fintype F]
    [AddCommGroup V] [Module F V]
    (hf : HashFamily F V HashKey) (g1 g2 : V) :
    PMF (PublicKey F V HashKey × SecretKey F HashKey) := do
  let hk ← hf.keyGen
  let x1 ← PMF.uniformOfFintype F
  let x2 ← PMF.uniformOfFintype F
  let y1 ← PMF.uniformOfFintype F
  let y2 ← PMF.uniformOfFintype F
  let z1 ← PMF.uniformOfFintype F
  let z2 ← PMF.uniformOfFintype F
  let sk : SecretKey F HashKey :=
    { hashKey := hk
      x1 := x1
      x2 := x2
      y1 := y1
      y2 := y2
      z1 := z1
      z2 := z2 }
  pure (publicKey g1 g2 sk, sk)

/-- Deterministic encryption with explicitly supplied coins. -/
def encryptWithCoins
    {F V HashKey : Type} [CommSemiring F]
    [AddCommMonoid V] [Module F V]
    (hf : HashFamily F V HashKey) (pk : PublicKey F V HashKey)
    (message : V) (r : F) : Ciphertext V :=
  let u1 := r • pk.g1
  let u2 := r • pk.g2
  let e := r • pk.h + message
  let alpha := hf.hash pk.hashKey u1 u2 e
  let v := r • pk.c + (r * alpha) • pk.d
  { u1 := u1, u2 := u2, e := e, v := v }

/-- Probabilistic encryption samples uniform field coins. -/
noncomputable def encrypt
    {F V HashKey : Type} [Field F] [Fintype F]
    [AddCommGroup V] [Module F V]
    (hf : HashFamily F V HashKey) (pk : PublicKey F V HashKey)
    (message : V) : PMF (Ciphertext V) := do
  let r ← PMF.uniformOfFintype F
  pure (encryptWithCoins hf pk message r)

/-- The Cramer--Shoup verification equation. -/
def valid
    {F V HashKey : Type} [CommSemiring F]
    [AddCommMonoid V] [Module F V]
    (hf : HashFamily F V HashKey) (sk : SecretKey F HashKey)
    (ct : Ciphertext V) : Prop :=
  let alpha := hf.hash sk.hashKey ct.u1 ct.u2 ct.e
  ct.v = (sk.x1 + alpha * sk.y1) • ct.u1 +
    (sk.x2 + alpha * sk.y2) • ct.u2

open scoped Classical in
/-- Reject invalid ciphertexts; otherwise remove the message mask. -/
noncomputable def decrypt
    {F V HashKey : Type} [Field F]
    [AddCommGroup V] [Module F V]
    (hf : HashFamily F V HashKey) (sk : SecretKey F HashKey)
    (ct : Ciphertext V) : Option V :=
  if valid hf sk ct then
    some (ct.e - (sk.z1 • ct.u1 + sk.z2 • ct.u2))
  else
    none

/-- Honest ciphertexts satisfy the verification equation. -/
theorem valid_encryptWithCoins
    {F V HashKey : Type} [Field F]
    [AddCommGroup V] [Module F V]
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (sk : SecretKey F HashKey) (message : V) (r : F) :
    valid hf sk (encryptWithCoins hf (publicKey g1 g2 sk) message r) := by
  simp only [valid, encryptWithCoins, publicKey]
  module

/-- Decryption recovers the message from an honestly generated ciphertext. -/
@[simp]
theorem decrypt_encryptWithCoins
    {F V HashKey : Type} [Field F]
    [AddCommGroup V] [Module F V]
    (hf : HashFamily F V HashKey) (g1 g2 : V)
    (sk : SecretKey F HashKey) (message : V) (r : F) :
    decrypt hf sk (encryptWithCoins hf (publicKey g1 g2 sk) message r) =
      some message := by
  rw [decrypt, if_pos (valid_encryptWithCoins hf g1 g2 sk message r)]
  simp only [encryptWithCoins, publicKey, Option.some.injEq]
  module

end Hopscotch.CramerShoup
