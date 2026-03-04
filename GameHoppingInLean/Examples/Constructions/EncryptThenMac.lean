import GameHoppingInLean.Examples.Schemes.SymEnc
import GameHoppingInLean.Examples.Schemes.MAC

/-- Encrypt-then-MAC composition.

Given an encryption scheme and a MAC scheme over bitvectors, build a new symmetric
scheme whose ciphertext is a pair `(c, t)` where `c` is the underlying encryption
ciphertext and `t` is a tag over `c`.

If tag verification fails during decryption, return the all-zero bitvector. -/
noncomputable def encryptThenMac {KEnc KMac Tag : Type} [DecidableEq Tag]
    (enc : SymEncScheme KEnc BitVec) (mac : MACScheme KMac Tag) :
    SymEncScheme (KMac × KEnc) (fun n => BitVec n × Tag) where
  keyGen := do
    let ke ← enc.keyGen
    let km ← mac.keyGen
    pure (km, ke)
  encrypt := fun {_n} ⟨km, ke⟩ m => do
    let c ← enc.encrypt ke m
    pure (c, mac.tag km c)
  decrypt := fun {n} ⟨km, ke⟩ ct =>
    let (c, t) := ct
    if mac.check km c t then
      enc.decrypt ke c
    else
      BitVec.zero n
