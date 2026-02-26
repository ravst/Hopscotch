import GameHoppingInLean.Examples.Schemes.SymEnc


noncomputable
def doubleSymEnc {K₁ K₂ : Type} (S : SymEncScheme K₁) (T : SymEncScheme K₂) : SymEncScheme (K₁ × K₂) where
  keyGen := do
    let key1 <- S.keyGen
    let key2 <- T.keyGen
    pure (key1, key2)
  encrypt := fun ⟨ks, kt⟩ msg => do
    let enc1 <- S.encrypt ks msg
    T.encrypt kt enc1
  decrypt := fun ⟨ks, kt⟩ ctg =>
    let dec1 := T.decrypt kt ctg
    S.decrypt ks dec1
