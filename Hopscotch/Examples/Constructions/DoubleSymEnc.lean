import Hopscotch.Examples.Schemes.SymEnc

noncomputable def doubleSymEnc {K₁ K₂ : Type} {C : ℕ → Type}
    (S : SymEncScheme K₁ BitVec) (T : SymEncScheme K₂ C) :
    SymEncScheme (K₁ × K₂) C where
  keyGen := do
    let key2 <- T.keyGen
    let key1 <- S.keyGen
    pure (key1, key2)
  encrypt := fun ⟨ks, kt⟩ msg => do
    let enc1 <- S.encrypt ks msg
    T.encrypt kt enc1
  decrypt := fun ⟨ks, kt⟩ ctg =>
    let dec1 := T.decrypt kt ctg
    S.decrypt ks dec1

/-- Family obtained by composing the two scheme families pointwise. -/
noncomputable def doubleSymEncFamily
    {K₁ K₂ : ℕ → Type} {C₂ : ℕ → ℕ → Type}
    (outerFam : SymEncSchemeFamily K₁ (fun _ => BitVec)) (innerFam : SymEncSchemeFamily K₂ C₂) :
    SymEncSchemeFamily (fun κ => K₁ κ × K₂ κ) C₂ where
  scheme := fun κ =>
    doubleSymEnc (outerFam.scheme κ) (innerFam.scheme κ)
