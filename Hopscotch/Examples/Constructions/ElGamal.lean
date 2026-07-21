import Hopscotch.Examples.Schemes.PubEnc
import Hopscotch.Examples.Misc.Groups

noncomputable
def ElGamal {G : Type} [Group G] [Fintype G] [Nontrivial G] (g : G) : PubEncScheme G ℕ G (G × G) where
  keyGen := do
    let sk <- sampleExponent G
    let pk := g ^ sk
    pure (pk, sk)
  encrypt := fun pk m => do
    let r <- sampleExponent G
    pure (g ^ r, m * pk ^ r)
  decrypt := fun sk ct =>
    let (c1, c2) := ct
    c2 * (c1 ^ sk)⁻¹

noncomputable def ElGamalFamily (Γ : GroupGeneratorFamily) :
    PubEncSchemeFamily Γ.G (fun _ => ℕ) Γ.G (fun κ => Γ.G κ × Γ.G κ) where
  scheme := fun κ => by
    letI := Γ.group κ
    letI := Γ.fintype κ
    letI := Γ.nontrivial κ
    exact ElGamal (Γ.gen κ)
