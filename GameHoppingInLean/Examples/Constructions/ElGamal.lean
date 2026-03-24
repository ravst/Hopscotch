import GameHoppingInLean.Examples.Schemes.PubEnc
import GameHoppingInLean.Examples.Misc.Groups

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
