import GameHoppingInLean.Tactic.Normalization.Group.Simprocs

/-- A security-parameter-indexed family of finite nontrivial groups with chosen generators. -/
structure GroupGeneratorFamily where
  G : ℕ → Type
  group : ∀ κ, Group (G κ)
  fintype : ∀ κ, Fintype (G κ)
  nontrivial : ∀ κ, Nontrivial (G κ)
  inhabited : ∀ κ, Inhabited (G κ)
  gen : ∀ κ, G κ
  isGenerator : ∀ κ, @IsGenerator (G κ) (group κ) (fintype κ) (gen κ)

namespace GroupGeneratorFamily

instance instGroup (Γ : GroupGeneratorFamily) (κ : ℕ) : Group (Γ.G κ) :=
  Γ.group κ

instance instFintype (Γ : GroupGeneratorFamily) (κ : ℕ) : Fintype (Γ.G κ) :=
  Γ.fintype κ

instance instNontrivial (Γ : GroupGeneratorFamily) (κ : ℕ) : Nontrivial (Γ.G κ) :=
  Γ.nontrivial κ

instance instInhabited (Γ : GroupGeneratorFamily) (κ : ℕ) : Inhabited (Γ.G κ) :=
  Γ.inhabited κ

end GroupGeneratorFamily
