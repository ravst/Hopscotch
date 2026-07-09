import GameHoppingInLean.Comp.RState
import GameHoppingInLean.Normalization.Group.Attrs


/-- Sample an exponent uniformly in the range `0, ..., |G| - 1`. -/
noncomputable
def sampleExponent (G : Type) [Fintype G] [Nontrivial G] : PMF ℕ :=
  let hcard : 0 < Fintype.card G := Fintype.card_pos_iff.mpr inferInstance
  letI : Nonempty (Fin (Fintype.card G)) := ⟨⟨0, hcard⟩⟩
  (PMF.uniformOfFintype (Fin (Fintype.card G))).map fun x => x.1

/-- `g` generates the whole finite group `G` if exponentiation by `g` gives a bijection from
`Fin |G|` onto `G`. -/
def IsGenerator {G : Type} [Group G] [Fintype G] (g : G) : Prop :=
  Function.Bijective fun x : Fin (Fintype.card G) => g ^ (x : Nat)

/-- The equivalence induced by a generator. -/
noncomputable def generatorEquiv {G : Type} [Group G] [Fintype G] {g : G}
    (hgen : IsGenerator g) : Fin (Fintype.card G) ≃ G :=
  Equiv.ofBijective (fun x : Fin (Fintype.card G) => g ^ (x : Nat)) hgen

@[GH_group_norm]
theorem generatorEquiv_apply {G : Type} [Group G] [Fintype G] {g : G}
    (hgen : IsGenerator g) (x : Fin (Fintype.card G)) :
    generatorEquiv hgen x = g ^ (x : Nat) := rfl

/-- Left multiplication by a fixed group element as an equivalence. -/
def mulLeftEquiv {G : Type} [Group G] (m : G) : G ≃ G where
  toFun x := m * x
  invFun x := m⁻¹ * x
  left_inv := by
    intro x
    simp [mul_assoc]
  right_inv := by
    intro x
    simp [mul_assoc]

@[GH_group_norm]
theorem pow_pow_eq_pow_mul {G : Type} [Group G] (g : G) (a b : Nat) :
    (g ^ a) ^ b = g ^ (a * b) := by
  rw [pow_mul]

namespace PMF

/-- Replacing a generator exponent sample by a uniform group element inside a `PMF` bind. -/
@[GH_group_random_exp]
theorem bind_sampleExponent_pow_eq_bind_uniformOfFintype
    {G α : Type} [Group G] [Fintype G] [Nontrivial G] {g : G}
    (hgen : IsGenerator g) (rest : G → PMF α) :
    PMF.bind (sampleExponent G) (fun x => rest (g ^ x)) =
    PMF.bind (PMF.uniformOfFintype G) rest := by
  let hcard : 0 < Fintype.card G := Fintype.card_pos_iff.mpr inferInstance
  letI : Nonempty (Fin (Fintype.card G)) := ⟨⟨0, hcard⟩⟩
  let e : Fin (Fintype.card G) ≃ G := generatorEquiv hgen
  change
    (sampleExponent G).bind (fun x => rest (g ^ x)) =
      (PMF.uniformOfFintype G).bind rest
  calc
    (sampleExponent G).bind (fun x => rest (g ^ x))
      = (PMF.uniformOfFintype (Fin (Fintype.card G))).bind
          (fun x => rest (g ^ (x : Nat))) := by
            rw [sampleExponent, PMF.bind_map]
            rfl
    _ = (PMF.uniformOfFintype (Fin (Fintype.card G))).bind (fun x => rest (e x)) := by
          simp [e, generatorEquiv_apply]
    _ = (PMF.uniformOfFintype G).bind rest := by
          simpa using (PMF.bind_uniformOfFintype_equiv (e := e) (g := rest)).symm

/-- A generator raised to a uniformly sampled exponent is itself uniform on `G`. -/
@[GH_group_random_exp]
theorem sampleExponent_pow_eq_uniformOfFintype
    {G : Type} [Group G] [Fintype G] [Nontrivial G] {g : G}
    (hgen : IsGenerator g) :
    PMF.bind (sampleExponent G) (fun x => PMF.pure (g ^ x)) =
      PMF.uniformOfFintype G := by
  calc
    PMF.bind (sampleExponent G) (fun x => PMF.pure (g ^ x)) =
        PMF.bind (PMF.uniformOfFintype G) PMF.pure := by
            simpa using
              (bind_sampleExponent_pow_eq_bind_uniformOfFintype
                (g := g) hgen (rest := PMF.pure))
    _ = PMF.uniformOfFintype G := by
          simp [PMF.bind_pure]

/-- Left multiplication preserves the uniform distribution on a finite group. -/
theorem bind_uniformOfFintype_mul_left_eq_bind_uniformOfFintype
    (G : Type) [Group G] [Fintype G] {α : Type} (m : G) (rest : G → PMF α) :
    PMF.bind (PMF.uniformOfFintype G) (fun x => rest (m * x)) =
    PMF.bind (PMF.uniformOfFintype G) rest := by
  let e : G ≃ G := mulLeftEquiv m
  simpa [e] using (PMF.bind_uniformOfFintype_equiv (e := e) (g := rest)).symm

end PMF
