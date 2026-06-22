import GameHoppingInLean.MonadRandomState
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

@[simp] theorem generatorEquiv_apply {G : Type} [Group G] [Fintype G] {g : G}
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

namespace PMF

/-- Replacing a generator exponent sample by a uniform group element inside a `PMF` bind. -/
@[GH_group_nom]
theorem bind_sampleExponent_pow_eq_bind_uniformOfFintype
    {G α : Type} [Group G] [Fintype G] [Nontrivial G] {g : G}
    (hgen : IsGenerator g) (rest : G → PMF α) :
    (do
      let x ← sampleExponent G
      rest (g ^ x)) =
    (do
      let elem_x ← PMF.uniformOfFintype G
      rest elem_x) := by
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
          simp [e]
    _ = (PMF.uniformOfFintype G).bind rest := by
          simpa using (RState.bind_uniformOfFintype_equiv (e := e) (g := rest)).symm

/-- A generator raised to a uniformly sampled exponent is itself uniform on `G`. -/
@[GH_group_nom]
theorem sampleExponent_pow_eq_uniformOfFintype
    {G : Type} [Group G] [Fintype G] [Nontrivial G] {g : G}
    (hgen : IsGenerator g) :
    (do
      let x ← sampleExponent G
      pure (g ^ x)) = PMF.uniformOfFintype G := by
  calc
    (do
      let x ← sampleExponent G
      pure (g ^ x)) =
        (do
          let elem_x ← PMF.uniformOfFintype G
          pure elem_x) := by
            simpa using
              (bind_sampleExponent_pow_eq_bind_uniformOfFintype
                (g := g) hgen (rest := PMF.pure))
    _ = PMF.uniformOfFintype G := by
          change (PMF.uniformOfFintype G).bind PMF.pure = PMF.uniformOfFintype G
          simp [ (PMF.bind_pure (p := PMF.uniformOfFintype G))]

/-- Left multiplication preserves the uniform distribution on a finite group. -/
theorem bind_uniformOfFintype_mul_left_eq_bind_uniformOfFintype
    (G : Type) [Group G] [Fintype G] {α : Type} (m : G) (rest : G → PMF α) :
    (do
      let x ← PMF.uniformOfFintype G
      rest (m * x)) =
    (do
      let x ← PMF.uniformOfFintype G
      rest x) := by
  let e : G ≃ G := mulLeftEquiv m
  simpa [e] using (RState.bind_uniformOfFintype_equiv (e := e) (g := rest)).symm

end PMF

namespace RState

/-- Replacing a lifted generator exponent sample by a lifted uniform group element. -/
@[GH_group_nom]
theorem do_liftM_sampleExponent_pow_eq_do_liftM_uniformOfFintype
    {σ G α : Type} [Group G] [Fintype G] [Nontrivial G] {g : G}
    (hgen : IsGenerator g) (rest : G → RState σ α) :
    (do
      let x ← (liftM (sampleExponent G) : RState σ ℕ)
      rest (g ^ x)) =
    (do
      let elem_x ← (liftM (PMF.uniformOfFintype G) : RState σ G)
      rest elem_x) := by
  funext s
  change
    StateT.run (((liftM (sampleExponent G) : RState σ ℕ) >>= fun x => rest (g ^ x)) :
      RState σ α) s =
      StateT.run (((liftM (PMF.uniformOfFintype G) : RState σ G) >>= fun elem_x => rest elem_x) :
        RState σ α) s
  rw [StateT.run_bind, StateT.run_bind]
  simp [StateT.run_lift]
  simpa using
    (PMF.bind_sampleExponent_pow_eq_bind_uniformOfFintype
      (g := g) hgen (rest := fun y => StateT.run (rest y) s))

/-- Left multiplication preserves a lifted uniform draw over a finite group. -/
theorem do_liftM_uniformOfFintype_mul_left_eq_do_liftM_uniformOfFintype
    {σ α : Type} (G : Type) [Group G] [Fintype G] (m : G) (rest : G → RState σ α) :
    (do
      let x ← (liftM (PMF.uniformOfFintype G) : RState σ G)
      rest (m * x)) =
    (do
      let x ← (liftM (PMF.uniformOfFintype G) : RState σ G)
      rest x) := by
  let e : G ≃ G := mulLeftEquiv m
  simpa [e] using (do_liftM_uniformOfFintype_equiv (e := e) (g := rest)).symm

end RState

