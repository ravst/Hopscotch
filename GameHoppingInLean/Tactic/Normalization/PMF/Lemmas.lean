import GameHoppingInLean.Tactic.Normalization.PMF.Attrs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ToMathlib.General

namespace PMF

@[GameHoppingSimplifyPMF]
lemma map_pure_eq_pure {α β : Type} (f : α → β) (a : α) :
    PMF.map f (PMF.pure a) = PMF.pure (f a) := by
  exact PMF.pure_map f a

@[GameHoppingSimplifyPMF]
lemma monad_map_pure_eq_pure {α β : Type} (f : α → β) (a : α) :
    f <$> (PMF.pure a) = PMF.pure (f a) := by
  rw [PMF.monad_map_eq_map]
  exact PMF.map_pure_eq_pure f a

/-- Rewriting a uniform draw over a product type as two independent uniform draws. -/
@[GameHoppingSimplifyPMF]
lemma uniformOfFintype_prod_bind
    {A B α : Type}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (f : A × B → PMF α) :
    (PMF.uniformOfFintype (A × B)).bind f =
      (PMF.uniformOfFintype A).bind (fun a =>
        (PMF.uniformOfFintype B).bind (fun b => f (a, b))) := by
  ext x
  have hprod :
      (∑' i : A × B, (f i) x) = ∑' i : A, ∑' j : B, (f (i, j)) x := by
    simpa using (ENNReal.tsum_prod' (f := fun p : A × B => (f p) x))
  simp [PMF.bind_apply, Fintype.card_prod, ENNReal.mul_inv, ENNReal.tsum_mul_left,
    mul_assoc, mul_left_comm, mul_comm, hprod]
  simp [<-Finset.mul_sum]
  rw [Fintype.sum_prod_type fun x_1 ↦ (f x_1) x]

/-- Rewrite a raw `PMF.bind` into monadic `do` notation. -/
@[GameHoppingPrettyPrintPMF]
theorem bind_eq_do {α β : Type} (A : PMF α) (X : α → PMF β) :
    A.bind (fun a => X a) = (do
      let a ← A
      X a) := by
  rfl

/-- Rewrite a `PMF.map` into monadic form. -/
@[GameHoppingPrettyPrintPMF]
theorem map_eq_do {α β : Type} (p : PMF α) (f : α → β) :
    p.map f = (do
      let x ← p
      pure (f x)) := by
  simpa [Function.comp] using (PMF.bind_pure_comp (p := p) (f := f)).symm

/-- Rewrite `PMF.map` into raw `PMF.bind` form for PMF normalization. -/
@[GameHoppingSimplifyPMF]
theorem map_eq_bind_pure {α β : Type} (p : PMF α) (f : α → β) :
    p.map f = PMF.bind p (fun x => PMF.pure (f x)) := by
  simpa [Function.comp] using (PMF.bind_pure_comp (p := p) (f := f)).symm

/-- Rewrite monadic map notation into monadic `do` notation. -/
@[GameHoppingPrettyPrintPMF]
theorem monad_map_eq_do {α β : Type} (f : α → β) (A : PMF α) :
    f <$> A = (do
      let x ← A
      pure (f x)) := by
  rw [PMF.monad_map_eq_map]
  exact PMF.map_eq_do A f

/-- Eliminate a pure bind in monadic form. -/
@[GameHoppingSimplifyPMF]
theorem pure_bind_do {α β : Type} (a : α) (f : α → PMF β) :
    (do
      let x ← (PMF.pure a : PMF α)
      f x) = f a := by
  exact PMF.pure_bind a f

/-- Rewrite `PMF.pure` back to monadic `pure` when using the custom PMF simp set. -/
@[GameHoppingPrettyPrintPMF]
theorem pure_eq_monad_pure {α : Type} (a : α) :
    PMF.pure a = @Pure.pure PMF (inferInstance : Pure PMF) α a := rfl

/-- Eliminate an identity bind in monadic form. -/
@[GameHoppingSimplifyPMF]
theorem bind_pure_do {α : Type} (p : PMF α) :
    (do
      let x ← p
      pure x) = p := by
  change p.bind (pure ∘ id) = p
  rw [PMF.bind_pure_comp, PMF.map_id]

/-- Eliminate a bind whose sampled value is unused. -/
@[GameHoppingSimplifyPMF]
theorem bind_const_do {α β : Type} (m : PMF α) (rest : PMF β) :
    (do
      let _x ← m
      rest) = rest := by
  exact PMF.bind_const m rest

/-- Eliminate a raw `PMF.bind` whose sampled value is unused. -/
@[GameHoppingSimplifyPMF]
theorem bind_const_raw {α β : Type} (m : PMF α) (rest : PMF β) :
    PMF.bind m (fun _x => rest) = rest := by
  exact PMF.bind_const m rest

/-- Every `PMF Unit` is concentrated on `()`. -/
theorem unit_eq_pure (m : PMF Unit) :
    m = PMF.pure () := by
  ext x
  cases x
  have hsum : (∑' x : Unit, m x) = 1 := m.tsum_coe
  have hsingle : (∑' x : Unit, m x) = m () := by
    simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
  rw [PMF.pure_apply_self]
  exact hsingle.symm.trans hsum

/-- Eliminate a bind over a `PMF Unit`. -/
@[GameHoppingSimplifyPMF]
theorem unit_bind_do {α : Type} (m : PMF Unit) (f : Unit → PMF α) :
    (do
      let x ← m
      f x) = f () := by
  rw [PMF.unit_eq_pure m]
  exact PMF.pure_bind () f

/-- Pull an `if` out of a monadic bind in `do` notation. -/
@[GameHoppingSimplifyPMF]
theorem monad_ite_bind_do {α β : Type} (p : Prop) [Decidable p]
    (A B : PMF α) (rest : α → PMF β) :
    ((if p then A else B) >>= rest) =
    if p then
      A.bind rest
    else
      B.bind rest := by
  split_ifs <;> rfl

/-- Pull an `if` out of a `PMF` bind. -/
@[GameHoppingSimplifyPMF]
theorem ite_bind_do {α β : Type} (p : Prop) [Decidable p]
    (A B : PMF α) (rest : α → PMF β) :
    (do
      let x ← if p then A else B
      rest x) =
    if p then
      A.bind rest
    else
      B.bind rest := by
  split_ifs <;> rfl

/-- Reassociate nested binds into raw `PMF.bind` form. -/
@[GameHoppingSimplifyPMF]
theorem bind_assoc_do {α β γ : Type} (p : PMF α) (f : α → PMF β) (g : β → PMF γ) :
    (do
      let y ← (do
        let x ← p
        f x)
      g y) =
    PMF.bind p (fun x => PMF.bind (f x) g) := by
  exact bind_assoc p f g

/-- Push a bind past a mapped input, keeping the result in raw `PMF.bind` form. -/
@[GameHoppingSimplifyPMF]
theorem bind_map_do {α β γ : Type} (p : PMF α) (f : α → β) (q : β → PMF γ) :
    (do
      let y ← p.map f
      q y) =
    PMF.bind p (fun x => q (f x)) := by
  change (p.map f).bind q = p.bind (fun x => q (f x))
  rw [PMF.bind_map]
  rfl

/-- Raw `PMF.bind` form of `bind_map_do`. -/
@[GameHoppingSimplifyPMF]
theorem bind_map_raw {α β γ : Type} (p : PMF α) (f : α → β) (q : β → PMF γ) :
    PMF.bind (PMF.map f p) q =
    PMF.bind p (fun x => q (f x)) := by
  rw [PMF.bind_map]
  rfl

/-- Push a map through a bind, keeping the result in raw `PMF` form. -/
@[GameHoppingSimplifyPMF]
theorem map_bind_do {α β γ : Type} (p : PMF α) (f : α → PMF β) (g : β → γ) :
    PMF.map g (do
      let x ← p
      f x) =
    PMF.bind p (fun x => PMF.map g (f x)) := by
  change (p.bind f).map g = p.bind (fun x => (f x).map g)
  simpa using (PMF.map_bind (p := p) (q := f) (f := g))

/-- Raw `PMF.bind` form of `map_bind_do`. -/
@[GameHoppingSimplifyPMF]
theorem map_bind_raw {α β γ : Type} (p : PMF α) (f : α → PMF β) (g : β → γ) :
    PMF.map g (PMF.bind p f) =
    PMF.bind p (fun x => PMF.map g (f x)) := by
  simpa using (PMF.map_bind (p := p) (q := f) (f := g))

/-- Transporting a uniform `PMF` sample across an equivalence. -/
theorem bind_uniformOfFintype_equiv {X Y α : Type}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (e : X ≃ Y) (g : Y → PMF α) :
    (PMF.uniformOfFintype Y).bind g =
      (PMF.uniformOfFintype X).bind (fun x => g (e x)) := by
  ext a
  have htsum :
      ∑' y : Y, ((Fintype.card Y : ENNReal)⁻¹ * (g y) a) =
        ∑' x : X, ((Fintype.card Y : ENNReal)⁻¹ * (g (e x)) a) := by
    simpa using
      (Equiv.tsum_eq e (fun y : Y => ((Fintype.card Y : ENNReal)⁻¹ * (g y) a))).symm
  calc
    ((PMF.uniformOfFintype Y).bind g) a =
        ∑' y : Y, ((Fintype.card Y : ENNReal)⁻¹ * (g y) a) := by
          simp [PMF.bind_apply, PMF.uniformOfFintype_apply]
    _ = ∑' x : X, ((Fintype.card Y : ENNReal)⁻¹ * (g (e x)) a) := htsum
    _ = ((PMF.uniformOfFintype X).bind (fun x => g (e x))) a := by
          simp [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_congr e]

/-- Mapping a uniform `PMF` through an equivalence gives the uniform `PMF`. -/
@[GameHoppingSimplifyPMF]
theorem map_uniformOfFintype_equiv {X Y : Type}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] (e : X ≃ Y) :
    (PMF.uniformOfFintype X).bind (fun x => pure (e x)) = PMF.uniformOfFintype Y := by
  simpa using
    (PMF.bind_uniformOfFintype_equiv
      (e := e) (g := (PMF.pure : Y → PMF Y))).symm

/-- Split a function into its value at one point and its values everywhere else. -/
noncomputable def evalFunctionEquiv (X Y : Type) [DecidableEq X] (x : X) :
    (X → Y) ≃ Y × ({x' : X // x' ≠ x} → Y) where
  toFun f := (f x, fun x' => f x')
  invFun p x' := if h : x' = x then p.1 else p.2 ⟨x', h⟩
  left_inv f := by
    funext x'
    by_cases h : x' = x
    · subst x'
      simp
    · simp [h]
  right_inv p := by
    apply Prod.ext
    · simp
    · funext x'
      simp [x'.2]

/-- Sampling a uniform function and evaluating it at one fixed input is the same as
sampling a uniform value directly. -/
@[GameHoppingSimplifyPMF]
theorem bind_uniformOfFintype_eval_do {X Y α : Type}
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (x : X) (rest : Y → PMF α) :
    (do
      let f ← PMF.uniformOfFintype (X → Y)
      rest (f x)) =
    (do
      let y ← PMF.uniformOfFintype Y
      rest y) := by
  let rest' : Y × ({x' : X // x' ≠ x} → Y) → PMF α := fun p => rest p.1
  calc
    (do
      let f ← PMF.uniformOfFintype (X → Y)
      rest (f x)) =
        (PMF.uniformOfFintype (Y × ({x' : X // x' ≠ x} → Y))).bind rest' := by
          simpa [rest', evalFunctionEquiv] using
            (PMF.bind_uniformOfFintype_equiv
              (e := PMF.evalFunctionEquiv X Y x) (g := rest')).symm
    _ =
      (do
        let y ← PMF.uniformOfFintype Y
        rest y) := by
          rw [PMF.uniformOfFintype_prod_bind]
          simp [rest', PMF.bind_const]

@[GameHoppingSimplifyPMF]
lemma ite_pure {α} (p : Prop) [Decidable p] (a b : α) :
      (if p then (pure a : PMF α) else pure b) =
      (pure (if p then a else b) : PMF α)
       := by
  split_ifs <;> rfl

/-- Commuting two independent `PMF` draws.

Not marked `[simp]` to avoid commutativity rewrite loops. -/
lemma do_bind_comm {α β γ}
    (A : PMF α) (B : PMF β) (rest : α → β → PMF γ) :
    (do
      let x ← A
      let y ← B
      rest x y) =
    (do
      let y ← B
      let x ← A
      rest x y) := by
  simpa using (PMF.bind_comm (p := A) (q := B) (f := rest))

/-- Commuting two independent raw `PMF.bind` draws.

Not marked `[simp]` to avoid commutativity rewrite loops. -/
lemma bind_bind_comm {α β γ}
    (A : PMF α) (B : PMF β) (rest : α → β → PMF γ) :
    A.bind (fun x => B.bind (fun y => rest x y)) =
      B.bind (fun y => A.bind (fun x => rest x y)) := by
  simpa using (PMF.bind_comm (p := A) (q := B) (f := rest))

/-- Commute the second and third draws inside an outer `PMF.bind`.

This is useful when the third draw depends on the outer sample but is independent of the
second draw. -/
lemma bind_bind_bind_comm_middle {α β γ δ}
    (A : PMF α) (B : PMF β) (C : α → PMF γ)
    (rest : α → β → γ → PMF δ) :
    A.bind (fun x => B.bind (fun y => (C x).bind (fun z => rest x y z))) =
      A.bind (fun x => (C x).bind (fun z => B.bind (fun y => rest x y z))) := by
  apply congrArg (fun f => PMF.bind A f)
  funext x
  exact PMF.bind_bind_comm B (C x) (fun y z => rest x y z)

/-- Commute the second and third draws inside an outer monadic `PMF` bind. -/
lemma do_bind_comm_middle {α β γ δ}
    (A : PMF α) (B : PMF β) (C : α → PMF γ)
    (rest : α → β → γ → PMF δ) :
    (do
      let x ← A
      let y ← B
      let z ← C x
      rest x y z) =
    (do
      let x ← A
      let z ← C x
      let y ← B
      rest x y z) := by
  simpa using PMF.bind_bind_bind_comm_middle A B C rest

/-- Commuting a raw `PMF.bind` past an independent raw `PMF.map`.

Not marked `[simp]` to avoid commutativity rewrite loops. -/
lemma bind_map_comm {α β γ}
    (A : PMF α) (B : PMF β) (rest : α → β → γ) :
    A.bind (fun x => B.map (fun y => rest x y)) =
      B.bind (fun y => A.map (fun x => rest x y)) := by
  simp_rw [← PMF.bind_pure_comp]
  simpa [Function.comp] using
    (PMF.bind_comm (p := A) (q := B) (f := fun x y => PMF.pure (rest x y)))

/-- Commuting a monadic `PMF` bind past an independent monadic `PMF` map.

Not marked `[simp]` to avoid commutativity rewrite loops. -/
lemma do_bind_map_comm {α β γ}
    (A : PMF α) (B : PMF β) (rest : α → β → γ) :
    (do
      let x ← A
      rest x <$> B) =
    (do
      let y ← B
      (fun x => rest x y) <$> A) := by
  simpa [PMF.monad_map_eq_map] using
    (PMF.do_bind_comm A B (fun x y => pure (rest x y)))

end PMF
