import GameHoppingInLean.Misc.PMFSimpAttr
import GameHoppingInLean.MonadRandomState
import GameHoppingInLean.VCVio2.ToMathlib.General
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open Lean Meta

namespace PMF

 /-- Rewrite a raw `PMF.bind` into monadic `do` notation. -/
@[GameHoppingSimplifyPMF]
theorem bind_eq_do {α β : Type} (A : PMF α) (X : α → PMF β) :
    A.bind (fun a => X a) = (do
      let a ← A
      X a) := by
  exact (PMF.monad_bind_eq_bind A X).symm

/-- Rewrite a `PMF.map` into monadic form. -/
@[GameHoppingSimplifyPMF]
theorem map_eq_do {α β : Type} (p : PMF α) (f : α → β) :
    p.map f = (do
      let x ← p
      pure (f x)) := by
  simpa [Function.comp] using (PMF.bind_pure_comp (p := p) (f := f)).symm

/-- Rewrite monadic map notation into monadic `do` notation. -/
@[GameHoppingSimplifyPMF]
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
@[GameHoppingSimplifyPMF]
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
      (do
        let x ← A
        rest x)
    else
      (do
        let x ← B
        rest x) := by
  split_ifs <;> rfl

/-- Pull an `if` out of a monadic bind in `do` notation. -/
@[GameHoppingSimplifyPMF]
theorem ite_bind_do {α β : Type} (p : Prop) [Decidable p]
    (A B : PMF α) (rest : α → PMF β) :
    (do
      let x ← if p then A else B
      rest x) =
    if p then
      (do
        let x ← A
        rest x)
    else
      (do
        let x ← B
        rest x) := by
  split_ifs <;> rfl

/-- Reassociate nested binds into a left-to-right `do` block. -/
@[GameHoppingSimplifyPMF]
theorem bind_assoc_do {α β γ : Type} (p : PMF α) (f : α → PMF β) (g : β → PMF γ) :
    (do
      let y ← (do
        let x ← p
        f x)
      g y) =
    (do
      let x ← p
      let y ← f x
      g y) := by
  exact bind_assoc p f g

/-- Push a bind past a mapped input, keeping the result in monadic form. -/
@[GameHoppingSimplifyPMF]
theorem bind_map_do {α β γ : Type} (p : PMF α) (f : α → β) (q : β → PMF γ) :
    (do
      let y ← p.map f
      q y) =
    (do
      let x ← p
      q (f x)) := by
  change (p.map f).bind q = p.bind (fun x => q (f x))
  rw [PMF.bind_map]
  rfl

/-- Push a map through a bind, keeping the result in monadic form. -/
@[GameHoppingSimplifyPMF]
theorem map_bind_do {α β γ : Type} (p : PMF α) (f : α → PMF β) (g : β → γ) :
    PMF.map g (do
      let x ← p
      f x) =
    (do
      let x ← p
      let y ← f x
      pure (g y)) := by
  change (p.bind f).map g = p.bind (fun x => (f x).map g)
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
    (PMF.uniformOfFintype X).map e = PMF.uniformOfFintype Y := by
  change (PMF.uniformOfFintype X).bind (fun x => PMF.pure (e x)) =
    PMF.uniformOfFintype Y
  simpa using
    (PMF.bind_uniformOfFintype_equiv
      (e := e) (g := (PMF.pure : Y → PMF Y))).symm

/-- Two independent uniform bitvector draws, appended together, are the same as one
uniform draw at the appended width. -/
@[GameHoppingSimplifyPMF]
theorem bind_uniformOfFintype_bitVec_append_do
    {a b : ℕ} {α : Type} (f : BitVec (a + b) → PMF α) :
    (do
      let x₁ ← PMF.uniformOfFintype (BitVec a)
      let x₂ ← PMF.uniformOfFintype (BitVec b)
      f (x₁ ++ x₂)) =
    (do
      let x ← PMF.uniformOfFintype (BitVec (a + b))
      f x) := by
  change (PMF.uniformOfFintype (BitVec a)).bind
      (fun x₁ => (PMF.uniformOfFintype (BitVec b)).bind
        (fun x₂ => f (x₁ ++ x₂))) =
    (PMF.uniformOfFintype (BitVec (a + b))).bind f
  rw [← PMF.uniformOfFintype_prod_bind
    (f := fun p : BitVec a × BitVec b => f (p.1 ++ p.2))]
  exact (PMF.bind_uniformOfFintype_equiv
    (e := RState.bitVecAppendEquiv a b)
    (g := f)).symm

end PMF

namespace PMFSimp

private def mkBindConstRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match e.getAppFnArgs with
  | (``Bind.bind, #[m, _instBind, _α, _β, x, rest]) =>
      let pmfConst ← mkConstWithFreshMVarLevels ``PMF
      unless m.isConstOf ``PMF || (← isDefEq m pmfConst) do
        return none
      let .lam _xName _xTy body _xBi := rest | return none
      if body.hasLooseBVar 0 then
        return none
      let restConst := body.lowerLooseBVars 0 1
      let pf ← mkAppOptM ``PMF.bind_const_do
        #[none, none, some x, some restConst]
      let pfTy ← inferType pf
      let some (_ty, lhs, rhs) := pfTy.eq? | return none
      unless (← isDefEq lhs e) do
        return none
      return some (rhs, pf)
  | _ => return none

private def mkIteBindRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match e.getAppFnArgs with
  | (``Bind.bind, #[m, _instBind, _α, _β, x, rest]) =>
      let pmfConst ← mkConstWithFreshMVarLevels ``PMF
      unless m.isConstOf ``PMF || (← isDefEq m pmfConst) do
        return none
      match x.getAppFnArgs with
      | (``ite, #[_motive, p, instDec, A, B]) =>
          let pf ← mkAppOptM ``PMF.monad_ite_bind_do
            #[none, none, some p, some instDec, some A, some B, some rest]
          let pfTy ← inferType pf
          let some (_ty, lhs, rhs) := pfTy.eq? | return none
          unless (← isDefEq lhs e) do
            return none
          return some (rhs, pf)
      | _ => return none
  | _ => return none

private def mkBitVecAppendUniformRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  try
    let natTy := mkConst ``Nat
    let a ← mkFreshExprMVar natTy
    let b ← mkFreshExprMVar natTy
    let α ← mkFreshTypeMVar
    let ab ← mkAppM ``Nat.add #[a, b]
    let bitVecAB ← mkAppM ``BitVec #[ab]
    let pmfα ← mkAppM ``PMF #[α]
    let fTy ← mkArrow bitVecAB pmfα
    let f ← mkFreshExprMVar fTy
    let pf ← mkAppM ``PMF.bind_uniformOfFintype_bitVec_append_do #[f]
    let pfTy ← inferType pf
    let some (_ty, lhs, rhs) := pfTy.eq? | return none
    unless (← isDefEq lhs e) do
      return none
    return some (← instantiateMVars rhs, ← instantiateMVars pf)
  catch _ =>
    return none

end PMFSimp

/-- Simproc: remove a `PMF` bind when the continuation ignores the sampled value. -/
simproc [GameHoppingSimplifyPMF] pmfBindConst
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkBindConstRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Simproc: pull an `if` out of a `PMF` bind when using the game-hopping PMF simp set. -/
simproc [GameHoppingSimplifyPMF] pmfIteBind
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkIteBindRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Simproc: collapse two uniform `BitVec` draws followed by append into one uniform draw. -/
simproc [GameHoppingSimplifyPMF] pmfBitVecAppendUniform
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkBitVecAppendUniformRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }
