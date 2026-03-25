import GameHoppingInLean.Misc.PMFSimpAttr
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

end PMF

namespace PMFSimp

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

end PMFSimp

/-- Simproc: pull an `if` out of a `PMF` bind when using the game-hopping PMF simp set. -/
simproc [GameHoppingSimplifyPMF] pmfIteBind
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkIteBindRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }
