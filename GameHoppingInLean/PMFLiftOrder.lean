import GameHoppingInLean.MonadRandomState

open Lean Meta

namespace PMF

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

namespace PMFLiftOrder

private def getBind? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Bind.bind, #[m, instBind, α, β, x, f]) => some (m, instBind, α, β, x, f)
  | _ => none

private def getRawPMFBind? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``PMF.bind, #[α, β, x, f]) => some (α, β, x, f)
  | _ => none

private def isPMFExpr (e : Expr) : MetaM Bool := do
  let pmfConst ← mkConstWithFreshMVarLevels ``PMF
  return e.isConstOf ``PMF || (← isDefEq e pmfConst)

private def getPMFMap? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Expr × Expr)) := do
  match e.getAppFnArgs with
  | (``Functor.map, #[m, instFunctor, α, β, f, x]) =>
      if ← isPMFExpr m then
        return some (m, instFunctor, α, β, f, x)
      else
        return none
  | _ => return none

private def getRawPMFMap? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``PMF.map, #[α, β, f, x]) => some (α, β, f, x)
  | _ => none

private def getLiftMPMFArg? (e : Expr) : MetaM (Option Expr) := do
  match e.getAppFnArgs with
  | (``liftM, #[m, _n, _inst, _α, x]) =>
      let pmfConst ← mkConstWithFreshMVarLevels ``PMF
      if m.isConstOf ``PMF then
        return some x
      else if (← isDefEq m pmfConst) then
        return some x
      else
        return none
  | _ => return none

private partial def firstBinderUse? (e : Expr) (depth : Nat := 0) : Option Bool :=
  match e with
  | .bvar idx =>
      if idx == depth then
        some true
      else if idx == depth + 1 then
        some false
      else
        none
  | .app f a =>
      match firstBinderUse? f depth with
      | some b => some b
      | none => firstBinderUse? a depth
  | .lam _ _ body _ => firstBinderUse? body (depth + 1)
  | .forallE _ _ body _ => firstBinderUse? body (depth + 1)
  | .letE _ _ value body _ =>
      match firstBinderUse? value depth with
      | some b => some b
      | none => firstBinderUse? body (depth + 1)
  | .mdata _ body => firstBinderUse? body depth
  | .proj _ _ body => firstBinderUse? body depth
  | _ => none

private def mkRawPMFSwapProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_α, _γ, A, f) := getRawPMFBind? e | return none
  let .lam xName xTy body xBi := f | return none
  let some (_β, _γ2, B, g) := getRawPMFBind? body | return none
  if B.hasLooseBVar 0 then
    return none
  let .lam yName yTy body2 yBi := g | return none
  let some true := firstBinderUse? body2 | return none

  let restFn := Expr.lam xName xTy (Expr.lam yName yTy body2 yBi) xBi
  let pf ← mkAppM ``PMF.bind_bind_comm #[A, B, restFn]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkPMFSwapProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (m, _inst, _α, _γ, A, f) := getBind? e | return none
  unless (← isPMFExpr m) do
    return none
  let .lam xName xTy body xBi := f | return none
  let some (m2, _inst2, _β, _γ2, B, g) := getBind? body | return none
  unless (← isPMFExpr m2) do
    return none
  if B.hasLooseBVar 0 then
    return none
  let .lam yName yTy body2 yBi := g | return none
  let some true := firstBinderUse? body2 | return none

  let restFn := Expr.lam xName xTy (Expr.lam yName yTy body2 yBi) xBi
  let pf ← mkAppM ``PMF.do_bind_comm #[A, B, restFn]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkRawPMFBindMapSwapProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_α, _γ, A, f) := getRawPMFBind? e | return none
  let .lam xName xTy body xBi := f | return none
  let some (_β, _γ2, g, B) := getRawPMFMap? body | return none
  if B.hasLooseBVar 0 then
    return none
  let .lam yName yTy body2 yBi := g | return none
  let some true := firstBinderUse? body2 | return none

  let restFn := Expr.lam xName xTy (Expr.lam yName yTy body2 yBi) xBi
  let pf ← mkAppM ``PMF.bind_map_comm #[A, B, restFn]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkPMFBindMapSwapProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (m, _inst, _α, _γ, A, f) := getBind? e | return none
  unless (← isPMFExpr m) do
    return none
  let .lam xName xTy body xBi := f | return none
  let some (_m2, _inst2, _β, _γ2, g, B) ← getPMFMap? body | return none
  if B.hasLooseBVar 0 then
    return none
  let .lam yName yTy body2 yBi := g | return none
  let some true := firstBinderUse? body2 | return none

  let restFn := Expr.lam xName xTy (Expr.lam yName yTy body2 yBi) xBi
  let pf ← mkAppM ``PMF.do_bind_map_comm #[A, B, restFn]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkSwapProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_m, _inst, _α, _γ, x, f) := getBind? e | return none
  let some A ← getLiftMPMFArg? x | return none
  let .lam xName xTy body xBi := f | return none
  let some (_m2, _inst2, _β, _γ2, y, g) := getBind? body | return none
  if y.hasLooseBVar 0 then
    return none
  let some B ← getLiftMPMFArg? y | return none
  let .lam yName yTy body2 yBi := g | return none
  let some true := firstBinderUse? body2 | return none

  let restFn := Expr.lam xName xTy (Expr.lam yName yTy body2 yBi) xBi
  let pf ← mkAppM ``RState.do_liftM_comm #[A, B, restFn]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkSwapDepProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_m, _inst, _α, _δ, x, f) := getBind? e | return none
  let some B ← getLiftMPMFArg? x | return none
  let .lam xName xTy body xBi := f | return none

  let some (_m2, _inst2, _β, _δ2, y, g) := getBind? body | return none
  if y.hasLooseBVar 0 then
    return none
  let some A ← getLiftMPMFArg? y | return none
  let .lam yName yTy body2 yBi := g | return none

  let some (_m3, _inst3, _γ, _δ3, z, h) := getBind? body2 | return none
  if z.hasLooseBVar 0 then
    return none
  if !z.hasLooseBVar 1 then
    return none
  let some CVal ← getLiftMPMFArg? z | return none
  let .lam zName zTy body3 zBi := h | return none

  let CFn := Expr.lam xName xTy (CVal.lowerLooseBVars 1 1) xBi
  let restFn := Expr.lam xName xTy (Expr.lam yName yTy (Expr.lam zName zTy body3 zBi) yBi) xBi
  let pf ← mkAppM ``RState.do_liftM_comm_dep #[B, A, CFn, restFn]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some out ← mkRawPMFBindMapSwapProof? e then
    return some out
  if let some out ← mkRawPMFSwapProof? e then
    return some out
  if let some out ← mkPMFBindMapSwapProof? e then
    return some out
  if let some out ← mkPMFSwapProof? e then
    return some out
  if let some out ← mkSwapProof? e then
    return some out
  mkSwapDepProof? e

end PMFLiftOrder

/-- Simproc: order adjacent independent `PMF` draws and adjacent lifted `PMF` draws in `RState`
by the first continuation use of the bound variables. -/
simproc [simp] pmfLiftOrderBindComm
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFLiftOrder.mkRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Simproc: raw `PMF.bind` version of `pmfLiftOrderBindComm`. -/
simproc [simp] pmfBindOrderComm
  (PMF.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFLiftOrder.mkRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

open Lean Elab Tactic

/-- Explicit tactic for ordering lifted `PMF` draws in `RState` `do` notation. -/
elab "pmf_lift_order" : tactic => do
  evalTactic (← `(tactic| simp (failIfUnchanged := false)))
