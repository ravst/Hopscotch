import GameHoppingInLean.MonadRandomState

open Lean Meta

namespace PMFLiftOrder

private def getBind? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Bind.bind, #[m, instBind, α, β, x, f]) => some (m, instBind, α, β, x, f)
  | _ => none

private def getLiftMPMFArg? (e : Expr) : MetaM (Option Expr) := do
  match e.getAppFnArgs with
  | (``liftM, #[m, _n, _inst, _α, x]) =>
      if m.isConstOf ``PMF then
        return some x
      else if (← isDefEq m (mkConst ``PMF)) then
        return some x
      else
        return none
  | _ => return none

private def mkSwapProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_m, _inst, _α, _γ, x, f) := getBind? e | return none
  let some A ← getLiftMPMFArg? x | return none
  let .lam xName xTy body xBi := f | return none
  let some (_m2, _inst2, _β, _γ2, y, g) := getBind? body | return none
  if y.hasLooseBVar 0 then
    return none
  let some B ← getLiftMPMFArg? y | return none
  let .lam yName yTy body2 yBi := g | return none
  -- Reorder only when a strict decrease is detected, avoiding commutativity loops.
  -- Prefer draws that mention surrounding binders (via loose bound vars), then use a
  -- stable structural order as a fallback.
  let shouldSwap :=
    if B.hasLooseBVars && !A.hasLooseBVars then
      true
    else if !B.hasLooseBVars && A.hasLooseBVars then
      false
    else
      Expr.lt B A
  if !shouldSwap then
    return none

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
  let some out ← mkSwapProof? e | mkSwapDepProof? e
  return some out

end PMFLiftOrder

/-- Simproc: order adjacent independent lifted `PMF` draws in `RState` by a strict term decrease. -/
simproc [simp] pmfLiftOrderBindComm
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFLiftOrder.mkRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

open Lean Elab Tactic

/-- Explicit tactic for ordering lifted `PMF` draws in `RState` `do` notation. -/
elab "pmf_lift_order" : tactic => do
  evalTactic (← `(tactic| simp (failIfUnchanged := false)))
