import GameHoppingInLean.Tactic.Normalization.PMF.Lemmas
import GameHoppingInLean.Tactic.Normalization.RState.Lemmas
import GameHoppingInLean.Tactic.SimprocHelpers

open Lean Meta

namespace PMFSimp

theorem rstateDoLiftMComm {σ α β γ}
    (A : PMF α) (B : PMF β) (rest : α → β → RState σ γ) :
    (do
      let x ← (liftM A : RState σ α)
      let y ← (liftM B : RState σ β)
      rest x y) =
    (do
      let y ← (liftM B : RState σ β)
      let x ← (liftM A : RState σ α)
      rest x y) := by
  funext s
  change StateT.run ((liftM A : RState σ α) >>= fun x => do
      let y ← (liftM B : RState σ β)
      rest x y) s =
    StateT.run ((liftM B : RState σ β) >>= fun y => do
      let x ← (liftM A : RState σ α)
      rest x y) s
  rw [StateT.run_bind, StateT.run_bind]
  simp [StateT.run_bind]
  simpa using (PMF.bind_comm (p := A) (q := B) (f := fun a b => StateT.run (rest a b) s))

theorem rstateDoLiftMCommDep {σ α β γ δ}
    (B : PMF β) (A : PMF α) (C : β → PMF γ) (rest : β → α → γ → RState σ δ) :
    (do
      let b ← (liftM B : RState σ β)
      let a ← (liftM A : RState σ α)
      let c ← (liftM (C b) : RState σ γ)
      rest b a c) =
    (do
      let b ← (liftM B : RState σ β)
      let c ← (liftM (C b) : RState σ γ)
      let a ← (liftM A : RState σ α)
      rest b a c) := by
  refine congrArg (fun f => Bind.bind (liftM B : RState σ β) f) ?_
  funext b
  simpa using
    (rstateDoLiftMComm (A := A) (B := C b) (rest := fun a c => rest b a c))

private def getBind? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Expr × Expr)) := do
  match e.getAppFnArgs with
  | (``Bind.bind, #[m, instBind, α, β, x, f]) => return some (m, instBind, α, β, x, f)
  | _ => return none

private def getRawPMFBind? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``PMF.bind, #[α, β, x, f]) => some (α, β, x, f)
  | _ => none

private def isPMF? (m : Expr) : MetaM Bool := do
  let pmfConst ← mkConstWithFreshMVarLevels ``PMF
  if m.isConstOf ``PMF then
    return true
  else
    isDefEq m pmfConst

private def mkBindConstRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (m, _instBind, _α, _β, x, rest) ← getBind? e | return none
  unless ← isPMF? m do
    return none
  let .lam _xName _xTy body _xBi := rest | return none
  let body ← SimprocHelpers.reduceCtorProjsRec body
  if SimprocHelpers.hasLooseBVarExactlyInValue body 0 then
    return none
  let restConst := body.lowerLooseBVars 0 1
  let pf ← mkAppOptM ``PMF.bind_const_do
    #[none, none, some x, some restConst]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkRawPMFBindConstRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_α, _β, x, rest) := getRawPMFBind? e | return none
  let .lam _xName _xTy body _xBi := rest | return none
  let body ← SimprocHelpers.reduceCtorProjsRec body
  if SimprocHelpers.hasLooseBVarExactlyInValue body 0 then
    return none
  let restConst := body.lowerLooseBVars 0 1
  let pf ← mkAppOptM ``PMF.bind_const_raw
    #[none, none, some x, some restConst]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkIteBindRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (m, _instBind, _α, _β, x, rest) ← getBind? e | return none
  unless ← isPMF? m do
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

private def getArrowType? : Expr → Option (Expr × Expr)
  | .forallE _ dom cod _ =>
      if cod.hasLooseBVar 0 then none else some (dom, cod)
  | _ => none

private def getUniformFunctionType? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``PMF.uniformOfFintype, #[ty, _, _]) => getArrowType? ty
  | _ => none

private partial def abstractFunctionEvalOccurrencesAux?
    (e : Expr) (depth : Nat) (arg? : Option Expr) (saw : Bool) :
    MetaM (Option (Expr × Option Expr × Bool)) := do
  match e with
  | .bvar idx =>
      if idx == depth then
        return none
      else
        return some (e, arg?, saw)
  | .app fn arg =>
      if fn == mkBVar depth then
        if arg.hasLooseBVar depth then
          return none
        let arg? ←
          match arg? with
          | none => pure (some arg)
          | some old =>
              unless old == arg do
                return none
              pure (some old)
        return some (mkBVar depth, arg?, true)
      else
        let some (fn', arg?, saw) ← abstractFunctionEvalOccurrencesAux? fn depth arg? saw
          | return none
        let some (arg', arg?, saw) ← abstractFunctionEvalOccurrencesAux? arg depth arg? saw
          | return none
        return some (.app fn' arg', arg?, saw)
  | .lam n ty body bi =>
      let some (ty', arg?, saw) ← abstractFunctionEvalOccurrencesAux? ty depth arg? saw
        | return none
      let some (body', arg?, saw) ← abstractFunctionEvalOccurrencesAux? body (depth + 1) arg? saw
        | return none
      return some (.lam n ty' body' bi, arg?, saw)
  | .forallE n ty body bi =>
      let some (ty', arg?, saw) ← abstractFunctionEvalOccurrencesAux? ty depth arg? saw
        | return none
      let some (body', arg?, saw) ← abstractFunctionEvalOccurrencesAux? body (depth + 1) arg? saw
        | return none
      return some (.forallE n ty' body' bi, arg?, saw)
  | .letE n ty val body nondep =>
      let some (ty', arg?, saw) ← abstractFunctionEvalOccurrencesAux? ty depth arg? saw
        | return none
      let some (val', arg?, saw) ← abstractFunctionEvalOccurrencesAux? val depth arg? saw
        | return none
      let some (body', arg?, saw) ← abstractFunctionEvalOccurrencesAux? body (depth + 1) arg? saw
        | return none
      return some (.letE n ty' val' body' nondep, arg?, saw)
  | .mdata md body =>
      let some (body', arg?, saw) ← abstractFunctionEvalOccurrencesAux? body depth arg? saw
        | return none
      return some (.mdata md body', arg?, saw)
  | .proj s i body =>
      let some (body', arg?, saw) ← abstractFunctionEvalOccurrencesAux? body depth arg? saw
        | return none
      return some (.proj s i body', arg?, saw)
  | _ => return some (e, arg?, saw)

private def abstractFunctionEvalOccurrences? (body : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (body', some arg, true) ← abstractFunctionEvalOccurrencesAux? body 0 none false
    | return none
  return some (body', arg)

private def mkUniformFunctionEvalRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  try
    let some (m, _instBind, _α, _β, x, rest₁) ← getBind? e | return none
    unless ← isPMF? m do
      return none
    let some (_X, Y) := getUniformFunctionType? x | return none
    let .lam fName _fTy body fBi := rest₁ | return none
    let some (body', arg) ← abstractFunctionEvalOccurrences? body | return none
    let rest := Expr.lam fName Y body' fBi
    let pf ← mkAppM ``PMF.bind_uniformOfFintype_eval_do #[arg, rest]
    let pfTy ← inferType pf
    let some (_ty, lhs, rhs) := pfTy.eq? | return none
    unless (← isDefEq lhs e) do
      return none
    return some (rhs, pf)
  catch _ =>
    return none

end PMFSimp

/-- Simproc: remove a `PMF` bind when the continuation ignores the sampled value. -/
simproc [sPMF] pmfBindConst
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkBindConstRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Raw `PMF.bind` version of `pmfBindConst`, for goals after monad notation has unfolded. -/
simproc [sPMF] pmfRawBindConst
  (PMF.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkRawPMFBindConstRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Simproc: pull an `if` out of a `PMF` bind when using the game-hopping PMF simp set. -/
simproc [sPMF] pmfIteBind
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkIteBindRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }


/-- Simproc: replace a uniform function draw used only at one fixed input by a uniform draw of
the corresponding output value. -/
simproc [sPMF] pmfUniformFunctionEval
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkUniformFunctionEvalRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

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

private def getAnyPMFBind? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  if let some out := getRawPMFBind? e then
    return some out
  let some (m, _instBind, α, β, x, f) := getBind? e | return none
  unless (← isPMFExpr m) do
    return none
  return some (α, β, x, f)

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

private def mkRawPMFSwapProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_α, _γ, A, f) := getRawPMFBind? e | return none
  let .lam xName xTy body xBi := f | return none
  let some (_β, _γ2, B, g) := getRawPMFBind? body | return none
  if SimprocHelpers.hasLooseBVarExactly B 0 then
    return none
  let .lam yName yTy body2 yBi := g | return none
  unless SimprocHelpers.shouldSwapIndependentDraws A B body2 do
    return none
  let restFn := Expr.lam xName xTy (Expr.lam yName yTy body2 yBi) xBi
  let pf ← mkAppM ``PMF.bind_bind_comm #[A, B, restFn]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← withTransparency .all <| isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkRawPMFSwapMiddleProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_α, _δ, A, f) := getRawPMFBind? e | return none
  let .lam xName xTy body xBi := f | return none
  let some (_β, _δ2, B, g) := getRawPMFBind? body | return none
  if SimprocHelpers.hasLooseBVarExactly B 0 then
    return none
  let .lam yName yTy body2 yBi := g | return none
  let some (_γ, _δ3, CVal, h) := getRawPMFBind? body2 | return none
  if SimprocHelpers.hasLooseBVarExactly CVal 0 then
    return none
  let .lam zName zTy body3 zBi := h | return none
  unless SimprocHelpers.firstBinderUse? body3 == some true do
    return none
  let CFn := Expr.lam xName xTy (CVal.lowerLooseBVars 1 1) xBi
  let restFn := Expr.lam xName xTy
    (Expr.lam yName yTy (Expr.lam zName zTy body3 zBi) yBi) xBi
  let pf ← mkAppM ``PMF.bind_bind_bind_comm_middle #[A, B, CFn, restFn]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkPMFSwapMiddleProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_α, _δ, A, f) ← getAnyPMFBind? e | return none
  let .lam xName xTy body xBi := f | return none
  let some (_β, _δ2, B, g) ← getAnyPMFBind? body | return none
  if SimprocHelpers.hasLooseBVarExactly B 0 then
    return none
  let .lam yName yTy body2 yBi := g | return none
  let some (_γ, _δ3, CVal, h) ← getAnyPMFBind? body2 | return none
  if SimprocHelpers.hasLooseBVarExactly CVal 0 then
    return none
  let .lam zName zTy body3 zBi := h | return none
  unless SimprocHelpers.firstBinderUse? body3 == some true do
    return none
  let CFn := Expr.lam xName xTy (CVal.lowerLooseBVars 1 1) xBi
  let restFn := Expr.lam xName xTy
    (Expr.lam yName yTy (Expr.lam zName zTy body3 zBi) yBi) xBi
  let pf ← mkAppM ``PMF.do_bind_comm_middle #[A, B, CFn, restFn]
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
  if SimprocHelpers.hasLooseBVarExactly B 0 then
    return none
  let .lam yName yTy body2 yBi := g | return none
  unless SimprocHelpers.shouldSwapIndependentDraws A B body2 do
    return none
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
  if SimprocHelpers.hasLooseBVarExactly B 0 then
    return none
  let .lam yName yTy body2 yBi := g | return none
  unless SimprocHelpers.shouldSwapIndependentDraws A B body2 do
    return none
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
  if SimprocHelpers.hasLooseBVarExactly B 0 then
    return none
  let .lam yName yTy body2 yBi := g | return none
  unless SimprocHelpers.shouldSwapIndependentDraws A B body2 do
    return none
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
  if SimprocHelpers.hasLooseBVarExactly y 0 then
    return none
  let some B ← getLiftMPMFArg? y | return none
  let .lam yName yTy body2 yBi := g | return none
  unless SimprocHelpers.shouldSwapIndependentDraws A B body2 do
    return none
  let restFn := Expr.lam xName xTy (Expr.lam yName yTy body2 yBi) xBi
  let pf ← mkAppM ``PMFSimp.rstateDoLiftMComm #[A, B, restFn]
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
  let some CVal ← getLiftMPMFArg? z | return none
  let .lam zName zTy body3 zBi := h | return none
  let CFn := Expr.lam xName xTy (CVal.lowerLooseBVars 1 1) xBi
  let restFn := Expr.lam xName xTy (Expr.lam yName yTy (Expr.lam zName zTy body3 zBi) yBi) xBi
  let pf ← mkAppM ``PMFSimp.rstateDoLiftMCommDep #[B, A, CFn, restFn]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some out ← mkRawPMFSwapMiddleProof? e then
    return some out
  if let some out ← mkPMFSwapMiddleProof? e then
    return some out
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
simproc [simp, sPMF] pmfLiftOrderBindComm
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFLiftOrder.mkRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Simproc: raw `PMF.bind` version of `pmfLiftOrderBindComm`. -/
simproc [simp, sPMF] pmfBindOrderComm
  (PMF.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFLiftOrder.mkRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

open Lean Elab Tactic

/-- Explicit tactic for ordering lifted `PMF` draws in `RState` `do` notation. -/
elab "pmf_lift_order" : tactic => do
  evalTactic (← `(tactic| simp (failIfUnchanged := false)))
