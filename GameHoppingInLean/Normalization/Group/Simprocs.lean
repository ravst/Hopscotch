import GameHoppingInLean.Normalization.Group.Lemmas

open Lean Meta

namespace GroupSampleSimp

private def getBind? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Bind.bind, #[m, instBind, α, β, x, f]) => some (m, instBind, α, β, x, f)
  | _ => none

private def getSampleExponentArg? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``sampleExponent, #[G, _, _]) => some G
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

private def getLiftMSampleExponentArg? (e : Expr) : MetaM (Option Expr) := do
  let some x ← getLiftMPMFArg? e | return none
  return getSampleExponentArg? x

private def getPowArgs? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``HPow.hPow, args) =>
      match args.toList.reverse with
      | exp :: base :: _ => some (base, exp)
      | _ => none
  | (``Pow.pow, args) =>
      match args.toList.reverse with
      | exp :: base :: _ => some (base, exp)
      | _ => none
  | _ => none

private def getMulArgs? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``HMul.hMul, args) =>
      match args.toList.reverse with
      | rhs :: lhs :: _ => some (lhs, rhs)
      | _ => none
  | (``Mul.mul, args) =>
      match args.toList.reverse with
      | rhs :: lhs :: _ => some (lhs, rhs)
      | _ => none
  | _ => none

private partial def abstractPowOccurrencesAux?
    (e : Expr) (depth : Nat) (base? : Option Expr) (saw : Bool) :
    MetaM (Option (Expr × Option Expr × Bool)) := do
  if let some (base, exp) := getPowArgs? e then
    if exp == mkBVar depth then
      match base? with
      | none => return some (mkBVar depth, some base, true)
      | some base0 =>
          if ← isDefEq base base0 then
            return some (mkBVar depth, some base0, true)
          else
            return none
  match e with
  | .bvar idx =>
      if idx == depth then
        return none
      else
        return some (e, base?, saw)
  | .app f a =>
      let some (f', base1, saw1) ← abstractPowOccurrencesAux? f depth base? saw | return none
      let some (a', base2, saw2) ← abstractPowOccurrencesAux? a depth base1 saw1 | return none
      return some (.app f' a', base2, saw2)
  | .lam n ty body bi =>
      let some (ty', base1, saw1) ← abstractPowOccurrencesAux? ty depth base? saw | return none
      let some (body', base2, saw2) ← abstractPowOccurrencesAux? body (depth + 1) base1 saw1
        | return none
      return some (.lam n ty' body' bi, base2, saw2)
  | .forallE n ty body bi =>
      let some (ty', base1, saw1) ← abstractPowOccurrencesAux? ty depth base? saw | return none
      let some (body', base2, saw2) ← abstractPowOccurrencesAux? body (depth + 1) base1 saw1
        | return none
      return some (.forallE n ty' body' bi, base2, saw2)
  | .letE n ty val body nondep =>
      let some (ty', base1, saw1) ← abstractPowOccurrencesAux? ty depth base? saw | return none
      let some (val', base2, saw2) ← abstractPowOccurrencesAux? val depth base1 saw1 | return none
      let some (body', base3, saw3) ← abstractPowOccurrencesAux? body (depth + 1) base2 saw2
        | return none
      return some (.letE n ty' val' body' nondep, base3, saw3)
  | .mdata md body =>
      let some (body', base1, saw1) ← abstractPowOccurrencesAux? body depth base? saw
        | return none
      return some (.mdata md body', base1, saw1)
  | .proj s i body =>
      let some (body', base1, saw1) ← abstractPowOccurrencesAux? body depth base? saw
        | return none
      return some (.proj s i body', base1, saw1)
  | _ => return some (e, base?, saw)

private def abstractPowOccurrences? (body : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (body', some base, true) ← abstractPowOccurrencesAux? body 0 none false
    | return none
  return some (body', base)

private partial def abstractMulLeftOccurrencesAux?
    (e : Expr) (depth : Nat) (lhs? : Option Expr) (saw : Bool) :
    MetaM (Option (Expr × Option Expr × Bool)) := do
  if let some (lhs, rhs) := getMulArgs? e then
    if rhs == mkBVar depth then
      match lhs? with
      | none => return some (mkBVar depth, some lhs, true)
      | some lhs0 =>
          if ← isDefEq lhs lhs0 then
            return some (mkBVar depth, some lhs0, true)
          else
            return none
  match e with
  | .bvar idx =>
      if idx == depth then
        return none
      else
        return some (e, lhs?, saw)
  | .app f a =>
      let some (f', lhs1, saw1) ← abstractMulLeftOccurrencesAux? f depth lhs? saw | return none
      let some (a', lhs2, saw2) ← abstractMulLeftOccurrencesAux? a depth lhs1 saw1 | return none
      return some (.app f' a', lhs2, saw2)
  | .lam n ty body bi =>
      let some (ty', lhs1, saw1) ← abstractMulLeftOccurrencesAux? ty depth lhs? saw | return none
      let some (body', lhs2, saw2) ← abstractMulLeftOccurrencesAux? body (depth + 1) lhs1 saw1
        | return none
      return some (.lam n ty' body' bi, lhs2, saw2)
  | .forallE n ty body bi =>
      let some (ty', lhs1, saw1) ← abstractMulLeftOccurrencesAux? ty depth lhs? saw | return none
      let some (body', lhs2, saw2) ← abstractMulLeftOccurrencesAux? body (depth + 1) lhs1 saw1
        | return none
      return some (.forallE n ty' body' bi, lhs2, saw2)
  | .letE n ty val body nondep =>
      let some (ty', lhs1, saw1) ← abstractMulLeftOccurrencesAux? ty depth lhs? saw | return none
      let some (val', lhs2, saw2) ← abstractMulLeftOccurrencesAux? val depth lhs1 saw1 | return none
      let some (body', lhs3, saw3) ← abstractMulLeftOccurrencesAux? body (depth + 1) lhs2 saw2
        | return none
      return some (.letE n ty' val' body' nondep, lhs3, saw3)
  | .mdata md body =>
      let some (body', lhs1, saw1) ← abstractMulLeftOccurrencesAux? body depth lhs? saw
        | return none
      return some (.mdata md body', lhs1, saw1)
  | .proj s i body =>
      let some (body', lhs1, saw1) ← abstractMulLeftOccurrencesAux? body depth lhs? saw
        | return none
      return some (.proj s i body', lhs1, saw1)
  | _ => return some (e, lhs?, saw)

private def abstractMulLeftOccurrences? (body : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (body', some lhs, true) ← abstractMulLeftOccurrencesAux? body 0 none false
    | return none
  return some (body', lhs)

private def findGeneratorHyp? (g : Expr) : MetaM (Option Expr) := do
  let target ← mkAppM ``IsGenerator #[g]
  for ldecl in ← getLCtx do
    unless ldecl.isImplementationDetail do
      if (← isDefEq ldecl.type target) then
        return some ldecl.toExpr
  return none

private def mkPMFRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_m, _inst, _α, _β, x, f) := getBind? e | return none
  let some _G := getSampleExponentArg? x | return none
  let .lam xName _xTy body xBi := f | return none
  let some (body', g) ← abstractPowOccurrences? body | return none
  let some hgen ← findGeneratorHyp? g | return none
  let gTy ← inferType g
  let rest := Expr.lam xName gTy body' xBi
  let pf ← mkAppM ``PMF.bind_sampleExponent_pow_eq_bind_uniformOfFintype #[hgen, rest]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkRStateRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_m, _inst, _α, _β, x, f) := getBind? e | return none
  let some _G ← getLiftMSampleExponentArg? x | return none
  let .lam xName _xTy body xBi := f | return none
  let some (body', g) ← abstractPowOccurrences? body | return none
  let some hgen ← findGeneratorHyp? g | return none
  let gTy ← inferType g
  let rest := Expr.lam xName gTy body' xBi
  let pf ← mkAppM ``RState.do_liftM_sampleExponent_pow_eq_do_liftM_uniformOfFintype
    #[hgen, rest]
  let pfTy ← inferType pf
  let some (_ty, lhs, rhs) := pfTy.eq? | return none
  unless (← isDefEq lhs e) do
    return none
  return some (rhs, pf)

private def mkPMFMulLeftRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_m, _inst, _α, _β, x, f) := getBind? e | return none
  match x.getAppFnArgs with
  | (``PMF.uniformOfFintype, #[G, _, _]) =>
      let .lam xName _xTy body xBi := f | return none
      let some (body', m) ← abstractMulLeftOccurrences? body | return none
      let mTy ← inferType m
      let rest := Expr.lam xName mTy body' xBi
      let pf ← mkAppM ``PMF.bind_uniformOfFintype_mul_left_eq_bind_uniformOfFintype #[G, m, rest]
      let pfTy ← inferType pf
      let some (_ty, lhs, rhs) := pfTy.eq? | return none
      unless (← isDefEq lhs e) do
        return none
      return some (rhs, pf)
  | _ => return none

private def mkRStateMulLeftRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_m, _inst, _α, _β, x, f) := getBind? e | return none
  match (← getLiftMPMFArg? x) with
  | some y =>
      match y.getAppFnArgs with
      | (``PMF.uniformOfFintype, #[G, _, _]) =>
          let .lam xName _xTy body xBi := f | return none
          let some (body', m) ← abstractMulLeftOccurrences? body | return none
          let mTy ← inferType m
          let rest := Expr.lam xName mTy body' xBi
          let pf ← mkAppM ``RState.do_liftM_uniformOfFintype_mul_left_eq_do_liftM_uniformOfFintype
            #[G, m, rest]
          let pfTy ← inferType pf
          let some (_ty, lhs, rhs) := pfTy.eq? | return none
          unless (← isDefEq lhs e) do
            return none
          return some (rhs, pf)
      | _ => return none
  | none => return none

end GroupSampleSimp

/-- Simproc: replace generator exponent samples in `PMF` `do` blocks by uniform samples from `G`. -/
simproc [GH_group_nom] sampleExponentPowToUniformPMF
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← GroupSampleSimp.mkPMFRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Simproc: replace lifted generator exponent samples in `RState` `do` blocks by lifted
uniform samples from `G`. -/
simproc [GH_group_nom] sampleExponentPowToUniformRState
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← GroupSampleSimp.mkRStateRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Simproc: replace left-multiplied uniform group draws in `PMF` `do` blocks by uniform draws. -/
simproc [GH_group_nom] uniformMulLeftToUniformPMF
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← GroupSampleSimp.mkPMFMulLeftRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Simproc: replace left-multiplied lifted uniform group draws in `RState` `do` blocks by
lifted uniform draws. -/
simproc [GH_group_nom] uniformMulLeftToUniformRState
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← GroupSampleSimp.mkRStateMulLeftRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }
