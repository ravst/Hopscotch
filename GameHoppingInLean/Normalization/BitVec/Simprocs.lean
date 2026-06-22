import GameHoppingInLean.Normalization.BitVec.Lemmas
import GameHoppingInLean.Misc.SimprocHelpers

open Lean Meta

namespace PMFSimp

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

private def getBitVecWidth? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``BitVec, #[w]) => some w
  | _ => none

private def getUniformBitVecWidth? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``PMF.uniformOfFintype, #[ty, _, _]) => getBitVecWidth? ty
  | _ => none

private def getArrowType? : Expr → Option (Expr × Expr)
  | .forallE _ dom cod _ =>
      if cod.hasLooseBVar 0 then none else some (dom, cod)
  | _ => none

private def getUniformFunctionType? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``PMF.uniformOfFintype, #[ty, _, _]) => getArrowType? ty
  | _ => none

private def getBitVecAppendArgs? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``BitVec.append, args) =>
      match args.toList.reverse with
      | rhs :: lhs :: _ => some (lhs, rhs)
      | _ => none
  | (``HAppend.hAppend, args) =>
      match args.toList.reverse with
      | rhs :: lhs :: _ => some (lhs, rhs)
      | _ => none
  | _ => none

private partial def abstractBitVecAppendOccurrencesAux?
    (e : Expr) (depth : Nat) (saw : Bool) : MetaM (Option (Expr × Bool)) := do
  if let some (lhs, rhs) := getBitVecAppendArgs? e then
    if lhs == mkBVar (depth + 1) && rhs == mkBVar depth then
      return some (mkBVar depth, true)
  match e with
  | .bvar idx =>
      if idx == depth || idx == depth + 1 then
        return none
      else
        return some (e, saw)
  | .app f a =>
      let some (f', saw1) ← abstractBitVecAppendOccurrencesAux? f depth saw | return none
      let some (a', saw2) ← abstractBitVecAppendOccurrencesAux? a depth saw1 | return none
      return some (.app f' a', saw2)
  | .lam n ty body bi =>
      let some (ty', saw1) ← abstractBitVecAppendOccurrencesAux? ty depth saw | return none
      let some (body', saw2) ← abstractBitVecAppendOccurrencesAux? body (depth + 1) saw1
        | return none
      return some (.lam n ty' body' bi, saw2)
  | .forallE n ty body bi =>
      let some (ty', saw1) ← abstractBitVecAppendOccurrencesAux? ty depth saw | return none
      let some (body', saw2) ← abstractBitVecAppendOccurrencesAux? body (depth + 1) saw1
        | return none
      return some (.forallE n ty' body' bi, saw2)
  | .letE n ty val body nondep =>
      let some (ty', saw1) ← abstractBitVecAppendOccurrencesAux? ty depth saw | return none
      let some (val', saw2) ← abstractBitVecAppendOccurrencesAux? val depth saw1 | return none
      let some (body', saw3) ← abstractBitVecAppendOccurrencesAux? body (depth + 1) saw2
        | return none
      return some (.letE n ty' val' body' nondep, saw3)
  | .mdata md body =>
      let some (body', saw1) ← abstractBitVecAppendOccurrencesAux? body depth saw | return none
      return some (.mdata md body', saw1)
  | .proj s i body =>
      let some (body', saw1) ← abstractBitVecAppendOccurrencesAux? body depth saw | return none
      return some (.proj s i body', saw1)
  | _ => return some (e, saw)

private def abstractBitVecAppendOccurrences? (body : Expr) : MetaM (Option Expr) := do
  let some (body', true) ← abstractBitVecAppendOccurrencesAux? body 0 false
    | return none
  return some (body'.lowerLooseBVars 1 1)

private def mkBitVecAppendUniformRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  try
    let some (m, _instBind, _α, _β, x₁, rest₁) ← getBind? e | return none
    unless ← isPMF? m do
      return none
    let some a := getUniformBitVecWidth? x₁ | return none
    let .lam xName _xTy body₁ xBi := rest₁ | return none
    let some (m₂, _instBind₂, _α₂, _β₂, x₂, rest₂) ← getBind? body₁ | return none
    unless ← isPMF? m₂ do
      return none
    let some b := getUniformBitVecWidth? x₂ | return none
    let .lam _yName _yTy body₂ _yBi := rest₂ | return none
    let some body ← abstractBitVecAppendOccurrences? body₂ | return none
    let ab ← mkAppM ``Nat.add #[a, b]
    let bitVecAB ← mkAppM ``BitVec #[ab]
    let rest := Expr.lam xName bitVecAB body xBi
    let pf ← mkAppM ``PMF.bind_uniformOfFintype_bitVec_append_do #[rest]
    let pfTy ← inferType pf
    let some (_ty, lhs, rhs) := pfTy.eq? | return none
    unless (← isDefEq lhs e) do
      return none
    return some (rhs, pf)
  catch _ =>
    return none

private def getNatAddArgs? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Nat.add, #[a, b]) => some (a, b)
  | _ => none

private def getNatTwoMulArg? (e : Expr) : MetaM (Option Expr) := do
  match e.getAppFnArgs with
  | (``Nat.mul, #[two, k]) =>
      if ← isDefEq two (mkNatLit 2) then
        return some k
      else
        return none
  | _ => return none

private def getBitVecExtractLsbArgs? (e : Expr) : Option (Expr × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``BitVec.extractLsb', args) =>
      match args.toList.reverse with
      | x :: len :: start :: _ => some (start, len, x)
      | _ => none
  | _ => none

private def isSliceOf? (e : Expr) (z : Expr) (start len : Expr) : MetaM Bool := do
  let some (start', len', z') := getBitVecExtractLsbArgs? e | return false
  return (← isDefEq z' z) && (← isDefEq start' start) && (← isDefEq len' len)

private partial def abstractBitVecSliceOccurrencesAux?
    (a b : Expr) (e : Expr) (depth : Nat) (saw : Bool) : MetaM (Option (Expr × Bool)) := do
  let z := mkBVar depth
  if ← isSliceOf? e z b a then
    return some (mkBVar (depth + 1), true)
  if ← isSliceOf? e z (mkNatLit 0) b then
    return some (mkBVar depth, true)
  match e with
  | .bvar idx =>
      if idx == depth then
        return none
      else
        return some (e, saw)
  | .app f x =>
      let some (f', saw1) ← abstractBitVecSliceOccurrencesAux? a b f depth saw | return none
      let some (x', saw2) ← abstractBitVecSliceOccurrencesAux? a b x depth saw1 | return none
      return some (.app f' x', saw2)
  | .lam n ty body bi =>
      let some (ty', saw1) ← abstractBitVecSliceOccurrencesAux? a b ty depth saw | return none
      let some (body', saw2) ← abstractBitVecSliceOccurrencesAux? a b body (depth + 1) saw1
        | return none
      return some (.lam n ty' body' bi, saw2)
  | .forallE n ty body bi =>
      let some (ty', saw1) ← abstractBitVecSliceOccurrencesAux? a b ty depth saw | return none
      let some (body', saw2) ← abstractBitVecSliceOccurrencesAux? a b body (depth + 1) saw1
        | return none
      return some (.forallE n ty' body' bi, saw2)
  | .letE n ty val body nondep =>
      let some (ty', saw1) ← abstractBitVecSliceOccurrencesAux? a b ty depth saw | return none
      let some (val', saw2) ← abstractBitVecSliceOccurrencesAux? a b val depth saw1 | return none
      let some (body', saw3) ← abstractBitVecSliceOccurrencesAux? a b body (depth + 1) saw2
        | return none
      return some (.letE n ty' val' body' nondep, saw3)
  | .mdata md body =>
      let some (body', saw1) ← abstractBitVecSliceOccurrencesAux? a b body depth saw | return none
      return some (.mdata md body', saw1)
  | .proj s i body =>
      let some (body', saw1) ← abstractBitVecSliceOccurrencesAux? a b body depth saw | return none
      return some (.proj s i body', saw1)
  | _ => return some (e, saw)

private def abstractBitVecSliceOccurrences? (a b body : Expr) : MetaM (Option Expr) := do
  let some (body', true) ← abstractBitVecSliceOccurrencesAux? a b body 0 false
    | return none
  return some body'

private def mkBitVecSplitUniformRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  try
    let some (m, _instBind, _α, _β, x, rest₁) ← getBind? e | return none
    unless ← isPMF? m do
      return none
    let some width := getUniformBitVecWidth? x | return none
    let some (a, b) := getNatAddArgs? width | return none
    let .lam xName _xTy body xBi := rest₁ | return none
    let some body ← abstractBitVecSliceOccurrences? a b body | return none
    let bitVecA ← mkAppM ``BitVec #[a]
    let bitVecB ← mkAppM ``BitVec #[b]
    let rest := Expr.lam xName bitVecA (Expr.lam `x₂ bitVecB body xBi) xBi
    let pf ← mkAppM ``PMF.bind_uniformOfFintype_bitVec_extract_do #[rest]
    let pfTy ← inferType pf
    let some (_ty, lhs, rhs) := pfTy.eq? | return none
    unless (← isDefEq lhs e) do
      return none
    return some (rhs, pf)
  catch _ =>
    return none

private def mkBitVecTwoMulSplitUniformRewriteProof? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  try
    let some (m, _instBind, _α, _β, x, rest₁) ← getBind? e | return none
    unless ← isPMF? m do
      return none
    let some width := getUniformBitVecWidth? x | return none
    let some k ← getNatTwoMulArg? width | return none
    let .lam xName _xTy body xBi := rest₁ | return none
    let some body ← abstractBitVecSliceOccurrences? k k body | return none
    let bitVecK ← mkAppM ``BitVec #[k]
    let rest := Expr.lam xName bitVecK (Expr.lam `x₂ bitVecK body xBi) xBi
    let pf ← mkAppM ``PMF.bind_uniformOfFintype_bitVec_two_mul_extract_do #[rest]
    let pfTy ← inferType pf
    let some (_ty, lhs, rhs) := pfTy.eq? | return none
    unless (← isDefEq lhs e) do
      return none
    return some (rhs, pf)
  catch _ =>
    return none

end PMFSimp

/-- Simproc: combine two independent uniform `BitVec` draws when they are observed only
through their append. -/
simproc [GHSimpPMFBitVec] pmfBitVecAppendUniform
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkBitVecAppendUniformRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Raw `PMF.bind` version of `pmfBitVecAppendUniform`. -/
simproc [GHSimpPMFBitVec] pmfRawBitVecAppendUniform
  (PMF.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkBitVecAppendUniformRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Simproc: split a uniform `BitVec (a + b)` draw used only through its high and low
slices into two independent uniform `BitVec` draws. -/
simproc [GHSimpPMFBitVec] pmfBitVecSplitUniform
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkBitVecSplitUniformRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Raw `PMF.bind` version of `pmfBitVecSplitUniform`. -/
simproc [GHSimpPMFBitVec] pmfRawBitVecSplitUniform
  (PMF.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkBitVecSplitUniformRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Simproc: split a uniform `BitVec (2 * k)` draw used only through its two `k`-bit
slices into two independent uniform `BitVec k` draws. -/
simproc [GHSimpPMFBitVec] pmfBitVecTwoMulSplitUniform
  (Bind.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkBitVecTwoMulSplitUniformRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }

/-- Raw `PMF.bind` version of `pmfBitVecTwoMulSplitUniform`. -/
simproc [GHSimpPMFBitVec] pmfRawBitVecTwoMulSplitUniform
  (PMF.bind _ _)
  := fun e => do
    let some (rhs, pf) ← PMFSimp.mkBitVecTwoMulSplitUniformRewriteProof? e | return .continue
    return .visit { expr := rhs, proof? := some pf }
