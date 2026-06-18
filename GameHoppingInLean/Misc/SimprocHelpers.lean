import Lean

open Lean Meta

namespace SimprocHelpers

partial def firstBinderUse? (e : Expr) (depth : Nat := 0) : Option Bool :=
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

partial def hasLooseBVarAtLeast (e : Expr) (minIdx : Nat) : Bool :=
  match e with
  | .bvar idx => minIdx ≤ idx
  | .app f a => hasLooseBVarAtLeast f minIdx || hasLooseBVarAtLeast a minIdx
  | .lam _ ty body _ =>
      hasLooseBVarAtLeast ty minIdx || hasLooseBVarAtLeast body (minIdx + 1)
  | .forallE _ ty body _ =>
      hasLooseBVarAtLeast ty minIdx || hasLooseBVarAtLeast body (minIdx + 1)
  | .letE _ ty value body _ =>
      hasLooseBVarAtLeast ty minIdx ||
        hasLooseBVarAtLeast value minIdx ||
        hasLooseBVarAtLeast body (minIdx + 1)
  | .mdata _ body => hasLooseBVarAtLeast body minIdx
  | .proj _ _ body => hasLooseBVarAtLeast body minIdx
  | _ => false

partial def hasLooseBVarExactly (e : Expr) (idx : Nat) : Bool :=
  match e with
  | .bvar i => i == idx
  | .app f a => hasLooseBVarExactly f idx || hasLooseBVarExactly a idx
  | .lam _ ty body _ =>
      hasLooseBVarExactly ty idx || hasLooseBVarExactly body (idx + 1)
  | .forallE _ ty body _ =>
      hasLooseBVarExactly ty idx || hasLooseBVarExactly body (idx + 1)
  | .letE _ ty value body _ =>
      hasLooseBVarExactly ty idx ||
        hasLooseBVarExactly value idx ||
        hasLooseBVarExactly body (idx + 1)
  | .mdata _ body => hasLooseBVarExactly body idx
  | .proj _ _ body => hasLooseBVarExactly body idx
  | _ => false

partial def hasLooseBVarExactlyInValue (e : Expr) (idx : Nat) : Bool :=
  match e with
  | .bvar i => i == idx
  | .app f a => hasLooseBVarExactlyInValue f idx || hasLooseBVarExactlyInValue a idx
  | .lam _ _ body _ => hasLooseBVarExactlyInValue body (idx + 1)
  | .forallE _ _ body _ => hasLooseBVarExactlyInValue body (idx + 1)
  | .letE _ _ value body _ =>
      hasLooseBVarExactlyInValue value idx ||
        hasLooseBVarExactlyInValue body (idx + 1)
  | .mdata _ body => hasLooseBVarExactlyInValue body idx
  | .proj _ _ body => hasLooseBVarExactlyInValue body idx
  | _ => false

def shouldSwapIndependentDraws (A B body : Expr) : Bool :=
  let AUsesOuter := hasLooseBVarAtLeast A 1 || A.hasFVar
  let BUsesOuter := hasLooseBVarAtLeast B 1 || B.hasFVar
  if !AUsesOuter && BUsesOuter then
    true
  else if AUsesOuter && !BUsesOuter then
    false
  else
    firstBinderUse? body == some true

private def reduceProdProj? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``Prod.fst, args) =>
      match args.back? with
      | some major =>
          match major.getAppFnArgs with
          | (``Prod.mk, mkArgs) =>
              match mkArgs.toList.reverse with
              | _snd :: fst :: _ => some fst
              | _ => none
          | _ => none
      | _ => none
  | (``Prod.snd, args) =>
      match args.back? with
      | some major =>
          match major.getAppFnArgs with
          | (``Prod.mk, mkArgs) =>
              match mkArgs.toList.reverse with
              | snd :: _ => some snd
              | _ => none
          | _ => none
      | _ => none
  | _ => none

partial def reduceCtorProjsRec (e : Expr) : MetaM Expr := do
  match e with
  | .app f a =>
      let e' := .app (← reduceCtorProjsRec f) (← reduceCtorProjsRec a)
      match reduceProdProj? e' with
      | some e'' => reduceCtorProjsRec e''
      | none => return e'
  | .lam n ty body bi => return .lam n (← reduceCtorProjsRec ty) (← reduceCtorProjsRec body) bi
  | .forallE n ty body bi =>
      return .forallE n (← reduceCtorProjsRec ty) (← reduceCtorProjsRec body) bi
  | .letE n ty value body nondep =>
      return .letE n (← reduceCtorProjsRec ty) (← reduceCtorProjsRec value)
        (← reduceCtorProjsRec body) nondep
  | .mdata md body => return .mdata md (← reduceCtorProjsRec body)
  | .proj s i body =>
      let body ← reduceCtorProjsRec body
      match ← projectCore? body i with
      | some e' => reduceCtorProjsRec e'
      | none => return .proj s i body
  | _ => return e

end SimprocHelpers
