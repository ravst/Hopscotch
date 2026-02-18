/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import GameHoppingInLean.VCVio2.ToMathlib.Control.FreeMonad
import GameHoppingInLean.VCVio2.ToMathlib.Control.WriterT
import Mathlib.Control.Lawful
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleSpec

/-!
# Computations with Oracle Access

A value `oa : OracleComp spec α` represents a computation with return type `α`,
with access to any of the oracles specified by `spec : OracleSpec`.
Returning a value `x` corresponds to the computation `pure' α x`.
The computation `queryBind' i t α ou` represents querying the oracle corresponding to index `i`
on input `t`, getting a result `u : spec.range i`, and then running `ou u`.
These operations induce a `Monad` instance on `OracleComp spec`.

`pure' α a` gives a monadic `pure` operation, while a more general `>>=` operator
is derived by induction on the first computation (see `OracleComp.bind`).
This importantly allows us to define a `LawfulMonad` instance on `OracleComp spec`,
which isn't possible if a general bind operator is included in the main syntax.

We also define simple operations like `coin : OracleComp coinSpec Bool` for flipping a fair coin,
and `$[0..n] : ProbComp (Fin (n + 1))` for selecting from an inclusive range.

Note that the monadic structure on `OracleComp` exists only for a fixed `OracleSpec`,
so it isn't possible to combine computations where one has a superset of oracles of the other.
We later introduce a set of type coercions that mitigate this for most common cases,
such as calling a computation with `spec` as part of a computation with `spec ++ spec'`.
-/

universe u v w z

namespace OracleSpec

/-- An `OracleQuery` to one of the oracles in `spec`, bundling an index and the input to
use for querying that oracle, implemented as a dependent pair.
Implemented as a functor with the oracle output type as the constructor result. -/
inductive OracleQuery {ι : Type u} (spec : OracleSpec.{u,v} ι) : Type v → Type (max u v)
  | query (i : ι) (t : spec.domain i) : OracleQuery spec (spec.range i)

namespace OracleQuery

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type v}

def defaultOutput [∀ i, Inhabited (spec.range i)] : (q : OracleQuery spec α) → α
  | query i t => default

def index : (q : OracleQuery spec α) → ι | query i t => i

@[simp] lemma index_query (i : ι) (t : spec.domain i) : (query i t).index = i := rfl

def input : (q : OracleQuery spec α) → spec.domain q.index | query i t => t

@[simp] lemma input_query (i : ι) (t : spec.domain i) : (query i t).input = t := rfl

@[simp]
lemma range_index : (q : OracleQuery spec α) → spec.range q.index = α | query i t => rfl

lemma eq_query_index_input : (q : OracleQuery spec α) →
    q = q.range_index ▸ OracleQuery.query q.index q.input | query i t => rfl

def rangeDecidableEq [spec.DecidableEq] : OracleQuery spec α → DecidableEq α
  | query i t => inferInstance

def rangeFintype [spec.FiniteRange] : OracleQuery spec α → Fintype α
  | query i t => inferInstance

def rangeInhabited [spec.FiniteRange] : OracleQuery spec α → Inhabited α
  | query i t => inferInstance

instance isEmpty : IsEmpty (OracleQuery []ₒ α) where false | query i t => i.elim

instance [hι : DecidableEq ι] [hd : ∀ i, DecidableEq (spec.domain i)] {α : Type u} :
    DecidableEq (OracleQuery spec α)
  | query i t => λ q ↦ match hι i q.index with
    | isTrue h => by
        have : q = query i (h ▸ q.input) := by
          refine q.eq_query_index_input.trans (eq_of_heq (eqRec_heq_iff_heq.2 ?_))
          congr
          · exact h.symm
          · exact HEq.symm (eqRec_heq (Eq.symm h) q.input)
        rw [this, query.injEq]
        exact hd i t _
    | isFalse h => isFalse λ h' ↦ h (congr_arg index h')

end OracleQuery

-- Put `query` in the main `OracleSpec` namespace
export OracleQuery (query)

end OracleSpec

open OracleSpec

/-- `OracleComp spec α` represents computations with oracle access to oracles in `spec`,
where the final return value has type `α`.
The basic computation is just an `OracleQuery`, augmented with `pure` and `bind` by `FreeMonad`,
with no separate failure branch.

In practive computations in `OracleComp spec α` have have one of two forms:
* `return x` to succeed with some `x : α` as the result.
* `do u ← query i t; oa u` where `oa` is a continutation to run with the query result
See `OracleComp.inductionOn` for an explicit induction principle. -/
abbrev OracleComp {ι : Type u} (spec : OracleSpec.{u,v} ι) :
    Type v → Type (max u (v + 1)) :=
  FreeMonad (OracleQuery.{u,v} spec)

/-- Simplified notation for computations with no oracles besides random inputs. -/
abbrev ProbComp := OracleComp unifSpec

namespace OracleComp

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type v}

instance : LawfulMonad (OracleComp spec) :=
  inferInstanceAs (LawfulMonad (FreeMonad (OracleQuery spec)))

section lift

/-- Lift a query to `OracleComp`. -/
def lift (q : OracleQuery spec α) : OracleComp spec α :=
  FreeMonad.lift q

/-- Automatically coerce an `OracleQuery spec α` to an `OracleComp spec α`. -/
instance : MonadLift (OracleQuery spec) (OracleComp spec) where
  monadLift := lift

/-- Lift a function on oracle queries to one on oracle computations. -/
instance : MonadFunctor (OracleQuery spec) (OracleComp spec) where
  monadMap f := (FreeMonad.instMonadFunctor).monadMap f

protected lemma liftM_def (q : OracleQuery spec α) :
    (q : OracleComp spec α) = FreeMonad.lift q := rfl
alias lift_query_def := OracleComp.liftM_def

--@[simp] -- Usually this is a better simp pathway but occasionally bad. Simp specific cases below
lemma liftM_query_eq_liftM_liftM {m : Type v → Type z} [MonadLift (OracleComp spec) m] {α : Type v}
    (q : OracleQuery spec α) : (liftM q : m α) = liftM (liftM q : OracleComp spec α) := rfl

@[simp]
lemma liftM_query_stateT {σ : Type v} {α : Type v} (q : OracleQuery spec α) :
  (liftM q : StateT σ (OracleComp spec) α) = liftM (liftM q : OracleComp spec α) := rfl

@[simp]
lemma liftM_query_writerT {ω : Type v} [Monoid ω] {α : Type v} (q : OracleQuery spec α) :
  (liftM q : WriterT ω (OracleComp spec) α) = liftM (liftM q : OracleComp spec α) := rfl

@[simp]
lemma liftM_query_readerT {ρ : Type v} {α : Type v} (q : OracleQuery spec α) :
  (liftM q : ReaderT ρ (OracleComp spec) α) = liftM (liftM q : OracleComp spec α) := rfl

lemma query_bind_eq_roll (q : OracleQuery spec α) (ob : α → OracleComp spec β) :
    (q : OracleComp spec α) >>= ob = FreeMonad.roll q ob := rfl

end lift

protected lemma pure_def (x : α) : (pure x : OracleComp spec α) = FreeMonad.pure x := rfl

protected lemma bind_def (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    oa >>= ob = FreeMonad.bind oa ob := rfl

protected lemma bind_congr' {oa oa' : OracleComp spec α} {ob ob' : α → OracleComp spec β}
    (h : oa = oa') (h' : ∀ x, ob x = ob' x) : oa >>= ob = oa' >>= ob' := h ▸ bind_congr h'

/-- `coin` is the computation representing a coin flip, given a coin flipping oracle. -/
@[reducible, inline] def coin : OracleComp coinSpec Bool :=
  coinSpec.query () ()

/-- `$[0..n]` is the computation choosing a random value in the given range, inclusively.
By making this range inclusive we avoid the case of choosing from the empty range. -/
@[reducible, inline] def uniformFin (n : ℕ) : ProbComp (Fin (n + 1)) :=
  unifSpec.query n ()

@[reducible, inline] def uniformFin' (n m : ℕ) : OracleComp probSpec (Fin (m + 1)) :=
  probSpec.query m n

notation "$[0.." n "]" => uniformFin n

-- TODO: could consider this notation if we switch to probspec
notation:50 "$[" n "⋯" m "]" => uniformFin' n m

example : OracleComp probSpec ℕ := do
  let x ← $[314⋯31415]; let y ← $[0⋯x]
  return x + 2 * y

-- `guard_eq` no longer applies since `OracleComp` has no failure branch.

-- NOTE: This should maybe be a `@[simp]` lemma? `apply_ite` can't be a simp lemma in general.
lemma ite_bind (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)
    (ob : α → OracleComp spec β) : ite p oa oa' >>= ob = ite p (oa >>= ob) (oa' >>= ob) :=
  apply_ite (· >>= ob) p oa oa'

/-- Nicer induction rule for `OracleComp` that uses monad notation.
Allows inductive definitions on compuations by considering the three cases:
* `return x` / `pure x` for any `x`
* `do let u ← query i t; oa u` (with inductive results for `oa u`)
See `oracleComp_emptySpec_equiv` for an example of using this in a proof.
If the final result needs to be a `Type` and not a `Prop`, see `OracleComp.construct`. -/
@[elab_as_elim]
protected def inductionOn {C : OracleComp spec α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (i : ι) → (t : spec.domain i) →
      (oa : spec.range i → OracleComp spec α) → (∀ u, C (oa u)) → C (query i t >>= oa))
    (oa : OracleComp spec α) : C oa :=
  FreeMonad.inductionOn pure (λ (query i t) ↦ query_bind i t) oa

@[elab_as_elim]
protected def induction {C : OracleComp spec α → Prop}
    (oa : OracleComp spec α) (pure : (a : α) → C (pure a))
    (query_bind : (i : ι) → (t : spec.domain i) →
      (oa : spec.range i → OracleComp spec α) → (∀ u, C (oa u)) → C (query i t >>= oa)) : C oa :=
  FreeMonad.inductionOn pure (λ (query i t) ↦ query_bind i t) oa

section construct

/-- NOTE: if `inductionOn` could work with `Sort u` instead of `Prop` we wouldn't need this,
not clear to me why lean doesn't like unifying the `Prop` and `Type` cases.

If the output type of `C` is a monad then `OracleComp.mapM` is usually preferable. -/
@[elab_as_elim]
protected def construct {C : OracleComp spec α → Type*}
    (pure : (a : α) → C (pure a))
    (query_bind : {β : Type v} → (q : OracleQuery spec β) →
      (oa : β → OracleComp spec α) → ((u : β) → C (oa u)) → C (q >>= oa))
    (oa : OracleComp spec α) : C oa :=
  FreeMonad.construct pure query_bind oa

/-- Version of `construct` with automatic induction on the `query` in when defining the
`query_bind` case. Can be useful with `spec.DecidableEq` and `spec.FiniteRange`.
NOTE: may be better to just use this universally in all cases? avoids duplicating lemmas below. -/
@[elab_as_elim]
protected def construct' {C : OracleComp spec α → Type*}
    (pure : (a : α) → C (pure a))
    (query_bind : (i : ι) → (t : spec.domain i) →
      (oa : spec.range i → OracleComp spec α) →
      ((u : spec.range i) → C (oa u)) → C (query i t >>= oa))
    (oa : OracleComp spec α) : C oa :=
  oa.construct pure (λ (query i t) ↦ query_bind i t)

variable {C : OracleComp spec α → Type w}
  (h_pure : (a : α) → C (pure a))
  (h_query_bind : {β : Type v} → (q : OracleQuery spec β) →
      (oa : β → OracleComp spec α) → ((u : β) → C (oa u)) → C (q >>= oa))
  (oa : OracleComp spec α)

@[simp]
lemma construct_pure (x : α) :
    OracleComp.construct h_pure h_query_bind (pure x) = h_pure x := rfl

@[simp]
lemma construct_query (q : OracleQuery spec α) :
    (OracleComp.construct h_pure h_query_bind (q : OracleComp spec α) : C q) =
      h_query_bind q pure h_pure := rfl
alias construct_liftM := construct_query

@[simp]
lemma construct_query_bind (q : OracleQuery spec β) (oa : β → OracleComp spec α) :
    (OracleComp.construct h_pure h_query_bind ((q : OracleComp spec β) >>= oa)) =
      h_query_bind q oa (λ u ↦ (oa u).construct h_pure h_query_bind) := rfl

@[simp]
lemma construct_roll (q : OracleQuery spec β) (oa : β → OracleComp spec α) :
    (OracleComp.construct h_pure h_query_bind (FreeMonad.roll q oa) :
      C (FreeMonad.roll q oa)) = h_query_bind q oa
        (λ u ↦ (oa u).construct h_pure h_query_bind) := rfl

end construct

section noConfusion

variable (x : α) (y : β) (q : OracleQuery spec β) (oa : β → OracleComp spec α)

/-- Returns `true` for computations that don't query any oracles or fail, else `false`. -/
def isPure {α : Type v} : OracleComp spec α → Bool
  | FreeMonad.pure _ => true
  | _ => false

@[simp] lemma isPure_pure : isPure (pure x : OracleComp spec α) = true := rfl
@[simp] lemma isPure_query_bind : isPure ((q : OracleComp spec β) >>= oa) = false := rfl

lemma exists_eq_of_isPure {oa : OracleComp spec α} (h : isPure oa) : ∃ x, oa = pure x := by
  induction oa using OracleComp.inductionOn with
  | pure => apply exists_apply_eq_apply'
  | query_bind => cases h

@[simp] lemma pure_ne_query : pure y ≠ (q : OracleComp spec β) := nofun
@[simp] lemma query_ne_pure : (q : OracleComp spec β) ≠ pure y := nofun

@[simp] lemma pure_ne_query_bind : pure x ≠ (q : OracleComp spec β) >>= oa := nofun
@[simp] lemma query_bind_ne_pure : (q : OracleComp spec β) >>= oa ≠ pure x := nofun

lemma pure_eq_query_iff_false : pure y = (q : OracleComp spec β) ↔ False := by
  constructor <;> intro h <;> cases h
lemma query_eq_pure_iff_false : (q : OracleComp spec β) = pure y ↔ False := by
  constructor <;> intro h <;> cases h

end noConfusion

section mapM

/-- Implement all queries in a computation using some other monad `m`,
preserving the pure and bind operations, giving a computation in the new monad.
The function `qm` specifies how to replace the queries in the computation,
If the final output type has an `Alternative` instance then `simulate` is usually preffered. -/
protected def mapM {m : Type v → Type w} [Monad m]
    (query_map : {α : Type v} → OracleQuery spec α → m α)
    (oa : OracleComp spec α) : m α :=
  FreeMonad.mapM oa query_map

variable {m : Type v → Type w} [Monad m]
  (qm : {α : Type v} → OracleQuery spec α → m α)

@[simp] lemma mapM_pure (x : α) : (pure x : OracleComp spec α).mapM qm = pure x := rfl

@[simp]
lemma mapM_query [LawfulMonad m] (q : OracleQuery spec α) :
    (q : OracleComp spec α).mapM qm = qm q :=
  by
    simp [OracleComp.mapM, OracleComp.liftM_def, FreeMonad.lift, FreeMonad.mapM]

@[simp]
lemma mapM_query_bind (q : OracleQuery spec α) (ob : α → OracleComp spec β) :
    ((q : OracleComp spec α) >>= ob).mapM qm =
      (do let x ← qm q; (ob x).mapM qm) := by
  simp [OracleComp.mapM, OracleComp.liftM_def, OracleComp.bind_def, FreeMonad.bind_lift,
    FreeMonad.mapM]

lemma mapM_bind [LawfulMonad m] (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    (oa >>= ob).mapM qm =
      oa.mapM qm >>= λ x ↦ (ob x).mapM qm := by
  induction oa with
  | pure x =>
      simp [OracleComp.mapM, OracleComp.bind_def, FreeMonad.mapM]
  | roll q r ih =>
      have hfun :
          (fun u => ((r u).bind ob).mapM qm) =
          (fun u => (r u).mapM qm >>= fun x => (ob x).mapM qm) := by
        funext u
        simpa [FreeMonad.monad_bind_def] using ih u
      simpa [OracleComp.mapM, OracleComp.bind_def, FreeMonad.mapM, FreeMonad.bind_roll] using
        congrArg (fun k => qm q >>= k) hfun

lemma mapM_map [LawfulMonad m] (oa : OracleComp spec α) (f : α → β) :
    (f <$> oa).mapM qm = f <$> oa.mapM qm := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  simpa using (mapM_bind (qm := qm) oa (fun x ↦ pure (f x)))

lemma mapM_seq [LawfulMonad m] (og : OracleComp spec (α → β)) (oa : OracleComp spec α)
    : (og <*> oa).mapM qm = og.mapM qm <*> oa.mapM qm := by
  rw [seq_eq_bind_map, seq_eq_bind_map]
  calc
    (og >>= fun g => g <$> oa).mapM qm
        = og.mapM qm >>= fun g => (g <$> oa).mapM qm := mapM_bind (qm := qm) og _
    _ = og.mapM qm >>= fun g => g <$> oa.mapM qm := by
      simp [mapM_map (qm := qm)]

@[simp]
lemma mapM_ite (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
    (ite p oa oa').mapM qm = ite p (oa.mapM qm) (oa'.mapM qm) := by
  split_ifs <;> rfl

end mapM

/-- Given a computation `oa : OracleComp spec α`, construct a value `x : α`,
by assuming each query returns the `default` value given by the `Inhabited` instance.
-/
def defaultResult [spec.FiniteRange] (oa : OracleComp spec α) : α :=
  oa.mapM (m := Id) (query_map := OracleQuery.defaultOutput)

/-- Total number of queries in a computation across all possible execution paths.
Can be a helpful alternative to `sizeOf` when proving recursive calls terminate. -/
def totalQueries [FiniteRange spec] {α : Type v} (oa : OracleComp spec α) : ℕ := by
  induction oa using OracleComp.construct' with
  | pure x => exact 0
  | query_bind i t oa rec_n =>
    exact 1 + ∑ x, rec_n x

section inj

@[simp]
lemma pure_inj (x y : α) : (pure x : OracleComp spec α) = pure y ↔ x = y := by
  rw [OracleComp.pure_def, OracleComp.pure_def, FreeMonad.pure.injEq]

@[simp]
lemma liftM_inj (q q' : OracleQuery spec α) : (q : OracleComp spec α) = q' ↔ q = q' := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    rfl

@[simp]
lemma query_inj (i : ι) (t t' : spec.domain i) :
    (query i t : OracleComp spec (spec.range i)) = query i t' ↔ t = t' := by
  simp only [liftM_inj, OracleQuery.query.injEq]

@[simp]
lemma queryBind_inj (q q' : OracleQuery spec α) (ob ob' : α → OracleComp spec β) :
    (q : OracleComp spec α) >>= ob = (q' : OracleComp spec α) >>= ob' ↔ q = q' ∧ ob = ob' := by
  simp only [OracleComp.liftM_def, OracleComp.bind_def, FreeMonad.monad_bind_def,
    FreeMonad.bind_lift]
  rw [FreeMonad.roll.injEq]
  simp only [heq_eq_eq, true_and]

@[simp]
lemma bind_eq_pure_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    oa >>= ob = pure y ↔ ∃ x : α, oa = pure x ∧ ob x = pure y := by
  refine ⟨λ h ↦ ?_, λ h ↦ let ⟨x, ⟨h, h'⟩⟩ := h; h ▸ h'⟩
  induction oa using OracleComp.induction with
  | pure x =>
      exact ⟨x, rfl, by simpa using h⟩
  | query_bind i t oa hoa =>
      cases h

@[simp]
lemma pure_eq_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    pure y = oa >>= ob ↔ ∃ x : α, oa = pure x ∧ ob x = pure y :=
  eq_comm.trans (bind_eq_pure_iff oa ob y)

alias ⟨_, bind_eq_pure⟩ := bind_eq_pure_iff
alias ⟨_, pure_eq_bind⟩ := pure_eq_bind_iff

end inj

/-- If the oracle indexing-type `ι`, output type `α`, and domains of all oracles have `DecidableEq`
then `OracleComp spec α` also has `DecidableEq`. -/
protected instance instDecidableEq [spec.FiniteRange] [hd : ∀ i, DecidableEq (spec.domain i)]
    [hι : DecidableEq ι] [h : DecidableEq α] : DecidableEq (OracleComp spec α) := fun
  | FreeMonad.pure x, FreeMonad.pure y =>
    match h x y with
    | isTrue rfl => isTrue rfl
    | isFalse h => isFalse λ h' ↦ h (by rwa [FreeMonad.pure.injEq] at h')
  | FreeMonad.pure x, FreeMonad.roll q r => isFalse <| by simp
  | FreeMonad.roll q r, FreeMonad.pure x => isFalse <| by simp
  | FreeMonad.roll (OracleQuery.query i t) r, FreeMonad.roll (OracleQuery.query i' t') s =>
    match hι i i' with
    | isTrue h => by
        induction h
        rw [FreeMonad.roll.injEq, heq_eq_eq, OracleQuery.query.injEq, eq_self, true_and, heq_eq_eq]
        refine @instDecidableAnd _ _ (hd i t t') ?_
        suffices Decidable (∀ u, r u = s u) from decidable_of_iff' _ funext_iff
        suffices ∀ u, Decidable (r u = s u) from Fintype.decidableForallFintype
        exact λ u ↦ OracleComp.instDecidableEq (r u) (s u)
    | isFalse h => isFalse λ h' ↦ h <|
        match FreeMonad.roll.inj h' with
        | ⟨h1, h2, _⟩ => @congr_heq _ _ ι OracleQuery.index OracleQuery.index
            (query i t) (query i' t') (h1 ▸ HEq.rfl) h2

end OracleComp
