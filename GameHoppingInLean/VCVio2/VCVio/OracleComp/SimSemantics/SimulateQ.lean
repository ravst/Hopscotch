/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleComp
import GameHoppingInLean.VCVio2.ToMathlib.Control.StateT

/-!
# Simulation Semantics for Oracles in a Computation

This file defines a type `SimOracle spec specₜ σ` to represent a way to.Garbling.Simulate
oracles in `spec` using the oracles in `specₜ`, maintaining some state of type `σ`.
We then define a function `simulate so oa s` to simulate the computation `oa`
using `so` to answer oracle queries, with initial state `s`.

We mark lemmas regarding simulating specific computations as `@[simp low]`,
so that lemmas specific to certain simulation oracles get applied firts.
For example `idOracle` has no effect upon simulation, and we should apply that fact first.
-/

open OracleSpec Prod

universe u v w

variable {ι ι' ιₜ : Type*} {spec : OracleSpec ι}
    {spec' : OracleSpec ι'} {specₜ : OracleSpec ιₜ}
    {m : Type u → Type v} {α β γ σ : Type u}

/-- Specifies a way to simulate a set of oracles using another set of oracles.
e.g. using uniform selection oracles with a query cache to simulate a random oracle.
`simulateQ` gives a method for applying a simulation oracle to a specific computation. -/
@[ext]
structure QueryImpl {ι : Type w} (spec : OracleSpec ι) (m : Type u → Type v) where
  impl {α : Type u} (q : OracleQuery spec α) : m α

instance QueryImpl.Inhabited [∀ i, Inhabited (spec.range i)] [Pure m] :
  Inhabited (QueryImpl spec m) := ⟨{impl q := pure q.defaultOutput}⟩

lemma QueryImpl.ext' {so so' : QueryImpl spec m}
    (h : ∀ {α} (q : OracleQuery spec α), so.impl q = so'.impl q) :
    so = so' := QueryImpl.ext (funext λ _ ↦ funext λ q ↦ h q)

namespace OracleComp

/-- Canonical lifting of a function `OracleQuery spec α → m α`
to a new function `OracleComp spec α` by preserving `bind` and `pure`.
NOTE: could change the output type to `OracleComp spec →ᵐ m`, makes some stuff below free -/
def simulateQ [Monad m] (so : QueryImpl spec m) (oa : OracleComp spec α) : m α :=
  FreeMonad.mapM oa so.impl

variable [Monad m] (so : QueryImpl spec m)

@[simp] lemma simulateQ_ite (p : Prop) [Decidable p] (oa oa' : OracleComp spec α) :
    simulateQ so (ite p oa oa') = ite p (simulateQ so oa) (simulateQ so oa') := by
  split_ifs <;> rfl

@[simp] lemma simulateQ_query [LawfulMonad m] (q : OracleQuery spec α) :
    simulateQ so q = so.impl q := by
  simp [simulateQ, OracleComp.liftM_def, FreeMonad.lift, FreeMonad.mapM]

@[simp] lemma simulateQ_pure (x : α) : simulateQ so (pure x) = pure x :=
  by simp [simulateQ]

@[simp] lemma simulateQ_comp_pure_comp (f : α → β) : simulateQ so ∘ pure ∘ f = pure ∘ f := by
  funext x
  exact simulateQ_pure (so := so) (x := f x)

@[simp] lemma simulateQ_query_bind (q : OracleQuery spec α) (ob : α → OracleComp spec β) :
    simulateQ so (liftM q >>= ob) = so.impl q >>= (simulateQ so ∘ ob) := by
  simpa [Function.comp_def] using OracleComp.mapM_query_bind (qm := so.impl) q ob

@[simp] lemma simulateQ_bind [LawfulMonad m] (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    simulateQ so (oa >>= ob) = simulateQ so oa >>= (simulateQ so ∘ ob) := by
  simpa [Function.comp_def] using OracleComp.mapM_bind (qm := so.impl) oa ob

@[simp] lemma simulateQ_map [LawfulMonad m] (oa : OracleComp spec α) (f : α → β) :
    simulateQ so (f <$> oa) = f <$> simulateQ so oa := by
  simpa using OracleComp.mapM_map (qm := so.impl) oa f

@[simp] lemma simulateQ_seq [LawfulMonad m] (og : OracleComp spec (α → β)) (oa : OracleComp spec α) :
    simulateQ so (og <*> oa) = simulateQ so og <*> simulateQ so oa := by
  simpa using OracleComp.mapM_seq (qm := so.impl) og oa

@[simp] lemma simulateQ_seqLeft [LawfulMonad m] (oa : OracleComp spec α) (ob : OracleComp spec β) :
    simulateQ so (oa <* ob) = simulateQ so oa <* simulateQ so ob := by simp [seqLeft_eq]

@[simp] lemma simulateQ_seqRight [LawfulMonad m] (oa : OracleComp spec α) (ob : OracleComp spec β) :
    simulateQ so (oa *> ob) = simulateQ so oa *> simulateQ so ob := by simp [seqRight_eq]

-- NOTE: I don't think this is true in general
-- @[simp] lemma simulateQ_orElse (oa oa' : OracleComp spec α) :
--     simulateQ so (oa <|> oa') = (simulateQ so oa <|> simulateQ so oa') := by
--   simp only [simulateQ, Option.getM]
--   simp [OracleComp.orElse_def, OptionT.run]

end OracleComp

open OracleComp

/-- Simulate a computation using the original oracles by "replacing" queries with queries.
This operates as an actual identity for `simulate'`, in that we get an exact equality
between the new and original computation.
This can be useful especially with `SimOracle.append`, in order to simulate a single oracle
in a larger set of oracles, leaving the behavior of other oracles unchanged.
The relevant spec can usually be inferred automatically, so we leave it implicit. -/
def idOracle : QueryImpl spec (OracleComp spec) where impl q := OracleComp.lift q

namespace idOracle

@[simp] lemma apply_eq (q : OracleQuery spec α) : idOracle.impl q = q := rfl

@[simp] lemma simulateQ_eq_id : @simulateQ ι spec _ α _ idOracle = id := by
  refine funext fun oa => by induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind i t oa hoa =>
      simp [simulateQ, idOracle, OracleComp.lift, FreeMonad.lift, FreeMonad.mapM, Function.comp_def]
      funext u
      simpa using hoa u

lemma simulateQ_eq (oa : OracleComp spec α) : simulateQ idOracle oa = oa := by simp

end idOracle

/-- Simulate a computation by having each oracle return the default value of the query output type
for all queries. This gives a way to run arbitrary computations to get *some* output.
Mostly useful in some existence proofs, not usually used in an actual implementation. -/
def defaultOracle [spec.FiniteRange] : QueryImpl spec Option where
  impl | q => do return q.defaultOutput

namespace defaultOracle

@[simp] lemma apply_eq [spec.FiniteRange] (q : OracleQuery spec α) :
    defaultOracle.impl q = return q.defaultOutput := rfl

@[simp] lemma simulateQ_eq_getM_defaultResult [spec.FiniteRange] :
    @simulateQ ι spec _ α _ defaultOracle = some ∘ defaultResult := by
  refine funext fun oa => by induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind i t oa hoa =>
      simp [simulateQ, defaultOracle, defaultResult, OracleComp.mapM, FreeMonad.mapM, hoa,
        Function.comp_def]
      simpa [defaultResult, OracleComp.mapM] using hoa ((query i t).defaultOutput)

lemma simulateQ_eq [spec.FiniteRange] (oa : OracleComp spec α) :
    simulateQ defaultOracle oa = some oa.defaultResult := by simp

end defaultOracle
