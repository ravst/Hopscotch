import GameHoppingInLean.MonadRandomState
import GameHoppingInLean.StatefulRandomOracle

structure QueryS {I : Type} (O : OracleSpec I) where
  index : I
  input : O.domain index

def QueryS.toQuery {I : Type} {O : OracleSpec I} (q : QueryS O) :
  OracleSpec.OracleQuery O (O.range q.index) :=
  OracleSpec.query q.index q.input

structure QueryResult {I : Type} (O : OracleSpec I) where
  index : I
  output : O.range index

noncomputable def runQueriesAux {I : Type} {O : OracleSpec I} {S : Type} (impl : QueryImpl O (RState S)) (queries : List (QueryS O)) :
  RState S (List (QueryResult O)) :=
  match queries with
  | [] => pure []
  | q :: qs => do
    let o ← impl.impl (q.toQuery)
    (fun os =>  ({index := q.index, output := o} :: os)) <$> runQueriesAux impl qs

noncomputable def runQueries {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List (QueryS O)) : PMF (List (QueryResult O)) :=
  (runQueriesAux ro.queries queries).eval ro.initialState

/-- Two stateful random oracles are observationally equal if, after any finite replay
context of prior queries, they induce the same output distribution on every next query. -/
def ObsEq (ro₁ ro₂ : RStateOracle O) : Prop :=
  ∀ queriesList, runQueries ro₁ queriesList = runQueries ro₂ queriesList

-- Now, we would like to show a sufficient condition for two oracles to be observationally equivalent.
-- Suppose that we have a a pair of functions `f₁ : S₁ → S` and `f₂ : S₂ → S` where `S` is some "abstract state space" that captures
-- all the relevant information. Then, if the initial states induce the same distribution on `s`, and the query imlementation
-- if each oracle is compatible with the abstraction, i.e. if two states `f₁(s₁) = f₂(s₂)` then the implementation of each
-- query on `S₁` and `S₂` induces the same distribution on (Output × S), then the two oracles are observationally equivalent.
-- This is a kind of "bisimulation" condition, and is often easier to check than the full definition of observational equivalence.

-- I think I need an aux function that takes a function, a pair and applies this function to the second element of the pair, and leaves the first element alone.
def mapSecond {α β γ} (f : β → γ) (p : α × β) : α × γ :=
  (p.1, f p.2)

def correctAbstraction {S I : Type} {O : OracleSpec I} (ro₁ ro₂ : RStateOracle O)
    (f₁ : ro₁.stateType → S) (f₂ : ro₂.stateType → S) : Prop :=
  ro₁.initialState.map f₁ = ro₂.initialState.map f₂ ∧
  ∀ (s₁ : ro₁.stateType) (s₂ : ro₂.stateType) (i) (t : O.domain i),
    f₁ s₁ = f₂ s₂ →
      (mapSecond f₁) <$> (StateT.run (ro₁.queries.impl (OracleSpec.query i t)) s₁) =
      (mapSecond f₂) <$> (StateT.run (ro₂.queries.impl (OracleSpec.query i t)) s₂)

def correctAbstractionImpliesObsEq {S : Type} (ro₁ ro₂ : RStateOracle O)
    (f₁ : ro₁.stateType → S) (f₂ : ro₂.stateType → S) :
    correctAbstraction ro₁ ro₂ f₁ f₂ → ObsEq ro₁ ro₂ := by
    sorry

def obsEqReflexive (ro₁ ro₂ : RStateOracle O) (hEq : ro₁ = ro₂) :
  ObsEq ro₁ ro₂ := sorry
