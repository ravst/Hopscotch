import GameHoppingInLean.Comp.StatefulRandomOracle
import GameHoppingInLean.ComputationalIndistinguishibility.EmptyTypes
import Mathlib

/- # Behavioral Oracle
 We provide behavioral definition of oracle implementation. Contrary to OracleImpl, behavioral definition does not involve any internal state.
   We define functions that transform OracleImpl into behavioral version and back. We prove that resulting oracle is ObsEq with original.

  This notion is used on ObsEqComp.lean to prove that ObsEq implies indistinguishability for adversaries (see there for more).
-/

structure BehavioralOracle {I : Type u} (O : OracleSpec I) (q_b : ENat) : Type _ where
  process : (l : List (O.Domain)) -> (l.length <= q_b) -> PMF (List (QueryWithResult O))
  no_look_ahead : forall (ql : List (O.Domain)) (H : ql.length+1 <= q_b) (x1 x2 : O.Domain),
    (process (List.cons x1 ql) H).map (List.tail) =
    (process (List.cons x2 ql) H).map (List.tail)
  well_formed : forall (ql : List (O.Domain)) (H : ql.length <= q_b),
      (process ql H).map (fun l => l.map (QueryWithResult.input)) =
      pure ql
  good_spec : forall x : I, Nonempty (O x)

-- alternative definition of behavioral oracle.
structure BehavioralOracle2 {I : Type u} (O : OracleSpec I) (q_b : ENat) : Type u where
  process : (ql : List (QueryWithResult O)) -> (ql.length <= q_b) -> (q : O.Domain) -> PMF (O.Range q)
  good_spec : forall x : I, Nonempty (O x)


--#  We take a short break to prove a few technical lemmas that allow conversion from BehavioralOracle to BehavioralOracle2.

/-- The input list recorded by `runQueriesOnlyOut` is exactly the list of queries asked,
in order. -/
lemma runQueriesOnlyOut_map_input {I : Type} {O : OracleSpec I} (o : OracleImpl O)
    (qs : List I) :
    (runQueriesOnlyOut o qs).map (fun l => l.map (QueryWithResult.input)) = pure qs := by
  have aux : ∀ (qs : List I) (s : o.stateType),
      (runQueries2Aux o.queries qs s).map (fun p => p.1.map (QueryWithResult.input)) = PMF.pure qs := by
    intro qs
    induction qs with
    | nil => intro s; simp [runQueries2Aux, sPMF]
    | cons q rest ih =>
        intro s
        have key : ∀ s', (runQueries2Aux o.queries rest s').bind
            (fun y => PMF.pure (q :: y.1.map (QueryWithResult.input))) = PMF.pure (q :: rest) := by
          intro s'
          have e1 : (runQueries2Aux o.queries rest s').bind
                (fun y => PMF.pure (q :: y.1.map (QueryWithResult.input)))
              = (runQueries2Aux o.queries rest s').map
                (fun y => q :: y.1.map (QueryWithResult.input)) := rfl
          rw [e1, show (fun y : List (QueryWithResult O) × o.stateType => q :: y.1.map (QueryWithResult.input))
                = (fun l => q :: l) ∘ (fun y => y.1.map (QueryWithResult.input)) from rfl,
            ← PMF.map_comp, ih s', PMF.pure_map]
        have hstep : runQueries2Aux o.queries (q::rest) s =
            (StateT.run (o.queries q) s).bind (fun x =>
              (runQueries2Aux o.queries rest x.2).bind (fun y =>
                PMF.pure (⟨q, x.1⟩ :: y.1, y.2))) := rfl
        rw [hstep, PMF.map_bind]
        simp only [PMF.map_bind, PMF.pure_map, List.map_cons]
        simp only [key, PMF.bind_const]
  have hbind : (o.initialState >>= runQueries2Aux o.queries qs)
      = o.initialState.bind (runQueries2Aux o.queries qs) := rfl
  rw [runQueriesOnlyOut, runQueries2, PMF.map_comp, hbind, PMF.map_bind]
  have hfun : (fun s => PMF.map ((fun l => l.map (QueryWithResult.input)) ∘ Prod.fst)
        (runQueries2Aux o.queries qs s))
      = (fun _ : o.stateType => PMF.pure qs) := by
    funext s
    rw [show ((fun l : List (QueryWithResult O) => l.map (QueryWithResult.input)) ∘ Prod.fst)
          = (fun p : List (QueryWithResult O) × o.stateType => p.1.map (QueryWithResult.input)) from rfl]
    exact aux qs s
  rw [hfun, PMF.bind_const]
  rfl

/-- Running the concatenation of two query lists is the same as running the first, then running
the second from the resulting state and concatenating the recorded results. -/
lemma runQueries2Aux_append {I : Type} {O : OracleSpec I} {S : Type}
    (impl : QueryImpl O (RState S)) (qs' : List I) :
    ∀ (qs : List I) (s : S),
      runQueries2Aux impl (qs ++ qs') s
        = (runQueries2Aux impl qs s).bind (fun p =>
            (runQueries2Aux impl qs' p.2).map (fun p' => (p.1 ++ p'.1, p'.2))) := by
  intro qs
  induction qs with
  | nil =>
      intro s
      rw [List.nil_append,
        show runQueries2Aux impl ([] : List I) s
            = PMF.pure (([] : List (QueryWithResult O)), s) from rfl,
        PMF.pure_bind,
        show (fun p' : List (QueryWithResult O) × S => (([] : List (QueryWithResult O)) ++ p'.1, p'.2))
            = (id : List (QueryWithResult O) × S → List (QueryWithResult O) × S) from by
              funext p'; rfl,
        PMF.map_id]
  | cons q rest ih =>
      intro s
      have hL : runQueries2Aux impl (q :: rest ++ qs') s =
          (StateT.run (impl q) s).bind (fun a =>
            (runQueries2Aux impl (rest ++ qs') a.2).bind (fun y =>
              PMF.pure (⟨q, a.1⟩ :: y.1, y.2))) := rfl
      have hR : runQueries2Aux impl (q :: rest) s =
          (StateT.run (impl q) s).bind (fun a =>
            (runQueries2Aux impl rest a.2).bind (fun y =>
              PMF.pure (⟨q, a.1⟩ :: y.1, y.2))) := rfl
      rw [hL, hR, PMF.bind_bind]
      congr 1
      funext a
      rw [ih a.2, PMF.bind_bind, PMF.bind_bind]
      congr 1
      funext w
      rw [PMF.bind_map, PMF.pure_bind]
      rfl

/-- Asking one more query at the very end and then discarding its result yields the same
distribution on the earlier results as not asking it at all: a later query cannot influence
the results of earlier ones. -/
lemma runQueriesOnlyOut_map_dropLast_append {I : Type} {O : OracleSpec I} (o : OracleImpl O)
    (qs : List I) (x : I) :
    (runQueriesOnlyOut o (qs ++ [x])).map List.dropLast = runQueriesOnlyOut o qs := by
  have hx : ∀ (t : o.stateType),
      runQueries2Aux o.queries [x] t
        = (StateT.run (o.queries x) t).map (fun a => ([⟨x, a.1⟩], a.2)) := by
    intro t
    change (StateT.run (o.queries x) t).bind (fun a =>
        (runQueries2Aux o.queries [] a.2).bind (fun y => PMF.pure (⟨x, a.1⟩ :: y.1, y.2)))
      = (StateT.run (o.queries x) t).map (fun a => ([⟨x, a.1⟩], a.2))
    rw [PMF.map]
    congr 1
    funext a
    rw [show runQueries2Aux o.queries ([] : List I) a.2
          = PMF.pure (([] : List (QueryWithResult O)), a.2) from rfl, PMF.pure_bind]
    rfl
  have aux : ∀ (s : o.stateType),
      (runQueries2Aux o.queries (qs ++ [x]) s).map (fun p => p.1.dropLast)
        = (runQueries2Aux o.queries qs s).map Prod.fst := by
    intro s
    rw [runQueries2Aux_append o.queries [x] qs s, PMF.map_bind,
      show (runQueries2Aux o.queries qs s).map Prod.fst
          = (runQueries2Aux o.queries qs s).bind (fun p => PMF.pure p.1) from rfl]
    congr 1
    funext p
    rw [hx p.2, PMF.map_comp, PMF.map_comp]
    have hconst : (((fun r : List (QueryWithResult O) × o.stateType => r.1.dropLast)
          ∘ (fun p' : List (QueryWithResult O) × o.stateType => (p.1 ++ p'.1, p'.2)))
          ∘ (fun a : O.Range x × o.stateType => ([⟨x, a.1⟩], a.2)))
        = (fun _ : O.Range x × o.stateType => p.1) := by
      funext a; simp [Function.comp, List.dropLast_concat]
    rw [hconst,
      show (StateT.run (o.queries x) p.2).map (fun _ : O.Range x × o.stateType => p.1)
          = (StateT.run (o.queries x) p.2).bind (fun _ => PMF.pure p.1) from rfl,
      PMF.bind_const]
  have hb : ∀ ys, (o.initialState >>= runQueries2Aux o.queries ys)
      = o.initialState.bind (runQueries2Aux o.queries ys) := fun _ => rfl
  rw [runQueriesOnlyOut, runQueriesOnlyOut, runQueries2, runQueries2, hb, hb,
    PMF.map_comp, PMF.map_bind, PMF.map_bind]
  congr 1
  funext s
  rw [show (List.dropLast ∘ Prod.fst : List (QueryWithResult O) × o.stateType → _)
        = (fun p : List (QueryWithResult O) × o.stateType => p.1.dropLast) from rfl]
  exact aux s

namespace BehavioralOracle

lemma BehavioralOracleLengthPreserving {I : Type} {O : OracleSpec I} {q_b} (x : BehavioralOracle O q_b) :
  forall (ql : List (O.Domain)) (H : ql.length <= q_b), pure ql.length = (x.process ql H).map List.length :=
by
  intro ql H
  have hw := x.well_formed ql H
  have h2 : (x.process ql H).map List.length
        = ((x.process ql H).map (fun l => l.map (QueryWithResult.input))).map List.length := by
    rw [PMF.map_comp]; congr 1; funext l; simp [Function.comp, List.length_map]
  rw [h2, hw]
  exact (PMF.pure_map List.length ql).symm

/-- Well-formedness of the behavioral oracle obtained from an `OracleImpl`.

We model the history list with the most recent query at the head (newest-first), so to run an
`OracleImpl` on the history `ql` we replay the queries in chronological order (`ql.reverse`)
and then put the answers back in newest-first order (`.map List.reverse`). With this convention
the recorded inputs are exactly `ql`. -/
lemma into_well_formed {I : Type} {O : OracleSpec I} (o : OracleImpl O) :
    forall (ql : List I),
      ((runQueriesOnlyOut o ql.reverse).map List.reverse).map (fun l => l.map (QueryWithResult.input)) =
        pure ql := by
  intro ql
  rw [PMF.map_comp,
    show ((fun l : List (QueryWithResult O) => l.map (QueryWithResult.input)) ∘ List.reverse)
        = (List.reverse ∘ (fun l : List (QueryWithResult O) => l.map (QueryWithResult.input))) from by
          funext l; simp [Function.comp, List.map_reverse],
    ← PMF.map_comp, runQueriesOnlyOut_map_input,
    show (pure ql.reverse : PMF (List I)) = PMF.pure ql.reverse from rfl,
    PMF.pure_map, List.reverse_reverse]
  rfl

/-- The "no look ahead" property of the behavioral oracle obtained from an `OracleImpl`:
the distribution of the answers to the earlier queries `ql` does not depend on the most recent
query (`x1` or `x2`) sitting at the head of the history. This holds because, after replaying in
chronological order, the most recent query is processed last and hence cannot affect the earlier
answers. -/
lemma into_no_look_ahead {I : Type} {O : OracleSpec I} (o : OracleImpl O) :
    forall (ql : List I) (x1 x2 : I),
      (((runQueriesOnlyOut o (List.cons x1 ql).reverse).map List.reverse).map List.tail) =
      (((runQueriesOnlyOut o (List.cons x2 ql).reverse).map List.reverse).map List.tail) := by
  intro ql x1 x2
  have step : ∀ z : I,
      (((runQueriesOnlyOut o (z :: ql).reverse).map List.reverse).map List.tail)
        = (runQueriesOnlyOut o ql.reverse).map List.reverse := by
    intro z
    rw [List.reverse_cons, PMF.map_comp,
      show (List.tail ∘ List.reverse : List (QueryWithResult O) → List (QueryWithResult O))
          = (List.reverse ∘ List.dropLast) from by
            funext l; simp [Function.comp, List.tail_reverse],
      ← PMF.map_comp, runQueriesOnlyOut_map_dropLast_append]
  rw [step x1, step x2]

--#  Conversion BehavioralOracle -> BehavioralOracle2 -> OracleImpl

/-- Realise an `OracleImpl` as a `BehavioralOracle`.

We replay the history in chronological order (`ql.reverse`) and report the answers newest-first (`.map List.reverse`), which satisfies both `well_formed` and `no_look_ahead`. -/
noncomputable def into {I : Type} {O : OracleSpec I} (q_b : ENat) (o : OracleImpl O) :
  BehavioralOracle O q_b :=
{
  process (ql : List (O.Domain)) (_H : ql.length <= q_b) :=
    (runQueriesOnlyOut o ql.reverse).map List.reverse
  no_look_ahead := by
    intro ql _H x1 x2
    exact into_no_look_ahead o ql x1 x2
  well_formed := by
    intro ql _H
    exact into_well_formed o ql
  good_spec := non_trivial_spec o
}

end BehavioralOracle

/- Conditional/defaulted map of a `PMF`: condition `d` on the event `s` (when it has positive
mass) and push the result through `f`; otherwise return the point mass at `dflt`. -/
open Classical in
noncomputable def condMap {α : Type u} {β : Type v} (d : PMF α) (s : Set α) (f : α → β) (dflt : β) :
    PMF β :=
  if h : ∃ a ∈ s, a ∈ d.support then (d.filter s h).map f else pure dflt

/-- Extract the output of the head of a query-result list as an element of `O q`, provided the
head was a query on `q`; otherwise return the supplied default. -/
noncomputable def extractHead {I : Type u} {O : OracleSpec I} (q : I) (dflt : O q)
    (l : List (QueryWithResult O)) : O q :=
  match l with
  | [] => dflt
  | a :: _ => @dite _ (a.input = q) (Classical.propDecidable _) (fun h => h ▸ a.output) (fun _ => dflt)

-- hard, we need to do conditional probabilities.
-- the intuition is that when processing a list L of List (QueryWithResult O), we should run
-- x.process on the list of inputs of `q :: L` (ignoring outputs) and then condition on the fact
-- that the previous queries (everything but the last/newest one) got outputs as specified in the
-- list L. In the result we get a distribution on the outputs of the last query asked.
noncomputable def behavioralOracle1to2 {I : Type u} {O : OracleSpec I} {q_b : ENat}
    (x : BehavioralOracle O q_b) : BehavioralOracle2 O q_b :=
  {
    process := fun ql _H q =>
      if H1 : ((ql.length + 1 : ℕ) : ENat) ≤ q_b then
        let dflt := Classical.choice (x.good_spec q)
        condMap (x.process (q :: ql.map (QueryWithResult.input)) (by simpa using H1))
          {l | l.tail = ql} (extractHead q dflt) dflt
      else
        pure (Classical.choice (x.good_spec q))
    good_spec := x.good_spec
  }

noncomputable def behavioralOracle2toRstate {I : Type} {O : OracleSpec I} {q_b : ENat}
  (x : BehavioralOracle2 O q_b) : OracleImpl O where
  stateType := List (QueryWithResult O)
  initialState := pure []
  queries := fun q =>
      do
        let state <- get
        if H : state.length <= q_b then
          let out : O.Range q <- x.process state H q
          set ({input := q, output := out : QueryWithResult O} :: state)
          pure out
        else
          -- error branch, we are not processing that many queires in any meaningful way
          let out : O.Range q := Classical.choice (x.good_spec q)
          pure out

noncomputable def behavioralOracle1toRstate {I : Type} {O : OracleSpec I} {q_b : ENat}
  (x : BehavioralOracle O q_b) : OracleImpl O :=
  behavioralOracle2toRstate (behavioralOracle1to2 x)

noncomputable def rState2Rstate {I : Type} {O : OracleSpec I} (q_b : ENat) (x : OracleImpl O) : OracleImpl O :=
  behavioralOracle1toRstate (BehavioralOracle.into q_b x)

-- # The prove of important lemmas is in ObsEqComp
