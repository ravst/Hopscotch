import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.ComputationalIndistinguishibility.EmptyTypes

structure BehavioralOracle {I : Type u} (O : OracleSpec  I) (q_b : ENat): Type _ where
  process : (l : List (O.Domain)) -> (l.length <= q_b) -> PMF (List (QueryWithResult O))
  no_look_ahead : forall (ql : List (O.Domain)) (H : ql.length+1 <= q_b) (x1 x2 : O.Domain),
    (process (List.cons x1 ql) H).map (List.tail) =
    (process (List.cons x2 ql) H).map (List.tail)
  well_formed : forall (ql : List (O.Domain)) (H : ql.length <= q_b),
      (process ql H).map (fun l => l.map (QueryWithResult.input)) =
      pure ql
  good_spec : forall x : I, Nonempty (O x)

structure BehavioralOracle2 {I : Type u} (O : OracleSpec I) (q_b : ENat) : Type u where
  process : (ql : List (QueryWithResult O)) -> (ql.length <= q_b) -> (q : O.Domain) -> PMF (O.Range q)
  good_spec : forall x : I, Nonempty (O x)


namespace BehavioralOracle

lemma BehavioralOracleLengthPreserving {I : Type} {O : OracleSpec  I} {q_b} (x : BehavioralOracle O q_b) :
  forall (ql : List (O.Domain)) (H : ql.length <= q_b), pure ql.length = (x.process ql H).map List.length :=
by
  sorry

noncomputable def into {I : Type} {O : OracleSpec I} (q_b : ENat) (o : RStateOracle O) :
  BehavioralOracle O q_b :=
{
  process (ql : List (O.Domain)) (H : ql.length <= q_b) :=
    runQueriesOnlyOut o ql
  no_look_ahead := sorry
  well_formed := sorry
  good_spec := non_trivial_spec o
}

end BehavioralOracle

-- hard, we need to do conditional probabilities.
def behavioralOracle1to2 {I : Type u} {O : OracleSpec  I} {q_b : ENat} (x : BehavioralOracle O q_b) : BehavioralOracle2 O q_b :=
  {
    process := sorry
    good_spec := x.good_spec
  }

noncomputable def behavioralOracle2toRstate {I : Type} {O : OracleSpec I} {q_b : ENat}
  (x : BehavioralOracle2 O q_b) : RStateOracle O where
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

noncomputable def behavioralOracle1toRstate {I : Type} {O : OracleSpec  I} {q_b : ENat}
  (x : BehavioralOracle O q_b) : RStateOracle O :=
  behavioralOracle2toRstate (behavioralOracle1to2 x)

noncomputable def rState2Rstate {I : Type} {O : OracleSpec  I} (q_b : ENat) (x : RStateOracle O) : RStateOracle O :=
  behavioralOracle1toRstate (BehavioralOracle.into q_b x)
