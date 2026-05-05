import GameHoppingInLean.MonadRandomState
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleComp
import GameHoppingInLean.VCVio2.VCVio.OracleComp.SimSemantics.SimulateQ
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleSpec


-- structure QueryImpl2 {ι : Type w} (spec : OracleSpec ι) (m : Type u → Type v) where
--   impl {i} (q : OracleSpec.OracleQuery spec (spec.range i)) : m (spec.range i)


structure QueryImpl3 {ι : Type w} (spec : OracleSpec ι) (m : Type u → Type v) where
  impl (i : ι) (t : spec.domain i) : m (spec.range i)

def query_impl_convert {ι : Type w} {spec : OracleSpec ι} {m : Type u → Type v}
  (x : QueryImpl3 spec m) : QueryImpl spec m :=
  { impl {α} q :=
    let (OracleSpec.OracleQuery.query i t) := q
    x.impl i t
  }

@[simp] lemma query_impl_convert_apply {ι : Type w} {spec : OracleSpec ι} {m : Type u → Type v}
    (x : QueryImpl3 spec m) {α : Type _} (q : OracleSpec.OracleQuery spec α) :
    (query_impl_convert x).impl q =
      match q with
      | OracleSpec.query i t => x.impl i t := by
  cases q
  rfl

@[simp] lemma query_impl_convert_apply_query {ι : Type w} {spec : OracleSpec ι}
    {m : Type u → Type v} (x : QueryImpl3 spec m) (i : ι) (t : spec.domain i) :
    (query_impl_convert x).impl (OracleSpec.query i t) = x.impl i t := rfl



structure QueryS {I : Type u} (O : OracleSpec I) where
  index : I
  input : O.domain index

structure QueryResult {I : Type u} (O : OracleSpec I) where
  index : I
  output : O.range index

structure QueryWithResult {I : Type u} (O : OracleSpec I) where
  index : I
  input : O.domain index
  output : O.range index


structure RStateOracle {I : Type u} (O : OracleSpec I) where
  stateType : Type u
  initialState : PMF stateType
  queries : QueryImpl3 O (RState stateType)

namespace RStateOracle

noncomputable def runQueries2Aux {I : Type} {O : OracleSpec I} {S : Type} (impl : QueryImpl3 O (RState S)) (queries : List (QueryS O)) (init : S):
  PMF (List (QueryResult O) × S) :=
  match queries with
  | [] => pure ([], init)
  | q :: qs => do
    let (out, s) <- StateT.run (impl.impl q.index q.input) init
    let (outL, sF) <- runQueries2Aux impl qs s
    return ({index := q.index, output := out}::outL, sF)

noncomputable def runQueries2 {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List (QueryS O)) : PMF ((List (QueryResult O)) × ro.stateType) :=
  ro.initialState >>= runQueries2Aux ro.queries queries

noncomputable def runQueriesOnlyOut {I : Type} {O : OracleSpec I} (ro : RStateOracle O)
  (queries : List (QueryS O)) : PMF (List (QueryResult O)) :=
  (RStateOracle.runQueries2 ro queries).map Prod.fst

end RStateOracle


structure BehavioralOracle {I : Type u} (O : OracleSpec I) : Type _ where
  process : List (QueryS O) -> PMF (List (QueryResult O))
  no_look_ahead : forall (ql : List (QueryS O)) (x1 x2 : QueryS O),
    (process (List.cons x1 ql)).map (List.tail) =
    (process (List.cons x2 ql)).map (List.tail)
  well_formed : forall (ql : List (QueryS O)),
      (process ql).map (fun l => l.map (QueryResult.index)) =
      pure (ql.map (QueryS.index))

structure BehavioralOracle2 {I : Type u} (O : OracleSpec I) : Type _ where
  process : List (QueryWithResult O) -> (QueryS O) -> PMF (QueryResult O)

namespace BehavioralOracle

lemma BehavioralOracleLengthPreserving {I : Type} (O : OracleSpec I) (x : BehavioralOracle O) :
  forall (ql : List (QueryS O)), pure ql.length = (x.process ql).map List.length :=
by
  sorry

noncomputable def into {I : Type} (O : OracleSpec I) (o : RStateOracle O) : BehavioralOracle O :=
{
  process (ql : List (QueryS O)) :=
    RStateOracle.runQueriesOnlyOut o ql
  no_look_ahead := sorry
  well_formed := sorry
}

end BehavioralOracle


-- def RStateOracleFam {I : Type} (O : OracleSpec I) := (κ : ℕ) -> RStateOracle O

-- lemma RStateOracle_idiotReduction {I : Type} {O : OracleSpec I}
--   (stateType : Type) (initialState : PMF stateType) (queries : QueryImpl O (RState stateType))  :
--   { stateType := stateType, initialState:= initialState, queries := queries : RStateOracle O}.queries = queries := by simp
