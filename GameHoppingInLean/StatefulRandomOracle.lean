import GameHoppingInLean.MonadRandomState
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.OracleSpec


/-!
# definition of various computation with oracles in rstate
-/

-- structure OracleSpec  (ι : Type u) where
--   domain : ι -> Type v
--   range : ι -> Type w

-- def toSpec {ι : Type _} (spec : OracleSpec ι) : OracleSpec ( (i: ι) × (spec.domain i) )
-- | ⟨a, _b⟩ =>
--     spec.range a

-- structure QueryImpl3 {ι : Type w} (spec : OracleSpec  ι) (m : Type u → Type v) where
--   impl (i : ι) (t : spec.domain i) : m (spec.range i)

-- def query_impl_convert {ι : Type w} {spec : OracleSpec  ι} {m : Type u → Type v}
--   (x : QueryImpl3 spec m) : QueryImpl (toSpec spec) m :=
--   fun ⟨α, q⟩ =>
-- --     x.impl i t

-- @[simp] lemma query_impl_convert_apply {ι : Type w} {spec : OracleSpec  ι} {m : Type u → Type v}
--     (x : QueryImpl3 spec m) {α : Type _} (q : OracleSpec .OracleQuery spec α) :
--     (query_impl_convert x).impl q =
--       match q with
--       | OracleSpec .query i t => x.impl i t := by
--   cases q
--   rfl

-- @[simp] lemma query_impl_convert_apply_query {ι : Type w} {spec : OracleSpec  ι}
--     {m : Type u → Type v} (x : QueryImpl3 spec m) (i : ι) (t : spec.domain i) :
--     (query_impl_convert x).impl (OracleSpec .query i t) = x.impl i t := rfl



-- structure QueryS {I : Type u} (O : OracleSpec  I) where
--   index : I
--   input : O.domain index

-- structure QueryResult {I : Type u} (O : OracleSpec  I) where
--   index : I
--   output : O.range index

structure QueryWithResult {I : Type u} (O : OracleSpec  I) where
  input : I
  output : O input


structure RStateOracle {I : Type u} (O : OracleSpec I) where
  stateType : Type u
  initialState : PMF stateType
  queries : QueryImpl O (RState stateType)

noncomputable def runQueries2Aux {I : Type} {O : OracleSpec I} {S : Type} (impl : QueryImpl O (RState S)) (queries : List I) (init : S):
  PMF (List (QueryWithResult O) × S) :=
  match queries with
  | [] => pure ([], init)
  | q :: qs => do
    let (out, s) <- StateT.run (impl q) init
    let (outL, sF) <- runQueries2Aux impl qs s
    return ({input := q, output := out}::outL, sF)

noncomputable def runQueries2 {I : Type} {O : OracleSpec  I} (ro : RStateOracle O) (queries : List I) : PMF ((List (QueryWithResult O)) × ro.stateType) :=
  ro.initialState >>= runQueries2Aux ro.queries queries

noncomputable def runQueriesOnlyOut {I : Type} {O : OracleSpec I} (ro : RStateOracle O)
  (queries : List I) : PMF (List (QueryWithResult O)) :=
  (runQueries2 ro queries).map Prod.fst


-- structure BehavioralOracle {I : Type u} (O : OracleSpec  I) (q_b : ENat): Type _ where
--   process : (l : List (QueryS O)) -> (l.length <= q_b) -> PMF (List (QueryResult O))
--   no_look_ahead : forall (ql : List (QueryS O)) (H : ql.length+1 <= q_b) (x1 x2 : QueryS O),
--     (process (List.cons x1 ql) H).map (List.tail) =
--     (process (List.cons x2 ql) H).map (List.tail)
--   well_formed : forall (ql : List (QueryS O)) (H : ql.length <= q_b),
--       (process ql H).map (fun l => l.map (QueryResult.index)) =
--       pure (ql.map (QueryS.index))

-- structure BehavioralOracle2 {I : Type u} (O : OracleSpec  I) (q_b : ENat): Type _ where
--   process : (ql : List (QueryWithResult O)) -> (ql.length <= q_b) -> (i : I) -> (O.domain i) -> PMF (O.range i)

-- namespace BehavioralOracle

-- lemma BehavioralOracleLengthPreserving {I : Type} {O : OracleSpec  I} {q_b} (x : BehavioralOracle O q_b) :
--   forall (ql : List (QueryS O)) (H : ql.length <= q_b), pure ql.length = (x.process ql H).map List.length :=
-- by
--   sorry

-- noncomputable def into {I : Type} {O : OracleSpec  I} (q_b : ENat) (o : RStateOracle O) : BehavioralOracle O q_b :=
-- {
--   process (ql : List (QueryS O)) (H : ql.length <= q_b) :=
--     RStateOracle.runQueriesOnlyOut o ql
--   no_look_ahead := sorry
--   well_formed := sorry
-- }

-- end BehavioralOracle

-- -- hard, we need to do conditional probabilities.
-- def behavioralOracle1to2 {I : Type u} {O : OracleSpec  I} {q_b : ENat} (x : BehavioralOracle O q_b) : BehavioralOracle2 O q_b :=
--   sorry

-- noncomputable def behavioralOracle2toRstate {I : Type} {O : OracleSpec  I} {q_b : ENat}
--   (x : BehavioralOracle2 O q_b) : RStateOracle O where
--   stateType := List (QueryWithResult O)
--   initialState := pure []
--   queries := {
--     impl i q :=
--       do
--         let state <- get
--         if H : state.length <= q_b then
--           let out <- x.process state H i q
--           set ({index := i, input := q, output := out : QueryWithResult O} :: state)
--           pure out
--         else
--           -- problem with q_b==0 and O.range i = Empty
--           sorry
--   }


-- noncomputable def behavioralOracle1toRstate {I : Type} {O : OracleSpec  I} {q_b : ENat}
--   (x : BehavioralOracle O q_b) : RStateOracle O :=
--   behavioralOracle2toRstate (behavioralOracle1to2 x)

-- noncomputable def rState2Rstate {I : Type} {O : OracleSpec  I} (q_b : ENat) (x : RStateOracle O) : RStateOracle O :=
--   behavioralOracle1toRstate (BehavioralOracle.into q_b x)
