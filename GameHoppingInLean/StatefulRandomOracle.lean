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

structure QueryWithResult {I : Type u} (O : OracleSpec I) where
  input : I
  output : O input


structure RStateOracle {I : Type u} (O : OracleSpec I) where
  stateType : Type u
  initialState : PMF stateType
  queries : QueryImpl O (RState stateType)

noncomputable def runQueries2Aux {I : Type} {O : OracleSpec I} {S : Type} (impl : QueryImpl O (RState S)) (queries : List I) (init : S) :
  PMF (List (QueryWithResult O) × S) :=
  match queries with
  | [] => pure ([], init)
  | q :: qs => do
    let (out, s) <- StateT.run (impl q) init
    let (outL, sF) <- runQueries2Aux impl qs s
    return ({input := q, output := out}::outL, sF)

noncomputable def runQueries2 {I : Type} {O : OracleSpec I} (ro : RStateOracle O) (queries : List I) : PMF ((List (QueryWithResult O)) × ro.stateType) :=
  ro.initialState >>= runQueries2Aux ro.queries queries

/-- Run a finite list of concrete oracle queries and keep only their observable outputs. -/
noncomputable def runQueriesOnlyOut {I : Type} {O : OracleSpec I} (ro : RStateOracle O)
  (queries : List I) : PMF (List (QueryWithResult O)) :=
  (runQueries2 ro queries).map Prod.fst
