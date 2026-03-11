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
    by
      cases q
      case query i t =>
      apply x.impl i t
  }

structure RStateOracle {I : Type} (O : OracleSpec I) where
  stateType : Type
  initialState : PMF stateType
  queries : QueryImpl3 O (RState stateType)


-- lemma RStateOracle_idiotReduction {I : Type} {O : OracleSpec I}
--   (stateType : Type) (initialState : PMF stateType) (queries : QueryImpl O (RState stateType))  :
--   { stateType := stateType, initialState:= initialState, queries := queries : RStateOracle O}.queries = queries := by simp
