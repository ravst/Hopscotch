import Hopscotch.Comp.RState
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.OracleSpec


/-!
# definition of oracle implementation
Type OracleImpl defines implementation of oracle in RState monad.
-/


structure QueryWithResult {I : Type u} (O : OracleSpec I) where
  input : I
  output : O input


/-- Implementation of oracle in RState monad. -/
structure OracleImpl {I : Type u} (O : OracleSpec I) where
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

noncomputable def runQueries2 {I : Type} {O : OracleSpec I} (ro : OracleImpl O) (queries : List I) : PMF ((List (QueryWithResult O)) × ro.stateType) :=
  ro.initialState >>= runQueries2Aux ro.queries queries

/-- Run a finite list of concrete oracle queries and keep only their observable outputs. -/
noncomputable def runQueriesOnlyOut {I : Type} {O : OracleSpec I} (ro : OracleImpl O)
  (queries : List I) : PMF (List (QueryWithResult O)) :=
  (runQueries2 ro queries).map Prod.fst
