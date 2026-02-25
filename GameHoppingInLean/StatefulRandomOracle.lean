import GameHoppingInLean.MonadRandomState
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleComp
import GameHoppingInLean.VCVio2.VCVio.OracleComp.SimSemantics.SimulateQ
import GameHoppingInLean.VCVio2.VCVio.OracleComp.OracleSpec


structure RStateOracle {I : Type} (O : OracleSpec I) where
  stateType : Type
  initialState : PMF stateType
  queries : QueryImpl O (RState stateType)
