import Hopscotch.Comp.StatefulRandomOracle
import Hopscotch.Comp.OracleReductions
import Hopscotch.ComputationalIndistinguishability.Distance

/- # Definitions of adversaries and their distinguishing advantage -/

def adversaryT {I : Type} (O : OracleSpec I) := OracleComp (withPMFSpec O) Bool

noncomputable def runDistinguisher {I : Type} {O : OracleSpec I}
    (d : adversaryT O) (impl : OracleImpl O) : PMF Bool :=
  let comp := simulateQ (addPMFtoImpl impl.queries) d
  do
    let init <- impl.initialState
    (comp init).map (fun x => x.1)

noncomputable def advantage {I : Type} {O : OracleSpec I}
    (distinguisher : adversaryT O) (o1 o2 : OracleImpl O) : Real :=
  pdistancePMF (runDistinguisher distinguisher o1) (runDistinguisher distinguisher o2)
