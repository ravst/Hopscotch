import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions

noncomputable
def OnceRed {I : Type} (s : OracleSpec I) [∀ n, Inhabited (s.range n)] (iq : I → Bool) : SRReduction s s where
  stateType := Bool
  initialState := pure false
  queries := {
    impl n args :=
      if not (iq n) then
        srQuery(n, args)
      else do
        let g <- srGet!
        if g then (pure default)
        else do
          srSet(true)
          srQuery(n, args)
  }
