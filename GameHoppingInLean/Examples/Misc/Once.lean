import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.ObservationalEquvialence

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

noncomputable
def once {I : Type} {s : OracleSpec I} [∀ n, Inhabited (s.range n)] (iq : I → Bool) (o : RStateOracle s) : RStateOracle s :=
  applySRReduction (OnceRed s iq) o

noncomputable
def simpleLocalRandomness {A} {I : Type} {s : OracleSpec I} (o : RStateOracle s) (iq : I → Bool) (r : PMF A) (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι)) :=
  { o with queries := {
    impl n args :=
      if not (iq n) then o.queries.impl n args else do
        let a ← r
        f a n args
  }}

noncomputable
def simpleGlobalRandomness {A} {I : Type} {s : OracleSpec I} (o : RStateOracle s) (iq : I → Bool) (r : PMF A) (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι)) : RStateOracle s := {
  stateType := A × o.stateType
  initialState := do
    let a ← r
    let st ← o.initialState
    pure ⟨a, st⟩
  queries := {
    impl n args :=
      if not (iq n) then (o.queries.impl n args).runOnSnd
      else do
        let st <- get
        (f st.1 n args).runOnSnd
  }
}

theorem OnceRedSimpleRandomnesGlobalLocalObsEq {I : Type} {s : OracleSpec I} [∀ n, Inhabited (s.range n)] (iq : I → Bool) (o : RStateOracle s) (r : PMF A) (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι)):
  ObsEq
    (once iq (simpleLocalRandomness o iq r f))
    (once iq (simpleGlobalRandomness o iq r f)) :=
  sorry
