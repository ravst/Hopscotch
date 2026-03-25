import GameHoppingInLean.StatefulRandomOracle
import GameHoppingInLean.OracleReductions
import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.FreeMonadLemmas

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


lemma onceInitialState {I : Type} {s : OracleSpec I} [∀ n, Inhabited (s.range n)] (iq : I → Bool) (o : RStateOracle s) : (once iq o).initialState = (o.initialState.map (fun x => (false, x))) :=
  by
    simp [once, applySRReduction, OnceRed]
    exact rfl

noncomputable
def simpleLocalRandomness {A} {I : Type} {s : OracleSpec I} (o : RStateOracle s) (iq : I → Bool) (r : PMF A) (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι)) :=
  { o with queries := {
    impl n args :=
      if not (iq n) then o.queries.impl n args else do
        let a ← r
        f a n args
  }}

lemma simpleLocalRandomnessInitialState {A} {I : Type} {s : OracleSpec I} (o : RStateOracle s) (iq : I → Bool) (r : PMF A) (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι)) :
  (simpleLocalRandomness o iq r f).initialState = o.initialState := rfl

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
def liftL (f : A -> B) : (C × A -> C × B) := fun (a, b) => (a, f b)

def proj {A Y : Type} : A × Y -> Y := fun (_, b) => b

def proj1 {A Y : Type} (x : Bool × (A × Y)) : Bool × Y :=
  let (a, (_b, c)) := x
  (a, c)


lemma t1 {I : Type} {s : OracleSpec I} [∀ n, Inhabited (s.range n)] (iq : I → Bool) (o : RStateOracle s)  : (once iq o).stateType = (Bool × o.stateType) := by
  simp [once, applySRReduction]
  simp [OnceRed]

lemma afterFirstHeavyQuery {I : Type} {s : OracleSpec I} [∀ n, Inhabited (s.range n)] (iq : I → Bool) (o : RStateOracle s) (r : PMF A) (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι)) (queriesl :  List (QueryS s)) (x :  A × o.stateType)
  -- (H : forall (x : QueryS s), x ∈ queriesl -> iq x.index)
  :
  (runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries queriesl (true, x.2) ) =
  (runQueries2Aux (once iq (simpleGlobalRandomness o iq r f)).queries queriesl (true, x)).map (liftL (liftL (proj)))
:= by

  sorry

noncomputable
def initTerm {A} {I : Type} {s : OracleSpec I} (o : RStateOracle s) (r : PMF A)  := (r.bind fun a ↦ o.initialState.bind fun a_1 ↦ PMF.pure (false, a, a_1))

lemma beforeFirstHeavyQuery {I : Type} {s : OracleSpec I} [∀ n, Inhabited (s.range n)] (iq : I → Bool) (o : RStateOracle s) (r : PMF A) (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι)) (queriesl :  List (QueryS s))
  (H : forall x, x ∈ queriesl -> ¬ iq x.index)
  :
  (r.bind fun a ↦ o.initialState.bind fun a_1 ↦ PMF.pure (false, a, a_1)).bind (
      runQueries2Aux (once iq (simpleGlobalRandomness o iq r f)).queries queriesl)
   =
  ((o.initialState.bind fun a_1 ↦ PMF.pure (false, a_1)).bind
      (runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries queriesl)).bind (fun (l, b, s) => do let sr <- r; return (l, b, sr, s))
  := by sorry

-- lemma ObsEqLonger {I : Type} {s : OracleSpec I} (o1 o2 : RStateOracle s) (queries l : List (QueryS s))
--   (H : runQueries o1 (queries++l) = runQueries o2 (queries++l)) :
--   runQueries o1 (queries) = runQueries o2 (queries)
--   := by sorry

def decomp (p : A -> Prop) (l : List A) : (forall x, x ∈ l -> ¬ p x) ⊕' {x // (let (l1, e ,l2) := x; l = l1++(e::l2) /\ p e /\ forall x, x ∈ l1 -> ¬ p x)} := by sorry

lemma decompRunQueries2Aux {O : OracleSpec I} (o : QueryImpl3 O (RState S)) (l p : List (QueryS O)) (x : S): runQueries2Aux o (l++p) x =
  (
  do
    let (out1, s1) <- runQueries2Aux o l x
    let (out2, s2) <- runQueries2Aux o p s1
    return (out1++out2, s2)
  )
 := by sorry

lemma decompRunQueries2Aux2 {O : OracleSpec I} (o : QueryImpl3 O (RState S)) (l p : List (QueryS O)) (xd : PMF S): xd.bind (runQueries2Aux o (l++p)) =
  (
  (xd.bind (fun x => runQueries2Aux o l x)).bind (fun (out1, s1) =>
  do
    let (out2, s2) <- runQueries2Aux o p s1
    return (out1++out2, s2)
  ))
 := by
  conv =>
    lhs
    arg 2
    ext xd
    rw [decompRunQueries2Aux]
  simp []

lemma flagLowered {I : Type} {s : OracleSpec I} [∀ n, Inhabited (s.range n)] (iq : I → Bool) (o : RStateOracle s) (r : PMF A) (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι)) (queriesl :  List (QueryS s)) (b: List (QueryResult s) × Bool × o.stateType) (tm : o.stateType)
: b ∈ (runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries queriesl (false, tm)).support -> b.2.1 = false :=
by
  induction queriesl
  case nil =>
    have H2 : runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries [] (false, tm) = PMF.pure ([], (false, tm)) :=
      by
        simp [runQueries2Aux]
    simp [H2]
    intro H
    simp [H]
  case cons a1 b1 =>
    intro H
    sorry

theorem OnceRedSimpleRandomnesGlobalLocalObsEq {I : Type} {s : OracleSpec I} [∀ n, Inhabited (s.range n)] (iq : I → Bool) (o : RStateOracle s) (r : PMF A) (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι)):
  ObsEq
    (once iq (simpleLocalRandomness o iq r f))
    (once iq (simpleGlobalRandomness o iq r f)) := by
  simp [ObsEq]
  intro queries
  rw [runQueriesEquiv]
  rw [runQueriesEquiv]
  simp [runQueries2]
  conv =>
    rhs
    arg 2
    arg 1
    simp [simpleGlobalRandomness, once, applySRReduction, OnceRed]
  cases (decomp (fun x => iq x.index) queries)
  case inl X =>
    rw [beforeFirstHeavyQuery iq o r f queries (by assumption)]
    simp []
    conv =>
      lhs
      arg 2
      arg 1
      simp [once]
      simp [applySRReduction, OnceRed, simpleLocalRandomness]
    simp []
    simp [PMF.map]
    rfl
  case inr a =>
    let ⟨(l1, e, l2), P⟩ := a
    simp [] at P
    clear a
    rw [P.1]
    rw [decompRunQueries2Aux2]
    rw [decompRunQueries2Aux2]
    conv =>
      rhs
      arg 2
      arg 1
      -- rw [beforeFirstHeavyQuery iq o r f l1] does not work, even when terms seems equal. why?
      arg 2
      change runQueries2Aux (once iq (simpleGlobalRandomness o iq r f)).queries l1
    rw [beforeFirstHeavyQuery iq o r f l1 (by
        intro x Hx
        simp []
        apply P.2.2
        assumption)]
    simp [onceInitialState, simpleLocalRandomnessInitialState]
    simp [PMF.map_bind]
    congr
    ext1 tm
    rw [<-PMF.bindOnSupport_eq_bind]
    conv =>
      rhs
      rw [<-PMF.bindOnSupport_eq_bind]
    congr
    ext1 b
    ext1 Hb
    have stateFalse : b.2.1 = false := by
      apply flagLowered _ _ _ _ _ _ _ Hb
    simp [runQueries2Aux]
    simp [StateT.run]
    conv =>
      lhs
      arg 1
      simp [once]
      simp [applySRReduction]
      simp [query_impl_convert]
      simp [OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, RState.modify, OnceRed, simpleLocalRandomness, get, P.2.1]
      simp [StateT.run, get ,getThe, set, MonadStateOf.get, Functor.map, StateT.map, StateT.get, StateT.set]
      simp [stateFalse]

    conv =>
      rhs
      arg 2
      intro a
      arg 1
      simp [once]
      simp [applySRReduction]
      simp [query_impl_convert]
      simp [OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, RState.modify, OnceRed, simpleGlobalRandomness, get, P.2.1]
      simp [StateT.run, get ,getThe, set, MonadStateOf.get, Functor.map, StateT.map, StateT.get, StateT.set]
      simp [stateFalse]
    simp [RState.runOnSnd, get, getThe, MonadStateOf.get, StateT.get, RState.run, StateT.run, liftM, MonadLift.monadLift, monadLift, StateT.lift]
    congr
    ext1 rs
    congr
    ext1 a
    simp [Functor.map, StateT.set, StateT.map]

    rw [afterFirstHeavyQuery iq o r f l2 (rs, a.2)]
    simp [PMF.map, liftL]
    rfl
