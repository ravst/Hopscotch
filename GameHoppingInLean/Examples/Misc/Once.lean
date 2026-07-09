import GameHoppingInLean.Comp.StatefulRandomOracle
import GameHoppingInLean.Comp.OracleReductions
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

set_option maxHeartbeats 1000000 in
lemma afterFirstHeavyQuery {I : Type} {s : OracleSpec I} [∀ n, Inhabited (s.range n)] (iq : I → Bool) (o : RStateOracle s) (r : PMF A) (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι)) (queriesl :  List (QueryS s)) (x :  A × o.stateType)
  -- (H : forall (x : QueryS s), x ∈ queriesl -> iq x.index)
  :
  (RStateOracle.runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries queriesl (true, x.2) ) =
  (RStateOracle.runQueries2Aux (once iq (simpleGlobalRandomness o iq r f)).queries queriesl (true, x)).map (liftL (liftL (proj)))
:= by
  induction queriesl generalizing x with
  | nil =>
      simp [RStateOracle.runQueries2Aux, PMF.map, liftL, proj]
  | cons q qs ih =>
      by_cases hq : iq q.index = false
      · simp [RStateOracle.runQueries2Aux, hq, once, applySRReduction, OnceRed, simpleLocalRandomness,
          simpleGlobalRandomness, query_impl_convert, OracleComp.simulateQ, FreeMonad.mapM,
          FreeMonad.lift, RState.modify, PMF.map_bind, PMF.bind_map, bind_assoc,
          Function.comp, liftL, proj]
        refine bind_congr (x := StateT.run (o.queries.impl q.index q.input) x.2) ?_
        intro a
        have hrec := ih (x := (x.1, a.2))
        have hrec' := congrArg (fun z =>
            z.bind (fun __discr =>
              PMF.pure ({ index := q.index, output := a.1 } :: __discr.1, __discr.2))) hrec
        simpa [once, applySRReduction, OnceRed, simpleLocalRandomness, simpleGlobalRandomness,
          query_impl_convert, OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, RState.modify,
          PMF.bind_map, Function.comp, liftL, proj] using hrec'
      ·
        have hqTrue : iq q.index = true := by
          cases h : iq q.index <;> simp [h] at hq ⊢
        simp [RStateOracle.runQueries2Aux, hqTrue]
        rw [PMF.map_bind]
        simp [once, applySRReduction, OnceRed, simpleLocalRandomness, simpleGlobalRandomness, hqTrue,
          query_impl_convert, OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, RState.modify]
        have hrec := ih (x := x)
        have hrec' := congrArg (fun z =>
            z.bind (fun __discr =>
              PMF.pure ({ index := q.index, output := default } :: __discr.1, __discr.2))) hrec
        rw [PMF.map_bind]
        simpa [once, applySRReduction, OnceRed, simpleLocalRandomness, simpleGlobalRandomness,
          query_impl_convert, OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, RState.modify,
          PMF.bind_map, Function.comp, liftL, proj] using hrec'

noncomputable
def initTerm {A} {I : Type} {s : OracleSpec I} (o : RStateOracle s) (r : PMF A)  := (r.bind fun a ↦ o.initialState.bind fun a_1 ↦ PMF.pure (false, a, a_1))

lemma beforeFirstHeavyQuery {I : Type} {s : OracleSpec I} [∀ n, Inhabited (s.range n)] (iq : I → Bool) (o : RStateOracle s) (r : PMF A) (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι)) (queriesl :  List (QueryS s))
  (H : forall x, x ∈ queriesl -> iq x.index = false)
  :
  (r.bind fun a ↦ o.initialState.bind fun a_1 ↦ PMF.pure (false, a, a_1)).bind (
      RStateOracle.runQueries2Aux (once iq (simpleGlobalRandomness o iq r f)).queries queriesl)
   =
  ((o.initialState.bind fun a_1 ↦ PMF.pure (false, a_1)).bind
      (RStateOracle.runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries queriesl)).bind (fun (l, b, s) => do let sr <- r; return (l, b, sr, s))
  := by
    let insA : A → (List (QueryResult s) × Bool × o.stateType) →
        (List (QueryResult s) × Bool × A × o.stateType) :=
      fun a z => (z.1, z.2.1, a, z.2.2)
    have hAux :
        ∀ (qs : List (QueryS s)) (Hqs : ∀ x ∈ qs, iq x.index = false) (a : A) (st : o.stateType),
          RStateOracle.runQueries2Aux (once iq (simpleGlobalRandomness o iq r f)).queries qs (false, a, st) =
            (RStateOracle.runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries qs (false, st)).map
              (insA a) := by
      intro qs Hqs a st
      induction qs generalizing st with
      | nil =>
          simp [RStateOracle.runQueries2Aux, insA]
      | cons q qs ih =>
          have hq : iq q.index = false := Hqs q (by simp)
          have htail : ∀ x ∈ qs, iq x.index = false := by
            intro x hx
            exact Hqs x (by simp [hx])
          simp [RStateOracle.runQueries2Aux, once, applySRReduction, OnceRed, simpleLocalRandomness,
            simpleGlobalRandomness, query_impl_convert, OracleComp.simulateQ, FreeMonad.mapM,
            FreeMonad.lift, RState.modify, hq, PMF.map_bind, PMF.bind_map,
            Function.comp]
          refine bind_congr (x := StateT.run (o.queries.impl q.index q.input) st) ?_
          intro a_1
          have hrec := ih htail a_1.2
          have hrec' := congrArg (fun z =>
              z.bind (fun __discr =>
                PMF.pure ({ index := q.index, output := a_1.1 } :: __discr.1, __discr.2))) hrec
          simpa [once, applySRReduction, OnceRed, simpleLocalRandomness, simpleGlobalRandomness,
            query_impl_convert, OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, RState.modify,
            PMF.bind_map, Function.comp, insA] using hrec'
    calc
      (r.bind fun a ↦ o.initialState.bind fun a_1 ↦ PMF.pure (false, a, a_1)).bind
          (RStateOracle.runQueries2Aux (once iq (simpleGlobalRandomness o iq r f)).queries queriesl)
          =
        r.bind (fun a => o.initialState.bind fun st =>
          RStateOracle.runQueries2Aux (once iq (simpleGlobalRandomness o iq r f)).queries queriesl (false, a, st)) := by
            simp [PMF.bind_bind]
      _ =
        r.bind (fun a => o.initialState.bind fun st =>
          (RStateOracle.runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries queriesl (false, st)).map
            (insA a)) := by
              refine bind_congr (x := r) ?_
              intro a
              refine bind_congr (x := o.initialState) ?_
              intro st
              simpa using hAux queriesl H a st
      _ =
        r.bind (fun a =>
          (o.initialState.bind fun st =>
            RStateOracle.runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries queriesl (false, st)).bind
              (PMF.pure ∘ insA a)) := by
                simp [PMF.bind_bind, PMF.map]
      _ =
        (o.initialState.bind fun st =>
          RStateOracle.runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries queriesl (false, st)).bind
            (fun z => r.bind fun sr => PMF.pure (insA sr z)) := by
              simpa using
                (PMF.bind_comm r
                  (o.initialState.bind fun st =>
                    RStateOracle.runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries queriesl (false, st))
                  (fun a z => PMF.pure (insA a z)))
      _ =
        ((o.initialState.bind fun a_1 ↦ PMF.pure (false, a_1)).bind
          (RStateOracle.runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries queriesl)).bind
            (fun (l, b, s) => do let sr <- r; return (l, b, sr, s)) := by
              simp [PMF.bind_bind, insA]
              rfl

-- lemma ObsEqLonger {I : Type} {s : OracleSpec I} (o1 o2 : RStateOracle s) (queries l : List (QueryS s))
--   (H : runQueries o1 (queries++l) = runQueries o2 (queries++l)) :
--   runQueries o1 (queries) = runQueries o2 (queries)
--   := by sorry

noncomputable def decomp (p : A -> Prop) (l : List A) :
    (forall x, x ∈ l -> ¬ p x) ⊕'
      {x // (let (l1, e ,l2) := x; l = l1++(e::l2) /\ p e /\ forall x, x ∈ l1 -> ¬ p x)} :=
  by
  classical
  induction l with
  | nil =>
      exact PSum.inl (by intro x hx; cases hx)
  | cons e l ih =>
      by_cases he : p e
      · exact PSum.inr ⟨([], e, l), by simp [he]⟩
      · cases ih with
        | inl hnone =>
            exact PSum.inl (by
              intro x hx
              have hx' : x = e ∨ x ∈ l := by
                simpa using hx
              cases hx' with
              | inl hxEq =>
                  cases hxEq
                  exact he
              | inr hxIn =>
                  exact hnone x hxIn)
        | inr hsplit =>
            refine PSum.inr ?_
            rcases hsplit with ⟨⟨l1, e', l2⟩, hs⟩
            rcases hs with ⟨hsEq, hp, hprefix⟩
            refine ⟨(e :: l1, e', l2), ?_⟩
            refine ⟨?_, hp, ?_⟩
            · simp [hsEq]
            · intro x hx
              have hx' : x = e ∨ x ∈ l1 := by
                simpa using hx
              cases hx' with
              | inl hxEq =>
                  cases hxEq
                  exact he
              | inr hxIn =>
                  exact hprefix x hxIn

lemma decompRStateOracle.runQueries2Aux {O : OracleSpec I} (o : QueryImpl3 O (RState S)) (l p : List (QueryS O)) (x : S): RStateOracle.runQueries2Aux o (l++p) x =
  (
  do
    let (out1, s1) <- RStateOracle.runQueries2Aux o l x
    let (out2, s2) <- RStateOracle.runQueries2Aux o p s1
    return (out1++out2, s2)
  )
 := by
  induction l generalizing x with
  | nil =>
      simp [RStateOracle.runQueries2Aux]
  | cons q qs ih =>
      simp [RStateOracle.runQueries2Aux, ih, bind_assoc]

lemma decompRStateOracle.runQueries2Aux2 {O : OracleSpec I} (o : QueryImpl3 O (RState S)) (l p : List (QueryS O)) (xd : PMF S): xd.bind (RStateOracle.runQueries2Aux o (l++p)) =
  (
  (xd.bind (fun x => RStateOracle.runQueries2Aux o l x)).bind (fun (out1, s1) =>
  do
    let (out2, s2) <- RStateOracle.runQueries2Aux o p s1
    return (out1++out2, s2)
  ))
 := by
  conv =>
    lhs
    arg 2
    ext xd
    rw [decompRStateOracle.runQueries2Aux]
  simp []

lemma flagLowered {I : Type} {s : OracleSpec I} [∀ n, Inhabited (s.range n)] (iq : I → Bool)
    (o : RStateOracle s) (r : PMF A)
    (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι))
    (queriesl :  List (QueryS s))
    (Hn : forall x, x ∈ queriesl -> iq x.index = false)
    (b: List (QueryResult s) × Bool × o.stateType) (tm : o.stateType)
: b ∈ (RStateOracle.runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries queriesl (false, tm)).support ->
    b.2.1 = false :=
by
  revert Hn b tm
  induction queriesl with
  | nil =>
      intro Hn b tm H
      simp [RStateOracle.runQueries2Aux] at H
      simp [H]
  | cons q qs ih =>
      intro Hn b tm H
      have hq : iq q.index = false := Hn q (by simp)
      have hqs : forall x, x ∈ qs -> iq x.index = false := by
        intro x hx
        exact Hn x (by simp [hx])
      rw [RStateOracle.runQueries2Aux] at H
      rcases (PMF.mem_support_bind_iff _ _ _).1 H with ⟨step, hStep, hTail⟩
      rcases step with ⟨out, bflag, st0⟩
      rcases (PMF.mem_support_bind_iff _ _ _).1 hTail with ⟨tail, hTailRun, hPure⟩
      have hStepFalse : bflag = false := by
        cases hb : bflag with
        | false =>
            rfl
        | true =>
            exfalso
            have hStepMem :
                (out, (true, st0)) ∈
                  (StateT.run ((once iq (simpleLocalRandomness o iq r f)).queries.impl q.index q.input)
                    (false, tm)).support := by
              simpa [hb] using hStep
            have hStepNotMem :
                (out, (true, st0)) ∉
                  (StateT.run ((once iq (simpleLocalRandomness o iq r f)).queries.impl q.index q.input)
                    (false, tm)).support := by
              intro hmem
              have hzero :
                  (StateT.run ((once iq (simpleLocalRandomness o iq r f)).queries.impl q.index q.input)
                    (false, tm)) (out, (true, st0)) = 0 := by
                simp [once, applySRReduction, OnceRed, simpleLocalRandomness, hq, query_impl_convert,
                  OracleComp.simulateQ, FreeMonad.mapM, FreeMonad.lift, RState.modify]
              exact ((PMF.mem_support_iff _ _).1 hmem) hzero
            exact hStepNotMem hStepMem
      have hTailRun' :
          tail ∈ (RStateOracle.runQueries2Aux (once iq (simpleLocalRandomness o iq r f)).queries qs
            (false, st0)).support := by
        simpa [hStepFalse] using hTailRun
      have hTailFalse : tail.2.1 = false := ih hqs tail st0 hTailRun'
      simp at hPure
      subst hPure
      simp [hTailFalse]

set_option maxHeartbeats 1000000 in
theorem OnceRedSimpleRandomnesGlobalLocalObsEq {I : Type} {s : OracleSpec I} [∀ n, Inhabited (s.range n)] (iq : I → Bool) (o : RStateOracle s) (r : PMF A) (f : A → (ι : I) → s.domain ι → RState o.stateType (s.range ι)):
  ObsEq
    (once iq (simpleLocalRandomness o iq r f))
    (once iq (simpleGlobalRandomness o iq r f)) := by
  simp [ObsEq]
  intro queries
  rw [runQueriesEquiv]
  rw [runQueriesEquiv]
  simp [RStateOracle.runQueriesOnlyOut, RStateOracle.runQueries2]
  conv =>
    rhs
    arg 2
    arg 1
    simp [simpleGlobalRandomness, once, applySRReduction, OnceRed]
  cases (decomp (fun x => iq x.index) queries)
  case inl X =>
    rw [beforeFirstHeavyQuery iq o r f queries (by
      intro x hx
      exact Bool.eq_false_iff.mpr (X x hx))]
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
    rw [decompRStateOracle.runQueries2Aux2]
    rw [decompRStateOracle.runQueries2Aux2]
    conv =>
      rhs
      arg 2
      arg 1
      -- rw [beforeFirstHeavyQuery iq o r f l1] does not work, even when terms seems equal. why?
      arg 2
      change RStateOracle.runQueries2Aux (once iq (simpleGlobalRandomness o iq r f)).queries l1
    rw [beforeFirstHeavyQuery iq o r f l1 (by
        intro x Hx
        exact P.2.2 x Hx)]
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
      have hNoHeavy : forall x, x ∈ l1 -> iq x.index = false := by
        intro x hx
        exact P.2.2 x hx
      exact flagLowered (iq := iq) (o := o) (r := r) (f := f) (queriesl := l1)
        hNoHeavy b tm Hb
    simp [RStateOracle.runQueries2Aux]
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

    rw [afterFirstHeavyQuery iq o r f l2 (rs, a.2)]
    simp [PMF.map, liftL]
    rfl
