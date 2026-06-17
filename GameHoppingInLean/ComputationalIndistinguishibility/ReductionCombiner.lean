import GameHoppingInLean.OracleReductions
import GameHoppingInLean.ComputationalIndistinguishibility.EmptyTypes
import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.ComputationalIndistinguishibility.AdversaryAdvantage
import GameHoppingInLean.ComputationalIndistinguishibility.ObsEqComp


noncomputable def addToStateL {I : Type u} {O : OracleSpec I} {s1 t : Type}
  (s2 : Type) [Ns1 : Nonempty s1]
  (x : OracleReduction.SRReductionComp O s1 t)
  : OracleReduction.SRReductionComp O (s1 ⊕ s2) t :=
  match x with
  | .roll query cont =>
    do
      let queryRes <- (do
        match h : query with
        | .oracle q =>
          let res <- orQuery(q)
          return (h ▸ res)
        | .sample d =>
          let res <- orSample(d)
          return (h ▸ res)
        | .getState =>
          let state <- orGet!
          let v1 := state.getLeft?.getD (Classical.choice Ns1)
          return (h ▸ v1)
        | .setState x =>
          let _ <- orSet(Sum.inl x)
          return (h ▸ ())
      )
      let res := cont queryRes
      addToStateL s2 res
  | .pure val =>
    pure val

lemma addToStateL_spec {J : Type} {O : OracleSpec J} {s1 s2 : Type}
  [Ns1 : Nonempty s1] (output : Type)
  (comp : OracleComp (withPMFAndStateSpec s1 O) output)
  (impl_state : Type _) (impl : QueryImpl O (RState impl_state)) :
  forall (st: s1 × impl_state),
  (simulateQ (OracleReduction.liftWithPMFAndState impl s1) comp st).map
    (mapSecond fun x ↦ (Sum.inl x.1, x.2)) =
  simulateQ (OracleReduction.liftWithPMFAndState impl (s1 ⊕ s2)) (addToStateL s2 comp) (Sum.inl st.1, st.2)
  := by
    induction comp
    case pure =>
      intro st
      rw [addToStateL.eq_def]
      simp [simulateQ, PFunctor.FreeM.mapM]
      -- rfl
    case roll query cont Hind =>
      intro st
      conv =>
        rhs
        arg 2
        rw [addToStateL.eq_def]
      simp [simulateQ, PFunctor.FreeM.mapM, OracleReduction.liftWithPMFAndState]
      simp [PMF.map_bind, StateT.run]
      simp [simulateQ] at Hind
      simp_rw [Hind]
      cases query <;> (
        simp []
        simp [withPMFAndStateSpec, StateT.bind, StateT.get, RState.modify,
          PMF.map_bind, StateT.run]
        try simp [OracleReduction.query, OracleReduction.sample, OracleReduction.get,
          liftM, monadLift, MonadLift.monadLift, PFunctor.FreeM.lift]
        )
      case oracle =>
        simp [OracleSpec.query, OracleReduction.liftWithPMFAndState]
        simp [withPMFAndStateSpec, StateT.bind, StateT.get, RState.modify,
          PMF.map_bind, StateT.run, set, StateT.set, Functor.map, StateT.map, PMF.map]
      case sample =>
        simp [OracleSpec.query, OracleReduction.liftWithPMFAndState]
        simp [withPMFAndStateSpec, StateT.bind, StateT.get, RState.modify,
          PMF.map_bind, StateT.run, set, StateT.set, Functor.map, StateT.map, PMF.map, Function.comp]
        unfold Function.comp
        simp []
      case getState =>
        simp [OracleSpec.query, OracleReduction.liftWithPMFAndState]
        simp [withPMFAndStateSpec, StateT.bind, StateT.get, RState.modify,
          PMF.map_bind, StateT.run, set, StateT.set, Functor.map, StateT.map, PMF.map, Function.comp]
      case setState =>
        simp [OracleReduction.set, liftM, monadLift, MonadLift.monadLift, PFunctor.FreeM.lift]
        simp [OracleSpec.query, OracleReduction.liftWithPMFAndState]


noncomputable def addToStateR {I : Type u} {O : OracleSpec I} {s1 t : Type}
  (s2 : Type) [Ns1 : Nonempty s1]
  (x : OracleReduction.SRReductionComp O s1 t)
  : OracleReduction.SRReductionComp O (s2 ⊕ s1) t :=
  match x with
  | .roll query cont =>
    do
      let queryRes <- (do
        match h : query with
        | .oracle q =>
          let res <- orQuery(q)
          return (h ▸ res)
        | .sample d =>
          let res <- orSample(d)
          return (h ▸ res)
        | .getState =>
          let state <- orGet!
          let v1 := state.getRight?.getD (Classical.choice Ns1)
          return (h ▸ v1)
        | .setState x =>
          let _ <- orSet(Sum.inr x)
          return (h ▸ ())
      )
      let res := cont queryRes
      addToStateR s2 res
  | .pure val =>
    pure val


lemma addToStateR_spec {J : Type} {O : OracleSpec J} {s1 s2 : Type}
  [Ns1 : Nonempty s1] (output : Type)
  (comp : OracleComp (withPMFAndStateSpec s1 O) output)
  (impl_state : Type _) (impl : QueryImpl O (RState impl_state)) :
  forall (st: s1 × impl_state),
  (simulateQ (OracleReduction.liftWithPMFAndState impl s1) comp st).map
    (mapSecond fun x ↦ (Sum.inr x.1, x.2)) =
  simulateQ (OracleReduction.liftWithPMFAndState impl (s2 ⊕ s1)) (addToStateR s2 comp) (Sum.inr st.1, st.2)
  := by
    induction comp
    case pure =>
      intro st
      rw [addToStateR.eq_def]
      simp [simulateQ, PFunctor.FreeM.mapM]
      -- rfl
    case roll query cont Hind =>
      intro st
      conv =>
        rhs
        arg 2
        rw [addToStateR.eq_def]
      simp [simulateQ, PFunctor.FreeM.mapM, OracleReduction.liftWithPMFAndState]
      simp [PMF.map_bind, StateT.run]
      simp [simulateQ] at Hind
      simp_rw [Hind]
      cases query <;> (
        simp []
        simp [withPMFAndStateSpec, StateT.bind, StateT.get, RState.modify,
          PMF.map_bind, StateT.run]
        try simp [OracleReduction.query, OracleReduction.sample, OracleReduction.get,
          liftM, monadLift, MonadLift.monadLift, PFunctor.FreeM.lift]
        )
      case oracle =>
        simp [OracleSpec.query, OracleReduction.liftWithPMFAndState]
        simp [withPMFAndStateSpec, StateT.bind, StateT.get, RState.modify,
          PMF.map_bind, StateT.run, set, StateT.set, Functor.map, StateT.map, PMF.map]
      case sample =>
        simp [OracleSpec.query, OracleReduction.liftWithPMFAndState]
        simp [withPMFAndStateSpec, StateT.bind, StateT.get, RState.modify,
          PMF.map_bind, StateT.run, set, StateT.set, Functor.map, StateT.map, PMF.map, Function.comp]
        unfold Function.comp
        simp []
      case getState =>
        simp [OracleSpec.query, OracleReduction.liftWithPMFAndState]
        simp [withPMFAndStateSpec, StateT.bind, StateT.get, RState.modify,
          PMF.map_bind, StateT.run, set, StateT.set, Functor.map, StateT.map, PMF.map, Function.comp]
      case setState =>
        simp [OracleReduction.set, liftM, monadLift, MonadLift.monadLift, PFunctor.FreeM.lift]
        simp [OracleSpec.query, OracleReduction.liftWithPMFAndState]


noncomputable def reductionStateInclusion {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (r : OracleReduction O1 O2) (T : Type)
  [Nonempty r.stateType]
  : OracleReduction O1 O2 :=
  {
    stateType := r.stateType ⊕ T
    initialState := do
      let init <- r.initialState
      return Sum.inl init
    queries := fun q => (do
      addToStateL _ (r.queries q)
    )
  }

lemma reductionStateInclusion_spec {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (r : OracleReduction O1 O2) (T : Type)
  [Nonempty r.stateType]
  (impl : RStateOracle O1) :
  ObsEq (r.apply impl) ((reductionStateInclusion r T).apply impl) := by
  simp [OracleReduction.apply]
  simp [reductionStateInclusion]
  apply correctAbstractionImpliesObsEq _ _ (fun x => by exact ((Sum.inl x.1), x.2))
  constructor
  · simp [PMF.map, Functor.map]
  · intro query
    simp []
    ext1 st
    simp [mapInputState, mapOutputState, mapSecond, PMF.map, StateT.run, Function.comp, PMF.pure]
    apply addToStateL_spec


noncomputable def reductionCombinerMiniL_nontrivial {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (x1 x2 : (OracleReduction O1 O2))
  [Nonempty x2.stateType] [Nonempty x1.stateType]
  : (OracleReduction O1 O2)
  :=
  {
    stateType := (x1.stateType ⊕ x2.stateType)
    initialState := (do
     let init <- x1.initialState
      return Sum.inl init
    )
    queries := fun q => (do
        let x <- orGet!
        match x with
        | Sum.inl _s =>
          addToStateL _ (x1.queries q)
        | Sum.inr _s =>
          addToStateR _ (x2.queries q)
      )
  }

lemma reductionStateInclusionMiniL_spec {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (x1 x2 : (OracleReduction O1 O2))
  [Nonempty x2.stateType] [Nonempty x1.stateType]
  (impl : RStateOracle O1) :
  ObsEq (x1.apply impl) ((reductionCombinerMiniL_nontrivial x1 x2).apply impl) := by
  simp [OracleReduction.apply]
  simp [reductionCombinerMiniL_nontrivial]
  apply correctAbstractionImpliesObsEq _ _ (fun x => by exact ((Sum.inl x.1), x.2))
  constructor
  · simp [PMF.map, Functor.map]
  · intro query
    simp []
    ext1 st
    simp [mapInputState, mapOutputState, mapSecond, StateT.run, Function.comp, PMF.pure, simulateQ]
    simp [StateT.bind, bind, OracleSpec.query]
    simp [withPMFAndStateI.getState, OracleReduction.liftWithPMFAndState, StateT.get, Functor.map, StateT.map]
    rw [<-simulateQ.eq_def]
    rw [addToStateL_spec]
    simp [simulateQ]

noncomputable def reductionCombinerMiniR_nontrivial {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (x1 x2 : (OracleReduction O1 O2))
  [Nonempty x2.stateType] [Nonempty x1.stateType]
  :  (OracleReduction O1 O2)
  :=
  {
    stateType := (x1.stateType ⊕ x2.stateType)
    initialState := (do
     let init <- x2.initialState
      return Sum.inr init
    )
    queries := fun q => (do
        let x <- orGet!
        match x with
        | Sum.inl _s =>
          addToStateL _ (x1.queries q)
        | Sum.inr _s =>
          addToStateR _ (x2.queries q)
      )
  }

lemma reductionStateInclusionMiniR_spec {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (x1 x2 : (OracleReduction O1 O2))
  [Nonempty x2.stateType] [Nonempty x1.stateType]
  (impl : RStateOracle O1) :
  ObsEq (x2.apply impl) ((reductionCombinerMiniR_nontrivial x1 x2).apply impl) := by
  simp [OracleReduction.apply]
  simp [reductionCombinerMiniR_nontrivial]
  apply correctAbstractionImpliesObsEq _ _ (fun x => by exact ((Sum.inr x.1), x.2))
  constructor
  · simp [PMF.map, Functor.map]
  · intro query
    simp []
    ext1 st
    simp [mapInputState, mapOutputState, mapSecond, StateT.run, Function.comp, PMF.pure, simulateQ]
    simp [StateT.bind, bind, OracleSpec.query]
    simp [withPMFAndStateI.getState, OracleReduction.liftWithPMFAndState, StateT.get, Functor.map, StateT.map]
    rw [<-simulateQ.eq_def]
    rw [addToStateR_spec]
    simp [simulateQ]

def reductionStateInclusionMiniR_spec2 {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (x1 x2 : (OracleReduction O1 O2))
  [Nonempty x2.stateType] [Nonempty x1.stateType]
  (impl : RStateOracle O1) :
  forall dist,
  runDinstinguisher dist ((reductionCombinerMiniR_nontrivial x1 x2).apply impl) =
  runDinstinguisher dist (x2.apply impl)
:=
by
  intro dist
  apply obsEq_distinquishing_ub
  apply ObsEqSymm
  apply reductionStateInclusionMiniR_spec

def reductionStateInclusionMiniL_spec2 {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (x1 x2 : (OracleReduction O1 O2))
  [Nonempty x2.stateType] [Nonempty x1.stateType]
  (impl : RStateOracle O1) :
  forall dist,
  runDinstinguisher dist ((reductionCombinerMiniL_nontrivial x1 x2).apply impl) =
  runDinstinguisher dist (x1.apply impl)
:= by
  intro dist
  apply obsEq_distinquishing_ub
  apply ObsEqSymm
  apply reductionStateInclusionMiniL_spec


noncomputable def bernulli_ratio (a b : ℕ) : PMF Bool :=
  PMF.bernoulli (a/(a+b)) (
        by
          have H : a <= a + b :=  by
            exact Nat.le_add_right a b
          refine NNReal.div_le_of_le_mul ?_
          simp
          )


noncomputable def reductionCombiner_nontrivial {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (x1 x2 : ℕ × (OracleReduction O1 O2))
  [Nonempty x2.2.stateType] [Nonempty x1.2.stateType]
  : ℕ × (OracleReduction O1 O2)
  :=
  (x1.1+x2.1, {
    stateType := (x1.2.stateType ⊕ x2.2.stateType)
    initialState := (do
      let x : Bool <- OracleReduction.initSample (bernulli_ratio x1.1 x2.1)
      if x then
        let init <- x1.2.initialState
        return Sum.inl init
      else
        let init <- x2.2.initialState
        return Sum.inr init
    )
    queries := fun q => (do
        let x <- orGet!
        match x with
        | Sum.inl _s =>
          addToStateL _ (x1.2.queries q)
        | Sum.inr _s =>
          addToStateR _ (x2.2.queries q)
      )
  })

-- TODO: fomrulate lemma, that reductionCombiner_nontrivial.2 is eqivalnet to running 'do


noncomputable def weightedCases (r : PMF Bool) (x1 x2 : PMF X) : PMF X :=
  (do
    let z : Bool <- r
    if z then x1 else x2
  )


lemma reductionOfIf {X : Type _} (r : PMF Bool) (x1 x2 : PMF X) (t : X) :
  getPMF (weightedCases r x1 x2) t = (getPMF r true) * getPMF x1 t + ((getPMF r false))*getPMF x2 t := by
  simp only [getPMF, weightedCases, bind, PMF.bind_apply, tsum_bool]
  simp only [Bool.false_eq_true, reduceIte, if_true]
  rw [ENNReal.toNNReal_add, ENNReal.toNNReal_mul, ENNReal.toNNReal_mul, add_comm]
  · exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  · exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

lemma getBernulli (x : NNReal) (Hx : x <= 1) : getPMF (PMF.bernoulli x Hx) true = x := by
  simp [getPMF, PMF.bernoulli_apply]
lemma getBernullif (x : NNReal) (Hx : x <= 1) : getPMF (PMF.bernoulli x Hx) false = 1-x := by
  simp [getPMF, PMF.bernoulli_apply]

lemma getBernullir (x1 x2 : ℕ) : getPMF (bernulli_ratio x1 x2) true = x1/(x1+x2) := by
  simp [bernulli_ratio, getBernulli]
lemma getBernullir2 (x1 x2 : ℕ) (H : x1 + x2 >= 1) : getPMF (bernulli_ratio x1 x2) false = x2/(x1+x2) := by
  simp only [bernulli_ratio, getBernullif]
  have hne : (x1 : NNReal) + x2 ≠ 0 := by
    have : (1:NNReal) ≤ (x1:NNReal) + x2 := by exact_mod_cast H
    intro h; rw [h] at this; simp at this
  rw [show (1:NNReal) = ((x1:NNReal)+x2)/((x1:NNReal)+x2) from (div_self hne).symm,
      ← NNReal.sub_div, add_tsub_cancel_left]


lemma reductionCombiner_initialState_split {I : Type} {O : OracleSpec I} {I1 : Type} {O1 : OracleSpec I1}
  (impl : RStateOracle O1)
  (x1 x2 : ℕ × (OracleReduction O1 O))
  [Nonempty x2.2.stateType] [Nonempty x1.2.stateType] :
  ((reductionCombiner_nontrivial x1 x2).2.apply impl).initialState =
  (bernulli_ratio x1.1 x2.1) >>= fun b =>
    if b then ((reductionCombinerMiniL_nontrivial x1.2 x2.2).apply impl).initialState
    else ((reductionCombinerMiniR_nontrivial x1.2 x2.2).apply impl).initialState := by
  simp only [OracleReduction.apply, reductionCombiner_nontrivial,
    reductionCombinerMiniL_nontrivial, reductionCombinerMiniR_nontrivial,
    OracleReduction.initSample]
  simp only [OracleSpec.query, simulateQ_query_bind, addPMFtoImpl,
    OracleQuery.cont, OracleQuery.query]
  simp only [liftM_self, id_eq, StateTSimps]
  simp only [bind, StateT.bind, StateT.lift, liftM, monadLift, MonadLift.monadLift,
    StateTSimps, PMF.map_bind, PMF.pure_bind, PMF.bind_bind, Functor.map]
  have hpb : ∀ {β γ : Type} (a : β) (f : β → PMF γ), (pure a : PMF β).bind f = f a :=
    fun a f => by rw [show (pure a : PMF _) = PMF.pure a from rfl, PMF.pure_bind]
  simp only [hpb]
  rw [PMF.bind_comm impl.initialState (bernulli_ratio x1.1 x2.1)]
  congr 1
  ext b
  cases b <;> simp only [Bool.false_eq_true, reduceIte, if_true]

lemma reductionCombinerCorrect_nontrivial_helper {I : Type} {O : OracleSpec I} {I1 : Type} {O1 : OracleSpec I1}
  (dist : OracleComp (withPMFSpec O) Bool)
  (impl : RStateOracle O1)
  (x1 x2 : ℕ × (OracleReduction O1 O))
  [Nonempty x2.2.stateType] [Nonempty x1.2.stateType] :
  runDinstinguisher dist ((reductionCombiner_nontrivial x1 x2).2.apply impl) =
  (weightedCases (bernulli_ratio x1.1 x2.1)
    (runDinstinguisher dist ((reductionCombinerMiniL_nontrivial x1.2 x2.2).apply impl))
    (runDinstinguisher dist ((reductionCombinerMiniR_nontrivial x1.2 x2.2).apply impl))
  )
:= by
  unfold weightedCases
  rw [runDinstinguisher2inner dist ((reductionCombiner_nontrivial x1 x2).2.apply impl),
      runDinstinguisher2inner dist ((reductionCombinerMiniL_nontrivial x1.2 x2.2).apply impl),
      runDinstinguisher2inner dist ((reductionCombinerMiniR_nontrivial x1.2 x2.2).apply impl)]
  rw [reductionCombiner_initialState_split]
  have hqL : ((reductionCombiner_nontrivial x1 x2).2.apply impl).queries
      = ((reductionCombinerMiniL_nontrivial x1.2 x2.2).apply impl).queries := by
    funext i
    simp only [reductionCombiner_nontrivial, reductionCombinerMiniL_nontrivial,
      OracleReduction.apply]
    congr 1
    congr 1
    funext x
    cases x <;> rfl
  have hqR : ((reductionCombiner_nontrivial x1 x2).2.apply impl).queries
      = ((reductionCombinerMiniR_nontrivial x1.2 x2.2).apply impl).queries := by
    funext i
    simp only [reductionCombiner_nontrivial, reductionCombinerMiniR_nontrivial,
      OracleReduction.apply]
    congr 1
    congr 1
    funext x
    cases x <;> rfl
  rw [bind_assoc]
  congr 1
  funext b
  cases b <;> simp only [Bool.false_eq_true, reduceIte, if_true]
  · rw [hqR]
    rfl
  · rw [hqL]
    rfl

lemma reductionCombinerCorrect_nontrivial {I : Type} {O : OracleSpec I}
  (dist : OracleComp (withPMFSpec O) Bool)
  (assumption : SingleAssumption)
  (x1 x2 : ℕ × (OracleReduction assumption.O O))
  [Nonempty x2.2.stateType] [Nonempty x1.2.stateType]
  (Hneq : x1.1 >= 1 ∧ x2.1 >= 1)
  : ascToReal dist assumption x1 + ascToReal dist assumption x2 =
  ascToReal dist assumption (reductionCombiner_nontrivial x1 x2) :=
by
  simp [ascToReal]
  nth_rw 1 [reductionCombiner_nontrivial]
  simp []
  simp [advantage]
  repeat rw [<-goodDoubleAction]
  conv =>
    rhs
    simp [reductionCombinerCorrect_nontrivial_helper]
  simp [pdistancePMF]
  simp [reductionOfIf _ _ _ true]
  simp [getBernullir, getBernullir2 x1.1 x2.1 (by
    refine Nat.le_add_right_of_le ?_
    · apply Hneq.1
    )]
  simp [reductionStateInclusionMiniR_spec2]
  simp [reductionStateInclusionMiniL_spec2]
  generalize (getPMF (runDinstinguisher dist (x1.2.apply assumption.i.1)) true).toReal = l1
  generalize (getPMF (runDinstinguisher dist (x1.2.apply assumption.i.2)) true).toReal = l2
  generalize (getPMF (runDinstinguisher dist (x2.2.apply assumption.i.1)) true).toReal = z1
  generalize (getPMF (runDinstinguisher dist (x2.2.apply assumption.i.2)) true).toReal = z2
  grind

noncomputable def reductionCombiner {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (x1 x2 : ℕ × (OracleReduction O1 O2))
  : ℕ × (OracleReduction O1 O2)
  :=
  open Classical in
  if HO1 : forall x : I1, Nonempty (O1 x) then
    have x1NoEmpty := oracleCompToObject _ (implementableWihtPMF _ HO1) x1.2.initialState
    have x2NoEmpty := oracleCompToObject _ (implementableWihtPMF _ HO1) x2.2.initialState
    reductionCombiner_nontrivial x1 x2
  else by
    simp at HO1
    have Hx := Classical.choose_spec HO1
    constructor
    · exact 0
    · exact {
        stateType := Unit,
        initialState := pure (),
        queries := fun input =>
          do
            let y <- orQuery(Classical.choose HO1)
            by
              exfalso
              exact IsEmpty.false y
        }

lemma reductionCombinerCorrect {I : Type} {O : OracleSpec I}
  (dist : OracleComp (withPMFSpec O) Bool)
  (assumption : SingleAssumption)
  (x1 x2 : ℕ × (OracleReduction assumption.O O))
  (Hneq : x1.1 >= 1 ∧ x2.1 >= 1)
  : ascToReal dist assumption x1 + ascToReal dist assumption x2 =
  ascToReal dist assumption (reductionCombiner x1 x2) :=
  by
    have H := non_trivial_spec assumption.i.1
    simp [reductionCombiner]
    simp [H]
    have x1NoEmpty := oracleCompToObject _ (implementableWihtPMF _ H) x1.2.initialState
    have x2NoEmpty := oracleCompToObject _ (implementableWihtPMF _ H) x2.2.initialState
    apply reductionCombinerCorrect_nontrivial
    apply Hneq
