import GameHoppingInLean.ComputationalIndistinguishibility.ReductionCombiner
import GameHoppingInLean.IndistinguishabilityTactics
import GameHoppingInLean.Comp.OracleReductionsLemmas

structure internal_type {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l : List (OracleReduction O1 O2)) where
  index : Fin (l.length)
  value : l[index].stateType

noncomputable def reduction_combiner_list
  {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l : List (OracleReduction O1 O2))
  (Hl : l.length > 0)
  (He : forall x : I1, Nonempty (O1 x))
  : OracleReduction O1 O2
  :=
  have lNoEmpty (x : Fin l.length) : Nonempty l[x].stateType :=
    oracleCompToObject _ (implementableWihtPMF _ He) l[x].initialState
  {
    stateType := internal_type l
    initialState := (do
      have X : Nonempty (Fin (l.length)) := by
        exists 0
      let x : Fin l.length <- OracleReduction.initSample (PMF.uniformOfFintype (Fin l.length))
      let init <- l[x].initialState
      return {index := x, value :=  init}
    )
    queries q := (do
        let x <- orGet!
        match x with
        | {index := i, value := v} =>
          have H0 := lNoEmpty i
          addToStateG _ (fun x => {index := i, value := x})
            (fun x => if h : x.index = i then some (h ▸ x.value) else none) (l[i].queries q)
      )
  }


noncomputable def reductionCombiner_nontrivial_packed
  {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (x1 x2 : ℕ × (OracleReduction O1 O2))
  -- [Nonempty x2.2.stateType] [Nonempty x1.2.stateType]
  (He : forall x : I1, Nonempty (O1 x))
  : ℕ × (OracleReduction O1 O2)
  :=
  have _x1NoEmpty := reductionNonEmpty x1.2 He
  have _x2NoEmpty := reductionNonEmpty x2.2 He
  reductionCombiner_nontrivial x1 x2


noncomputable def reduction_combiner_list_full
  {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l : {x : List (OracleReduction O1 O2) // x.length > 0})
  : OracleReduction O1 O2 :=
  open Classical in
  if H : forall i, Nonempty (O1 i) then
    reduction_combiner_list l.val l.2 H
  else
    reductionFromEmpty H

noncomputable def combine_red
  {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l : {x : List (OracleReduction O1 O2) // x.length > 0})
  : ℕ × OracleReduction O1 O2 :=
    (l.1.length, reduction_combiner_list_full l)

attribute [local game_hopping_unfold] combine_red reduction_combiner_list_full reduction_combiner_list


noncomputable def combine_red_singleton
  {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l : (OracleReduction O1 O2))
  (H : [l].length > 0)
  (H2 : forall i, Nonempty (O1 i))
  (impl : RStateOracle O1)
  :
  ObsEq
    ((reduction_combiner_list_full ⟨[l], H⟩).apply impl)
    (l.apply impl) := by
    simp [combine_red, reduction_combiner_list_full, H2]
    unfold reduction_combiner_list
    simp [internal_type]
    apply ObsEq.symm
    obs_eq_by_abstraction (fun x =>
      by
        unfold OracleReduction.apply
        unfold OracleReduction.apply at x
        simp at x
        simp []
        exact (
          {
            index := 0,
            value := x.1
          }, x.2)
      )
    · intro query
      ext1 s1
      simp [mapInputState, RStateSimplifier, StateTSimps]
      have X : Nonempty [l][0].stateType := by
        simp [List.get]
        apply reductionNonEmpty
        apply non_trivial_spec impl
      rw [<-addToStateG_spec (Ns1:=X)]
      · simp [mapOutputState, RStateSimplifier, StateTSimps, internal_type, OracleReductionSimps]
        simp [getElem]
      · intro X
        simp []
    · --simp [PMF.uniformOfFintype, PMF.uniformOfFinset, PMF.ofFinset]
      have H : PMF.pure (0 : Fin 1) = PMF.uniformOfFintype (Fin 1) := by
        simp [PMF.pure, PMF.uniformOfFintype, PMF.uniformOfFinset, PMF.ofFinset]
        congr
        funext a
        congr
      rw [<-H]
      simp []

def listCombiner (l1 l2 : {x : List X // x.length > 0}) : {x : List X // x.length > 0} :=
  ⟨l1.1++l2.1, by simp [l1.2, l2.2]⟩


-- a long boring proof.

/-- Forward state abstraction from the "flat" combiner state on `l1 ++ l2`
to the binary combiner state `internal_type l1 ⊕ internal_type l2`. -/
noncomputable def flatToSum {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
    (l1 l2 : List (OracleReduction O1 O2)) :
    internal_type (l1 ++ l2) → internal_type l1 ⊕ internal_type l2 :=
  fun s =>
    if h : (s.index : ℕ) < l1.length then
      Sum.inl { index := ⟨s.index, h⟩,
                value := (List.getElem_append_left (bs := l2) h (h' := s.index.isLt)) ▸ s.value }
    else
      Sum.inr { index := ⟨(s.index : ℕ) - l1.length, by
                  have hi := s.index.isLt
                  simp only [List.length_append] at hi
                  omega⟩,
                value := (List.getElem_append_right (bs := l2) (by omega) (h₂ := s.index.isLt)) ▸ s.value }

/-- The product version of `flatToSum` (identity on the underlying oracle state). -/
noncomputable def flatToSumProd {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
    (l1 l2 : List (OracleReduction O1 O2)) (S : Type) :
    internal_type (l1 ++ l2) × S → (internal_type l1 ⊕ internal_type l2) × S :=
  fun p => (flatToSum l1 l2 p.1, p.2)

/-
Splitting a uniform draw over `Fin (n1 + n2)` as a `bernulli_ratio`-weighted
choice between uniform draws over the two halves.
-/
lemma uniform_fin_add_split {X : Type} (n1 n2 : ℕ) [NeZero n1] [NeZero n2] [NeZero (n1 + n2)]
    (g : Fin (n1 + n2) → PMF X) :
    (PMF.uniformOfFintype (Fin (n1 + n2))).bind g =
      (bernulli_ratio n1 n2).bind (fun b =>
        if b then (PMF.uniformOfFintype (Fin n1)).bind (fun j => g (j.castAdd n2))
        else (PMF.uniformOfFintype (Fin n2)).bind (fun j => g (j.natAdd n1))) := by
  ext x;
  simp +decide [ PMF.bind_apply, PMF.uniformOfFintype_apply, bernulli_ratio ];
  simp +decide [ div_eq_mul_inv, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib, Finset.sum_mul, Nat.cast_add, Nat.cast_one, NeZero.ne ];
  rw [ show ( 1 - ( n1 : ENNReal ) * ( n1 + n2 : ENNReal ) ⁻¹ ) = ( n2 : ENNReal ) * ( n1 + n2 : ENNReal ) ⁻¹ from ?_ ];
  · simp +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, NeZero.ne ];
    rw [ show ( ∑ i : Fin ( n1 + n2 ), ( g i ) x ) = ( ∑ i : Fin n1, ( g ( Fin.castAdd n2 i ) ) x ) + ( ∑ i : Fin n2, ( g ( Fin.natAdd n1 i ) ) x ) from ?_ ];
    · rw [ ENNReal.mul_inv_cancel, ENNReal.inv_mul_cancel ] <;> norm_cast <;> norm_num [ NeZero.ne ];
      rw [ mul_add ];
    · rw [ Fin.sum_univ_add ];
  · rw [ ENNReal.sub_eq_of_eq_add ];
    · simp +decide [ ENNReal.mul_eq_top ];
      aesop;
    · rw [ ← add_mul, mul_comm ];
      rw [ add_comm, ENNReal.inv_mul_cancel ] <;> norm_cast
      · aesop
      exact ENNReal.natCast_ne_top _

/-- Reindex a uniform draw along an equivalence of finite index types. -/
lemma uniform_reindex {α β : Type} [Fintype α] [Fintype β] [Nonempty α] {X : Type}
    (e : α ≃ β) (g : β → PMF X) :
    haveI : Nonempty β := ⟨e (Classical.arbitrary α)⟩
    (PMF.uniformOfFintype β).bind g = (PMF.uniformOfFintype α).bind (fun a => g (e a)) := by
  apply PMF.ext; intro x
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_congr e]
  rw [← Equiv.tsum_eq e (fun b => (Fintype.card β : ENNReal)⁻¹ * (g b) x)]

/-- `uniform_fin_add_split` specialised to a list-length index. -/
lemma uniform_list_append_split {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2} {X : Type}
    (l1 l2 : List (OracleReduction O1 O2)) [NeZero l1.length] [NeZero l2.length]
    [NeZero (l1 ++ l2).length]
    (g : Fin (l1 ++ l2).length → PMF X)
    (gl : Fin l1.length → PMF X) (gr : Fin l2.length → PMF X)
    (hl : ∀ j : Fin l1.length, g ⟨↑j, by have := j.isLt; simp only [List.length_append]; omega⟩ = gl j)
    (hr : ∀ j : Fin l2.length,
      g ⟨l1.length + ↑j, by have := j.isLt; simp only [List.length_append]; omega⟩ = gr j) :
    (PMF.uniformOfFintype (Fin (l1 ++ l2).length)).bind g =
      (bernulli_ratio l1.length l2.length).bind (fun b =>
        if b then (PMF.uniformOfFintype (Fin l1.length)).bind gl
        else (PMF.uniformOfFintype (Fin l2.length)).bind gr) := by
  have hlen : (l1 ++ l2).length = l1.length + l2.length := List.length_append ..
  haveI : NeZero (l1.length + l2.length) := ⟨by have := (NeZero.ne l1.length); omega⟩
  rw [uniform_reindex (finCongr hlen).symm g]
  rw [uniform_fin_add_split l1.length l2.length]
  congr 1
  funext b
  cases b <;> simp only [Bool.false_eq_true, reduceIte, if_true]
  · congr 1; funext j; rw [← hr j]; congr 1
  · congr 1; funext j; rw [← hl j]; congr 1

/-- `simulateQ` commutes with an initial `initSample`: the sampled value can be
pulled outside as a `PMF.bind`. -/
lemma simulateQ_initSample_run {I : Type} {O : OracleSpec I} {st α β : Type}
    (impl : QueryImpl O (RState st)) (d : PMF α)
    (k : α → OracleComp (withPMFSpec O) β) (s : st) :
    StateT.run (simulateQ (addPMFtoImpl impl) ((OracleReduction.initSample d) >>= k)) s
      = d.bind (fun x => StateT.run (simulateQ (addPMFtoImpl impl) (k x)) s) := by
  rw [OracleReduction.initSample, OracleSpec.query, simulateQ_query_bind]
  simp only [addPMFtoImpl, OracleQuery.cont, OracleQuery.query, id_eq]
  simp only [bind, StateT.bind, StateT.lift, liftM, monadLift, MonadLift.monadLift, StateTSimps,
    PMF.map_bind, PMF.pure_bind, PMF.bind_bind, Functor.map]
  simp only [Pure.pure, PMF.pure_bind]
  rfl


/-- Binding a computation with `pure ∘ W` under `simulateQ` is the same as mapping `W`
over the result state (leaving the oracle state untouched). -/
lemma simulateQ_bind_pure_run {I : Type} {O : OracleSpec I} {st α γ : Type}
    (impl : QueryImpl O (RState st)) (c : OracleComp (withPMFSpec O) α)
    (W : α → γ) (s : st) :
    StateT.run (simulateQ (addPMFtoImpl impl) (c >>= fun x => (pure (W x)))) s
      = PMF.map (fun p => (W p.1, p.2)) (StateT.run (simulateQ (addPMFtoImpl impl) c) s) := by
  rw [show (c >>= fun x => (pure (W x) : OracleComp (withPMFSpec O) γ)) = (W <$> c) from rfl]
  rw [simulateQ_map]
  simp only [Functor.map, StateT.map, StateT.run, PMF.map_bind, PMF.map]
  rfl

/-- Transport an initial-state simulation along an equality of reductions. -/
lemma simulateQ_init_run_congr {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
    (impl : RStateOracle O1) (red red' : OracleReduction O1 O2) (hEq : red = red')
    (s : impl.stateType) :
    StateT.run (simulateQ (addPMFtoImpl impl.queries) red'.initialState) s
      = PMF.map (fun p => (hEq ▸ p.1, p.2))
          (StateT.run (simulateQ (addPMFtoImpl impl.queries) red.initialState) s) := by
  subst hEq
  simp only [eq_mpr_eq_cast, cast_eq]
  rw [show (fun p : red.stateType × impl.stateType => (p.1, p.2)) = id from by funext p; rfl,
    PMF.map_id]

/-- Extensionality for `internal_type`: equal indices and heterogeneously-equal values. -/
lemma internal_type_ext {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
    {l : List (OracleReduction O1 O2)} {i1 i2 : Fin l.length}
    {v1 : l[i1].stateType} {v2 : l[i2].stateType}
    (hi : i1 = i2) (hv : HEq v1 v2) :
    ({index := i1, value := v1} : internal_type l) = {index := i2, value := v2} := by
  subst hi
  simp only [heq_eq_eq] at hv
  rw [hv]

/-- Left-branch initial-state fibre agreement (the `hl` obligation of `flat_init`). -/
lemma flat_init_hl {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
    (l1 l2 : List (OracleReduction O1 O2)) (impl : RStateOracle O1)
    (sₒ : impl.stateType) (j : Fin l1.length) (hidx : (↑j : ℕ) < (l1 ++ l2).length) :
    ((StateT.run (simulateQ (addPMFtoImpl impl.queries)
        ((l1 ++ l2)[(⟨↑j, hidx⟩ : Fin (l1 ++ l2).length)].initialState >>= fun init =>
          pure {index := (⟨↑j, hidx⟩ : Fin (l1 ++ l2).length), value := init})) sₒ).bind
      fun a => PMF.map (flatToSumProd l1 l2 impl.stateType) (PMF.pure (a.1, a.2)))
    = (StateT.run (simulateQ (addPMFtoImpl impl.queries)
        ((l1[j].initialState >>= fun init =>
            (pure {index := j, value := init} : OracleComp (withPMFSpec O1) (internal_type l1)))
          >>= fun i2 =>
            (pure (Sum.inl i2) : OracleComp (withPMFSpec O1) (internal_type l1 ⊕ internal_type l2))))
        sₒ).bind fun d => PMF.pure (d.1, d.2) := by
  have hEq : l1[j] = (l1 ++ l2)[(⟨↑j, hidx⟩ : Fin (l1 ++ l2).length)] :=
    (List.getElem_append_left (bs := l2) (by exact j.isLt)).symm
  conv_lhs => rw [simulateQ_bind_pure_run, PMF.bind_map]
  conv_rhs => rw [bind_assoc]; simp only [pure_bind]; rw [simulateQ_bind_pure_run, PMF.bind_map]
  rw [simulateQ_init_run_congr impl (l1[j]) ((l1 ++ l2)[(⟨↑j, hidx⟩ : Fin (l1 ++ l2).length)]) hEq sₒ]
  rw [PMF.bind_map]
  congr 1
  funext p
  simp only [Function.comp, PMF.pure_map]
  congr 1
  simp only [flatToSumProd, Prod.mk.injEq, and_true]
  simp only [flatToSum, (show ((⟨↑j, hidx⟩ : Fin (l1 ++ l2).length) : ℕ) < l1.length from j.isLt),
    dif_pos]
  simp only [Fin.eta]
  congr 1
  simp only [eqRec_eq_cast, cast_cast, cast_eq]

/-- Right-branch initial-state fibre agreement (the `hr` obligation of `flat_init`). -/
lemma flat_init_hr {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
    (l1 l2 : List (OracleReduction O1 O2)) (impl : RStateOracle O1)
    (sₒ : impl.stateType) (j : Fin l2.length) (hidx : (l1.length + ↑j : ℕ) < (l1 ++ l2).length) :
    ((StateT.run (simulateQ (addPMFtoImpl impl.queries)
        ((l1 ++ l2)[(⟨l1.length + ↑j, hidx⟩ : Fin (l1 ++ l2).length)].initialState >>= fun init =>
          pure {index := (⟨l1.length + ↑j, hidx⟩ : Fin (l1 ++ l2).length), value := init})) sₒ).bind
      fun a => PMF.map (flatToSumProd l1 l2 impl.stateType) (PMF.pure (a.1, a.2)))
    = (StateT.run (simulateQ (addPMFtoImpl impl.queries)
        ((l2[j].initialState >>= fun init =>
            (pure {index := j, value := init} : OracleComp (withPMFSpec O1) (internal_type l2)))
          >>= fun i2 =>
            (pure (Sum.inr i2) : OracleComp (withPMFSpec O1) (internal_type l1 ⊕ internal_type l2))))
        sₒ).bind fun d => PMF.pure (d.1, d.2) := by
  have hval : ((⟨l1.length + ↑j, hidx⟩ : Fin (l1 ++ l2).length) : ℕ) = l1.length + ↑j := rfl
  have hEq : l2[j] = (l1 ++ l2)[(⟨l1.length + ↑j, hidx⟩ : Fin (l1 ++ l2).length)] := by
    conv_rhs => rw [Fin.getElem_fin, List.getElem_append_right (by rw [hval]; omega)]
    conv_lhs => rw [Fin.getElem_fin]
    congr 1
    rw [hval]; omega
  conv_lhs => rw [simulateQ_bind_pure_run, PMF.bind_map]
  conv_rhs => rw [bind_assoc]; simp only [pure_bind]; rw [simulateQ_bind_pure_run, PMF.bind_map]
  rw [simulateQ_init_run_congr impl (l2[j])
    ((l1 ++ l2)[(⟨l1.length + ↑j, hidx⟩ : Fin (l1 ++ l2).length)]) hEq sₒ]
  rw [PMF.bind_map]
  congr 1
  funext p
  simp only [Function.comp, PMF.pure_map]
  congr 1
  simp only [flatToSumProd, Prod.mk.injEq, and_true]
  simp only [flatToSum,
    (show ¬ ((⟨l1.length + ↑j, hidx⟩ : Fin (l1 ++ l2).length) : ℕ) < l1.length from by
      rw [hval]; omega),
    dif_neg]
  simp only [dif_neg (not_false)]
  have harith : l1.length + ↑j - l1.length = (↑j : ℕ) := by omega
  apply congrArg Sum.inr
  refine internal_type_ext (Fin.ext harith) ?_
  simp only [eqRec_heq_iff_heq, heq_eq_eq]


/-- Initial-state agreement under the abstraction `flatToSum`. -/
lemma flat_init {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l1 l2 : List (OracleReduction O1 O2))
  (Hl1 : l1.length > 0)
  (Hl2 : l2.length > 0)
  (He : forall x : I1, Nonempty (O1 x))
  (impl : RStateOracle O1) :
  ((reduction_combiner_list (l1 ++ l2) (by simp [Hl1, Hl2]) He).apply impl).initialState.map
      (flatToSumProd l1 l2 impl.stateType) =
  ((reductionCombiner_nontrivial_packed
      (l1.length, reduction_combiner_list l1 Hl1 He)
      (l2.length, reduction_combiner_list l2 Hl2 He)
      He).2.apply impl).initialState := by
  haveI : NeZero l1.length := ⟨by omega⟩
  haveI : NeZero l2.length := ⟨by omega⟩
  haveI : NeZero (l1 ++ l2).length := ⟨by simp only [List.length_append]; omega⟩
  simp only [OracleReduction.apply, reduction_combiner_list, reductionCombiner_nontrivial_packed,
    reductionCombiner_nontrivial]
  simp only [liftM_self, PMF.map_bind, bind_pure, PMF.bind_bind, PMF.pure_bind, Functor.map]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.map_bind]
  congr 1
  funext sₒ
  rw [PMF.map_bind]
  rw [simulateQ_initSample_run, PMF.bind_bind]
  conv_rhs => rw [simulateQ_initSample_run, PMF.bind_bind]
  rw [uniform_list_append_split l1 l2 _
    (fun j => (StateT.run (simulateQ (addPMFtoImpl impl.queries)
        ((l1[j].initialState >>= fun init =>
            (pure {index := j, value := init} : OracleComp (withPMFSpec O1) (internal_type l1)))
          >>= fun i2 =>
            (pure (Sum.inl i2) : OracleComp (withPMFSpec O1) (internal_type l1 ⊕ internal_type l2))))
        sₒ).bind fun d => PMF.pure (d.1, d.2))
    (fun j => (StateT.run (simulateQ (addPMFtoImpl impl.queries)
        ((l2[j].initialState >>= fun init =>
            (pure {index := j, value := init} : OracleComp (withPMFSpec O1) (internal_type l2)))
          >>= fun i2 =>
            (pure (Sum.inr i2) : OracleComp (withPMFSpec O1) (internal_type l1 ⊕ internal_type l2))))
        sₒ).bind fun d => PMF.pure (d.1, d.2))
    ?hl ?hr]
  case hl =>
    intro j
    exact flat_init_hl l1 l2 impl sₒ j
      (by have := j.isLt; simp only [List.length_append]; omega)
  case hr =>
    intro j
    exact flat_init_hr l1 l2 impl sₒ j
      (by have := j.isLt; simp only [List.length_append]; omega)
  · congr 1
    funext b
    cases b
    · simp only [Bool.false_eq_true, if_false, reduceIte]
      rw [bind_assoc, simulateQ_initSample_run, PMF.bind_bind]
    · simp only [if_true, reduceIte]
      rw [bind_assoc, simulateQ_initSample_run, PMF.bind_bind]


/-- Transport a per-query simulation along an equality of reductions. -/
lemma simQ_red_congr {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
    (impl : RStateOracle O1) (query : I2) (s2 : impl.stateType)
    (red red' : OracleReduction O1 O2) (hEq : red = red') (v : red.stateType) :
    simulateQ (OracleReduction.liftWithPMFAndState impl.queries red'.stateType) (red'.queries query)
        (hEq ▸ v, s2)
      = hEq ▸ (simulateQ (OracleReduction.liftWithPMFAndState impl.queries red.stateType)
          (red.queries query) (v, s2)) := by
  subst hEq; rfl

/-- Pull a reduction-state transport through `PMF.map`. -/
lemma pmf_map_red_transport {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
    {β A T : Type} (red red' : OracleReduction O1 O2) (hEq : red = red')
    (p : PMF (β × (red.stateType × T))) (F : β × (red'.stateType × T) → A) :
    PMF.map F (hEq ▸ p) = PMF.map (fun x => F (hEq ▸ x)) p := by
  subst hEq; rfl

/-- Distribute a reduction-state transport over a triple. -/
lemma prod_red_transport {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
    {β T : Type} (red red' : OracleReduction O1 O2) (hEq : red = red')
    (a : β) (st : red.stateType) (imp : T) :
    hEq ▸ (a, st, imp) = (a, hEq ▸ st, imp) := by
  subst hEq; rfl

/-- Per-query commutation, left branch (index lands in `l1`). -/
lemma flat_query_left {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l1 l2 : List (OracleReduction O1 O2))
  (Hl1 : l1.length > 0)
  (Hl2 : l2.length > 0)
  (He : forall x : I1, Nonempty (O1 x))
  (impl : RStateOracle O1)
  (query : I2)
  (s : internal_type (l1 ++ l2) × impl.stateType)
  (h : (s.1.index : ℕ) < l1.length) :
  PMF.map (mapSecond (flatToSumProd l1 l2 impl.stateType))
      (StateT.run (((reduction_combiner_list (l1 ++ l2) (by simp [Hl1, Hl2]) He).apply impl).queries query) s) =
    StateT.run (((reductionCombiner_nontrivial_packed
        (l1.length, reduction_combiner_list l1 Hl1 He)
        (l2.length, reduction_combiner_list l2 Hl2 He)
        He).2.apply impl).queries query) (flatToSumProd l1 l2 impl.stateType s) := by
  obtain ⟨⟨i, v⟩, s2⟩ := s
  simp only at h
  haveI : Nonempty (internal_type l1) :=
    ⟨{ index := ⟨0, Hl1⟩, value := Classical.choice (reductionNonEmpty (l1[0]'Hl1) He) }⟩
  haveI : Nonempty ((l1 ++ l2)[i].stateType) := reductionNonEmpty _ He
  haveI : Nonempty ((l1[(⟨↑i, h⟩ : Fin l1.length)]).stateType) := reductionNonEmpty _ He
  simp only [OracleReduction.apply, reduction_combiner_list, reductionCombiner_nontrivial_packed,
    reductionCombiner_nontrivial, flatToSumProd]
  simp only [OracleReduction.get, simulateQ_bind, simulateQ_query, OracleReduction.liftWithPMFAndState,
    OracleSpec.query]
  simp only [OracleQuery.input, OracleQuery.cont, id_eq, Functor.map, StateT.map, StateT.get,
    StateT.bind, bind, StateT.run, PMF.map_bind, PMF.pure_bind, RState.modify]
  simp only [flatToSum, dif_pos h]
  simp only [Pure.pure, PMF.pure_bind]
  rw [← addToStateL_spec _ _ _ _
    (({ index := ⟨↑i, h⟩, value := _ } : internal_type l1), s2)]
  simp only [← PFunctor.FreeM.monad_bind_def]
  simp only [OracleReduction.get, simulateQ_bind, simulateQ_query, OracleReduction.liftWithPMFAndState,
    OracleSpec.query]
  simp only [OracleQuery.input, OracleQuery.cont, id_eq, Functor.map, StateT.map, StateT.get,
    StateT.bind, bind, StateT.run, PMF.map_bind, PMF.pure_bind, RState.modify]
  simp only [Pure.pure, PMF.pure_bind]
  rw [← addToStateG_spec _ (fun x => ({ index := i, value := x } : internal_type (l1 ++ l2)))
      (fun z => if h : z.index = i then some (h ▸ z.value) else none)
      (by intro x; simp) _ _ impl.queries (v, s2)]
  rw [← addToStateG_spec _ (fun x => ({ index := ⟨↑i, h⟩, value := x } : internal_type l1))
      (fun z => if h_1 : z.index = ⟨↑i, h⟩ then some (h_1 ▸ z.value) else none)
      (by intro x; simp) _ _ impl.queries
      (((List.getElem_append_left (bs := l2) h (h' := i.isLt)) ▸ v), s2)]
  simp only [PMF.map_comp, Function.comp]
  have hEq : (l1 ++ l2)[i] = l1[(⟨↑i, h⟩ : Fin l1.length)] :=
    List.getElem_append_left (bs := l2) h (h' := i.isLt)
  rw [simQ_red_congr impl query s2 ((l1 ++ l2)[i]) (l1[(⟨↑i, h⟩ : Fin l1.length)]) hEq v]
  rw [pmf_map_red_transport ((l1 ++ l2)[i]) (l1[(⟨↑i, h⟩ : Fin l1.length)]) hEq]
  congr 1
  funext x
  obtain ⟨a, st, imp⟩ := x
  rw [prod_red_transport ((l1 ++ l2)[i]) (l1[(⟨↑i, h⟩ : Fin l1.length)]) hEq a st imp]
  simp only [mapSecond, flatToSumProd, flatToSum, dif_pos h, Function.comp]

/-- Per-query commutation, right branch (index lands in `l2`). -/
lemma flat_query_right {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l1 l2 : List (OracleReduction O1 O2))
  (Hl1 : l1.length > 0)
  (Hl2 : l2.length > 0)
  (He : forall x : I1, Nonempty (O1 x))
  (impl : RStateOracle O1)
  (query : I2)
  (s : internal_type (l1 ++ l2) × impl.stateType)
  (h : ¬ (s.1.index : ℕ) < l1.length) :
  PMF.map (mapSecond (flatToSumProd l1 l2 impl.stateType))
      (StateT.run (((reduction_combiner_list (l1 ++ l2) (by simp [Hl1, Hl2]) He).apply impl).queries query) s) =
    StateT.run (((reductionCombiner_nontrivial_packed
        (l1.length, reduction_combiner_list l1 Hl1 He)
        (l2.length, reduction_combiner_list l2 Hl2 He)
        He).2.apply impl).queries query) (flatToSumProd l1 l2 impl.stateType s) := by
  obtain ⟨⟨i, v⟩, s2⟩ := s
  simp only at h
  have hij : (↑i - l1.length) < l2.length := by
    have := i.isLt; simp only [List.length_append] at this; omega
  have h2 : l1.length ≤ ↑i := by omega
  haveI : Nonempty (internal_type l2) :=
    ⟨{ index := ⟨0, Hl2⟩, value := Classical.choice (reductionNonEmpty (l2[0]'Hl2) He) }⟩
  haveI : Nonempty ((l1 ++ l2)[i].stateType) := reductionNonEmpty _ He
  haveI : Nonempty ((l2[(⟨↑i - l1.length, hij⟩ : Fin l2.length)]).stateType) := reductionNonEmpty _ He
  simp only [OracleReduction.apply, reduction_combiner_list, reductionCombiner_nontrivial_packed,
    reductionCombiner_nontrivial, flatToSumProd]
  simp only [OracleReduction.get, simulateQ_bind, simulateQ_query, OracleReduction.liftWithPMFAndState,
    OracleSpec.query]
  simp only [OracleQuery.input, OracleQuery.cont, id_eq, Functor.map, StateT.map, StateT.get,
    StateT.bind, bind, StateT.run, PMF.map_bind, PMF.pure_bind, RState.modify]
  simp only [flatToSum, dif_neg h]
  simp only [Pure.pure, PMF.pure_bind]
  rw [← addToStateR_spec _ _ _ _
    (({ index := ⟨↑i - l1.length, hij⟩, value := _ } : internal_type l2), s2)]
  simp only [← PFunctor.FreeM.monad_bind_def]
  simp only [OracleReduction.get, simulateQ_bind, simulateQ_query, OracleReduction.liftWithPMFAndState,
    OracleSpec.query]
  simp only [OracleQuery.input, OracleQuery.cont, id_eq, Functor.map, StateT.map, StateT.get,
    StateT.bind, bind, StateT.run, PMF.map_bind, PMF.pure_bind, RState.modify]
  simp only [Pure.pure, PMF.pure_bind]
  rw [← addToStateG_spec _ (fun x => ({ index := i, value := x } : internal_type (l1 ++ l2)))
      (fun z => if h : z.index = i then some (h ▸ z.value) else none)
      (by intro x; simp) _ _ impl.queries (v, s2)]
  rw [← addToStateG_spec _ (fun x => ({ index := ⟨↑i - l1.length, hij⟩, value := x } : internal_type l2))
      (fun z => if h_1 : z.index = ⟨↑i - l1.length, hij⟩ then some (h_1 ▸ z.value) else none)
      (by intro x; simp) _ _ impl.queries
      (((List.getElem_append_right (bs := l2) h2 (h₂ := i.isLt)) ▸ v), s2)]
  simp only [PMF.map_comp, Function.comp]
  have hEq : (l1 ++ l2)[i] = l2[(⟨↑i - l1.length, hij⟩ : Fin l2.length)] :=
    List.getElem_append_right (bs := l2) h2 (h₂ := i.isLt)
  rw [simQ_red_congr impl query s2 ((l1 ++ l2)[i]) (l2[(⟨↑i - l1.length, hij⟩ : Fin l2.length)]) hEq v]
  rw [pmf_map_red_transport ((l1 ++ l2)[i]) (l2[(⟨↑i - l1.length, hij⟩ : Fin l2.length)]) hEq]
  congr 1
  funext x
  obtain ⟨a, st, imp⟩ := x
  rw [prod_red_transport ((l1 ++ l2)[i]) (l2[(⟨↑i - l1.length, hij⟩ : Fin l2.length)]) hEq a st imp]
  simp only [mapSecond, flatToSumProd, flatToSum, dif_neg h, Function.comp]

/-- Per-query commutation under the abstraction `flatToSum`. -/
lemma flat_query {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l1 l2 : List (OracleReduction O1 O2))
  (Hl1 : l1.length > 0)
  (Hl2 : l2.length > 0)
  (He : forall x : I1, Nonempty (O1 x))
  (impl : RStateOracle O1)
  (query : I2) :
  mapOutputState (flatToSumProd l1 l2 impl.stateType)
      (((reduction_combiner_list (l1 ++ l2) (by simp [Hl1, Hl2]) He).apply impl).queries query) =
  mapInputState (flatToSumProd l1 l2 impl.stateType)
      (((reductionCombiner_nontrivial_packed
        (l1.length, reduction_combiner_list l1 Hl1 He)
        (l2.length, reduction_combiner_list l2 Hl2 He)
        He).2.apply impl).queries query) := by
  funext s
  unfold mapOutputState mapInputState
  by_cases h : (s.1.index : ℕ) < l1.length
  · exact flat_query_left l1 l2 Hl1 Hl2 He impl query s h
  · exact flat_query_right l1 l2 Hl1 Hl2 He impl query s h

lemma reduction_combiner_list_vs_2
  {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
  (l1 l2 : List (OracleReduction O1 O2))
  (Hl1 : l1.length > 0)
  (Hl2 : l2.length > 0)
  (He : forall x : I1, Nonempty (O1 x))
  (impl : RStateOracle O1)
  :
  ObsEq
    ((reduction_combiner_list (l1 ++ l2) (by simp [Hl1, Hl2]) He).apply impl)
    ((reductionCombiner_nontrivial_packed
      (l1.length, reduction_combiner_list l1 Hl1 He)
      (l2.length, reduction_combiner_list l2 Hl2 He)
      He
    ).2.apply impl) := by
  apply correctAbstractionImpliesObsEq _ _ (flatToSumProd l1 l2 impl.stateType)
  refine ⟨?_, ?_⟩
  · exact flat_init l1 l2 Hl1 Hl2 He impl
  · intro query
    exact flat_query l1 l2 Hl1 Hl2 He impl query

lemma reduction_combiner_correct
  {I1 : Type} {O1 : OracleSpec I1}
  (dist : OracleComp (withPMFSpec O1) Bool)
  (assumption : SingleAssumption)
  (l1 l2 : List (OracleReduction assumption.O O1))
  (Hl1 : l1.length > 0)
  (Hl2 : l2.length > 0)
  (He : forall x : assumption.I, Nonempty (assumption.O x))
  : ascToReal dist assumption (l1.length, reduction_combiner_list l1 Hl1 He) +
    ascToReal dist assumption (l2.length, reduction_combiner_list l2 Hl2 He) =
  ascToReal dist assumption (l1.length+l2.length, reduction_combiner_list (l1++l2) (by simp [Hl1, Hl2]) He) :=
  by
    have inst1 :  Nonempty (reduction_combiner_list l1 Hl1 He).stateType :=
       reductionNonEmpty _ He
    have inst2 :  Nonempty (reduction_combiner_list l2 Hl2 He).stateType :=
        reductionNonEmpty _ He
    rw [reductionCombinerCorrect_nontrivial]
    · apply ascToRealFromObsEq
      · intro impl
        simp []
        apply ObsEq.symm
        apply reduction_combiner_list_vs_2
      · simp [reductionCombiner_nontrivial]
    · simp [Hl1, Hl2]

lemma reduction_combiner_correct_full
  {I1 : Type} {O1 : OracleSpec I1}
  (dist : OracleComp (withPMFSpec O1) Bool)
  (assumption : SingleAssumption)
  (l1 l2 : {x : List (OracleReduction assumption.O O1) // x.length > 0})
  : ascToReal dist assumption (combine_red l1) +
    ascToReal dist assumption (combine_red l2) =
  ascToReal dist assumption (combine_red (listCombiner l1 l2)) :=
by
    have He := non_trivial_spec assumption.i.1
    have inst1 :  Nonempty (reduction_combiner_list l1.1 l1.2 He).stateType :=
       reductionNonEmpty _ He
    have inst2 :  Nonempty (reduction_combiner_list l2.1 l2.2 He).stateType :=
        reductionNonEmpty _ He
    unfold combine_red
    unfold listCombiner
    unfold reduction_combiner_list_full
    simp [He]
    apply reduction_combiner_correct


/-- Pull an initial uniform (or arbitrary `PMF`) sample outside of `runDinstinguisher`. -/
lemma runDinstinguisher_initSample {I : Type} {O : OracleSpec I} {α : Type}
    (impl : RStateOracle O) (p : PMF α) (k : α → adversaryT O) :
    runDinstinguisher (OracleReduction.initSample p >>= k) impl
      = p.bind (fun x => runDinstinguisher (k x) impl) := by
  simp only [runDinstinguisher]
  have h : ∀ init : impl.stateType,
      PMF.map (fun x => x.1)
          (simulateQ (addPMFtoImpl impl.queries) (OracleReduction.initSample p >>= k) init)
        = p.bind (fun x =>
            PMF.map (fun y => y.1)
              (StateT.run (simulateQ (addPMFtoImpl impl.queries) (k x)) init)) := by
    intro init
    rw [show simulateQ (addPMFtoImpl impl.queries) (OracleReduction.initSample p >>= k) init
        = StateT.run (simulateQ (addPMFtoImpl impl.queries) (OracleReduction.initSample p >>= k))
            init from rfl]
    rw [simulateQ_initSample_run, PMF.map_bind]
  simp only [h]
  rw [show (impl.initialState >>= fun init =>
        p.bind fun x =>
          PMF.map (fun y => y.1) (StateT.run (simulateQ (addPMFtoImpl impl.queries) (k x)) init))
      = impl.initialState.bind (fun init =>
          p.bind fun x =>
            PMF.map (fun y => y.1) (StateT.run (simulateQ (addPMFtoImpl impl.queries) (k x)) init))
      from rfl]
  rw [PMF.bind_comm]
  rfl

/-- `defaultImpl` analogue of `addToStateG_spec`: relabelling the reduction state
by `f` (with left inverse `f_rev`) commutes with lowering by `defaultImpl`. -/
lemma addToStateG_defaultImpl_spec {J : Type} {O : OracleSpec J} {s1 s2 : Type}
    [Ns1 : Nonempty s1] {output : Type}
    (f : s1 -> s2) (f_rev : s2 -> Option s1)
    (f_ret : forall x, (f_rev (f x)) = some x)
    (comp : OracleReduction.SRReductionComp O s1 output) :
    forall (st : s1),
    simulateQ OracleReduction.defaultImpl (addToStateG s2 f f_rev comp) (f st) =
      (fun p => (p.1, f p.2)) <$> simulateQ OracleReduction.defaultImpl comp st := by
  induction comp with
  | pure x =>
    intro st
    change pure (x, f st) =
        (fun p => (p.1, f p.2)) <$> (pure (x, st) : OracleComp (withPMFSpec O) (output × s1))
    simp only [map_pure]
  | roll query cont Hind =>
    intro st
    conv_lhs => rw [addToStateG.eq_def]
    cases query with
    | oracle q =>
      simp only [OracleReduction.query, OracleReduction.get, OracleReduction.sample,
        OracleReduction.set, OracleReduction.modify]
      simp [simulateQ, goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier]
      apply bind_congr; intro a; exact Hind a st
    | sample p =>
      simp only [OracleReduction.query, OracleReduction.get, OracleReduction.sample,
        OracleReduction.set, OracleReduction.modify]
      simp [simulateQ, goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier]
      apply bind_congr; intro a; exact Hind a st
    | getState =>
      simp only [OracleReduction.query, OracleReduction.get, OracleReduction.sample,
        OracleReduction.set, OracleReduction.modify]
      simp [simulateQ, goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier,
        f_ret]
      exact Hind st st
    | setState stNew =>
      simp only [OracleReduction.query, OracleReduction.get, OracleReduction.sample,
        OracleReduction.set, OracleReduction.modify]
      simp [simulateQ, goodDoubleActionSimps, StateTSimps, OracleReductionSimps, RStateSimplifier,
        f_ret]
      exact Hind PUnit.unit stNew

/-- A single combiner query from state `{index := i, value := v}` runs `l[i]`'s
query, keeping the index fixed. -/
lemma combiner_query_step {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2}
    (l : List (OracleReduction O1 O2)) (Hl : l.length > 0)
    (He : forall x : I1, Nonempty (O1 x))
    (i : Fin l.length) (tt : I2) (v : l[i].stateType) :
    simulateQ OracleReduction.defaultImpl ((reduction_combiner_list l Hl He).queries tt)
        ({index := i, value := v} : internal_type l)
      = (fun p => (p.1, ({index := i, value := p.2} : internal_type l))) <$>
          simulateQ OracleReduction.defaultImpl ((l[i]).queries tt) v := by
  haveI : Nonempty (l[i]).stateType := reductionNonEmpty _ He
  exact addToStateG_defaultImpl_spec
      (fun y => ({index := i, value := y} : internal_type l))
      (fun z => if h : z.index = i then some (h ▸ z.value) else none)
      (by intro x; simp) (l[i].queries tt) v

/-- Inner state-tracking lemma: running the combiner's lowered query interpretation
from a state `{index := i, value := v}` behaves exactly like running the `i`-th
reduction from state `v`, with the index component held fixed at `i`. -/
lemma combiner_inner {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2} {X : Type}
    (l : List (OracleReduction O1 O2)) (Hl : l.length > 0)
    (He : forall x : I1, Nonempty (O1 x))
    (i : Fin l.length) (D : OracleComp (withPMFSpec O2) X) :
    forall (v : l[i].stateType),
    simulateQ OracleReduction.defaultImpl
        (simulateQ (OracleReduction.addPMFtoImpl2 (reduction_combiner_list l Hl He).queries) D)
        ({index := i, value := v} : internal_type l)
      = (fun p => (p.1, ({index := i, value := p.2} : internal_type l))) <$>
          simulateQ OracleReduction.defaultImpl
            (simulateQ (OracleReduction.addPMFtoImpl2 (l[i]).queries) D) v := by
  haveI : Nonempty (l[i]).stateType := reductionNonEmpty _ He
  induction D using OracleComp.inductionOn with
  | pure x =>
    intro v
    simp only [simulateQ_pure]
    change pure (x, ({index := i, value := v} : internal_type l)) =
        (fun p => (p.1, ({index := i, value := p.2} : internal_type l))) <$>
          (pure (x, v) : OracleComp (withPMFSpec O1) (X × l[i].stateType))
    simp only [map_pure]
  | query_bind t mx ih =>
    intro v
    cases t with
    | oracle tt =>
      rw [simulateQ_query_bind, simulateQ_query_bind]
      change simulateQ OracleReduction.defaultImpl
          ((reduction_combiner_list l Hl He).queries tt >>= fun u =>
            simulateQ (OracleReduction.addPMFtoImpl2 (reduction_combiner_list l Hl He).queries) (mx u))
          {index := i, value := v} =
        (fun p => (p.1, ({index := i, value := p.2} : internal_type l))) <$>
          simulateQ OracleReduction.defaultImpl
            (l[i].queries tt >>= fun u =>
              simulateQ (OracleReduction.addPMFtoImpl2 l[i].queries) (mx u)) v
      rw [simulateQ_bind, simulateQ_bind]
      simp only [bind, StateT.bind, StateT.run]
      rw [combiner_query_step]
      simp only [← PFunctor.FreeM.monad_bind_def, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp]
      apply bind_congr
      intro d
      simp only [map_eq_bind_pure_comp, Function.comp] at ih
      exact ih d.1 d.2
    | sample p =>
      rw [simulateQ_query_bind, simulateQ_query_bind]
      change simulateQ OracleReduction.defaultImpl
          (OracleReduction.sample p >>= fun u =>
            simulateQ (OracleReduction.addPMFtoImpl2 (reduction_combiner_list l Hl He).queries) (mx u))
          {index := i, value := v} =
        (fun p => (p.1, ({index := i, value := p.2} : internal_type l))) <$>
          simulateQ OracleReduction.defaultImpl
            (OracleReduction.sample p >>= fun u =>
              simulateQ (OracleReduction.addPMFtoImpl2 l[i].queries) (mx u)) v
      rw [simulateQ_bind, simulateQ_bind]
      simp only [bind, StateT.bind, StateT.run]
      have hsample : simulateQ OracleReduction.defaultImpl
            (OracleReduction.sample (O := O1) (s := internal_type l) p)
            ({index := i, value := v} : internal_type l)
          = (fun q => (q.1, ({index := i, value := q.2} : internal_type l))) <$>
              simulateQ OracleReduction.defaultImpl
                (OracleReduction.sample (O := O1) (s := l[i].stateType) p) v := by
        simp [OracleReduction.sample, simulateQ_query, OracleReduction.defaultImpl, OracleSpec.query,
          OracleQuery.input, OracleQuery.cont, Functor.map, StateT.map, StateT.lift, StateT.run,
          bind, map_bind, Function.comp, pure]
      rw [hsample]
      simp only [← PFunctor.FreeM.monad_bind_def, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp]
      apply bind_congr
      intro d
      simp only [map_eq_bind_pure_comp, Function.comp] at ih
      exact ih d.1 d.2

/-- Applying the list-combiner reduction to an adversary is the same as first
sampling a uniform index `i` and then applying the `i`-th reduction of the list.
The combiner samples its index once at initialization and never changes it, so
the whole computation is equivalent to picking the index up front. -/
lemma combiner_apply_uniform {I1 I2 : Type} {O1 : OracleSpec I1} {O2 : OracleSpec I2} {X : Type}
  (l : List (OracleReduction O1 O2)) (Hl : l.length > 0)
  (He : forall x : I1, Nonempty (O1 x))
  (D : OracleComp (withPMFSpec O2) X) :
  (reduction_combiner_list l Hl He).applyReductionToAdversary D =
    (do
      let i <- OracleReduction.initSample
        (@PMF.uniformOfFintype (Fin l.length) _ (⟨⟨0, Hl⟩⟩))
      (l[i]).applyReductionToAdversary D) := by
  have hinit : (reduction_combiner_list l Hl He).initialState =
      (do
        let x <- OracleReduction.initSample (@PMF.uniformOfFintype (Fin l.length) _ (⟨⟨0, Hl⟩⟩))
        let init <- l[x].initialState
        pure ({index := x, value := init} : internal_type l)) := rfl
  simp only [OracleReduction.applyReductionToAdversary, hinit, bind_assoc, pure_bind]
  simp only [combiner_inner]
  simp [Functor.mapRev, ← comp_map, Function.comp]

lemma compose_combine {I1 : Type} (O1 : OracleSpec I1)
  {I2 : Type} (O2 : OracleSpec I2)
  {I3 : Type} (O3 : OracleSpec I3)
  (r1 : OracleReduction O2 O3)
  (l : {x : List (OracleReduction O1 O2) // x.length > 0})
  (impl : RStateOracle O1) (dist : adversaryT O3) :
  runDinstinguisher dist
    ((rcompose (reduction_combiner_list_full l) r1).apply impl) =
  runDinstinguisher dist
    ((reduction_combiner_list_full ⟨l.val.map (fun x => rcompose x r1),
      by simp [l.2]
    ⟩).apply impl)
 :=
  by
    have He : forall i, Nonempty (O1 i) := non_trivial_spec impl
    simp only [reduction_combiner_list_full, dif_pos He]
    rw [goodDoubleAction, goodDoubleAction, rcompose_apply]
    rw [combiner_apply_uniform l.val l.2 He, combiner_apply_uniform _ _ He]
    rw [runDinstinguisher_initSample, runDinstinguisher_initSample]
    have hmap : (l.val.map (fun x => rcompose x r1)).length = l.val.length := by
      simp
    haveI : Nonempty (Fin l.val.length) := ⟨⟨0, l.2⟩⟩
    erw [uniform_reindex (finCongr hmap).symm]
    congr 1
    funext a
    have hget : (List.map (fun x => rcompose x r1) l.val)[(finCongr hmap).symm a]
        = rcompose (l.val[a]) r1 := by
      simp [List.getElem_map]
    rw [hget, rcompose_apply]
