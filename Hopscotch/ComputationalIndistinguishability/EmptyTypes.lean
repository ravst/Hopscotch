import Hopscotch.Comp.OracleReductions

/- # Solving issues about empty types in state space or in oracle interface.
When combining reductions (ReductionCombiner.lean, pick-one-reduction-from-list-at-random) it could 'happen' that analyzed reduction has empty state space. For example that could 'happen' if for some query `q` we are returned an object of empty type `spec q`.
 In this file we deal with all such annoying issues. We prove that existence of oracleImpl implies that spec has no empty types in it. We also prove that if spec has no empty types then reductions have nonempty state-spaces.
 -/

lemma pmf_nonempty (x : PMF X) : Nonempty X :=
  open Classical in
  byContradiction (by
    intro H
    simp at H
    cases x
    case mk d Hd =>
    simp [HasSum] at Hd
    simp [Filter.atTop, default, Set.Ici]  at Hd
    simp [Filter.Tendsto]  at Hd
  )

lemma QueryImpl2NonEmpty (stateType : Type _) {I : Type _} {O : OracleSpec I}
  (x : QueryImpl O (RState stateType))
  [Hs : Nonempty stateType] :
  forall x : I, Nonempty (O x) := by
    intro input
    cases Hs
    case intro init =>
    have Z := pmf_nonempty (x input init)
    cases Z
    case intro a =>
    constructor
    exact a.1

lemma non_trivial_spec {I : Type _} {O : OracleSpec I} (ro : OracleImpl O) :
  forall x : I, Nonempty (O x) :=
  by
    have Hstate : Nonempty ro.stateType := pmf_nonempty ro.initialState
    apply QueryImpl2NonEmpty ro.stateType ro.queries

lemma implementableWithPMF {I : Type _} (O : OracleSpec I) (H : forall x : I, Nonempty (O x)) :
  forall x, Nonempty ((withPMFSpec O) x) := by
  intro input
  cases input
  case oracle input =>
    simp [withPMFSpec]
    apply H
  case sample d =>
    simp [withPMFSpec]
    apply pmf_nonempty d

--somehow inverse of QueryImpl2NonEmpty
noncomputable def anyImplementation {I : Type _} (O : OracleSpec I)
  (H : forall x : I, Nonempty (O x))
  : QueryImpl O Id := by
    open Classical in
    intro x
    have y := Classical.choice (H x)
    exact y

lemma oracleCompToObject {Z : Type l2} {I : Type l1} (O : OracleSpec.{l1, l2} I)
  (H : forall x : I, Nonempty (O x))
  (comp : OracleComp O Z)
  : Nonempty Z := by
  let impl := anyImplementation O H
  let l := simulateQ impl comp
  constructor
  exact l

lemma reductionNonEmpty
  {I1 : Type _} {O1 : OracleSpec I1}
  {I2 : Type _} {O2 : OracleSpec I2}
  (x : OracleReduction O1 O2)
  (He : forall x : I1, Nonempty (O1 x)):
  Nonempty x.stateType :=
    oracleCompToObject _ (implementableWithPMF _ He) x.initialState
