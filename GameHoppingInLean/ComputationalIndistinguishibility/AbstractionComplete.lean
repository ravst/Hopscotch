import GameHoppingInLean.ComputationalIndistinguishibility.ObsEqComp


noncomputable def withInvariant {I : Type} {O : I → Type} {T : Type}
  (q_b : ℕ∞)
  (ostep : (i : I) → T → PMF (O i × T))
  (lvl : T → ℕ∞)
  (reach : (x : T) → Prop)
  (Hstep_reach : ∀ (i : I) (τ : T), reach τ → lvl τ + 1 ≤ q_b →
    ∀ p ∈ (ostep i τ).support, lvl p.2 = lvl τ + 1 ∧ reach p.2)
  : (i : I) → {x // lvl x <= q_b ∧ reach x } -> PMF (O i × {x // lvl x <= q_b ∧ reach x }) :=
fun i t =>
  (ostep i t).bindOnSupport (fun (out, state) Hp =>
  if H : lvl t +1 ≤ q_b then
    PMF.pure (out, ⟨state, by
      constructor
      · have X := (Hstep_reach i t.1 t.2.2 H (out ,state) Hp).1
        simp at X
        apply le_trans
        swap
        · apply H
        exact ge_of_eq (id (Eq.symm X))
      apply (Hstep_reach i t.1 t.2.2 H (out ,state) Hp).2
      ⟩)
  else
    -- error branch
    PMF.pure (out, t)
  )

noncomputable def withInvariant2 {I : Type} {O : I → Type} {T : Type}
  (q_b : ℕ∞)
  (ostep : (i : I) → T → PMF (O i × T))
  (lvl : T → ℕ∞)
  (reach : T → Prop)
  (Hstep_reach : ∀ (i : I) (τ : T), reach τ → lvl τ + 1 ≤ q_b →
    ∀ p ∈ (ostep i τ).support, lvl p.2 = lvl τ + 1 ∧ reach p.2)
  (start : T)
  (reach_unit : lvl start <= q_b ∧ reach start)
  : RStateOracle O where
  stateType := {x // lvl x <= q_b ∧ reach x }
  initialState := PMF.pure ⟨start, reach_unit⟩
  queries :=
    withInvariant q_b ostep lvl reach Hstep_reach


noncomputable def withInvariant2_val {I : Type} {O : I → Type} {T : Type}
  (q_b : ℕ∞)
  (ostep : (i : I) → T → PMF (O i × T))
  (lvl : T → ℕ∞)
  (reach : T → Prop)
  (Hstep_reach : ∀ (i : I) (τ : T), reach τ → lvl τ + 1 ≤ q_b →
    ∀ p ∈ (ostep i τ).support, lvl p.2 = lvl τ + 1 ∧ reach p.2)
  (start : T)
  (reach_unit : lvl start <= q_b ∧ reach start)
  : (withInvariant2 q_b ostep lvl reach Hstep_reach start reach_unit).stateType -> ENat :=
   (fun x =>
      by
        simp [withInvariant2] at x
        exact (q_b - lvl x)
      )



noncomputable def simple {I : Type} {O : I → Type} {T : Type}
  (ostep : (i : I) → T → PMF (O i × T))
  (start : T)
  : RStateOracle O where
  stateType := T
  initialState := PMF.pure start
  queries := ostep


noncomputable def withInvariant2_correct {I : Type} {O : I → Type} {T : Type}
  (q_b : ℕ∞)
  (ostep : (i : I) → T → PMF (O i × T))
  (lvl : T → ℕ∞)
  (reach : T → Prop)
  (Hstep_reach : ∀ (i : I) (τ : T), reach τ → lvl τ + 1 ≤ q_b →
    ∀ p ∈ (ostep i τ).support, lvl p.2 = lvl τ + 1 ∧ reach p.2)
  (start : T)
  (reach_unit : lvl start <= q_b ∧ reach start)
  (lvl_start : lvl start = 0) :
    correctAbstractionBound (withInvariant2 q_b ostep lvl reach Hstep_reach start reach_unit) (simple ostep start)
      (fun x => x.1) (withInvariant2_val q_b ostep lvl reach Hstep_reach start reach_unit) q_b := by
  unfold withInvariant2_val
  constructor
  · simp [correctAbstractionBound_inner]
    constructor
    · simp [withInvariant2, simple]
      simp [PMF.map]
    · constructor
      · simp [goodValuation, withInvariant2]
        intro query s b
        have I1 : DecidableEq ENat := Classical.decEq ENat
        have I2 : forall a, Decidable ((ostep query s) a = 0) := by
          intro a
          have T : DecidableEq ENNReal := inferInstance
          apply T ((ostep query s) a) 0
        simp only [withInvariant]
        intro l
        if H : lvl s + 1 ≤ q_b then
          conv =>
            arg 1
            arg 1
            arg 2
            intro x Hx
            simp [H]
          rw [PMF.support_bindOnSupport]
          simp
          intro a y c
          -- have W : reach l.2 := l.2.2
          -- subst l
          -- simp at W
          have Z := (Hstep_reach query s l H (a, y) c).1
          simp at Z
          rw [Z]
          rw [add_assoc, add_comm 1 (lvl s), tsub_add_cancel_of_le H]
        else
          simp [H]
          intro a b c
          calc q_b ≤ q_b - lvl s + lvl s := le_tsub_add
            _ ≤ q_b - lvl s + 1 + lvl s := by gcongr; exact le_self_add
      intro query st Hst
      simp [withInvariant, withInvariant2, simple]
      simp [mapOutputState, mapInputState, PMF.map]
      simp [StateT.run, withInvariant, mapSecond, Function.comp]
      simp at Hst
      have H : lvl st.1 + 1 ≤ q_b := Order.add_one_le_of_lt Hst
      simp [H]
      rw [<-PMF.bindOnSupport_eq_bind]
      rw[PMF.bindOnSupport_bindOnSupport]
      conv =>
        lhs
        arg 2
        intro a ah
        rw [PMF.bindOnSupport_eq_bind]
        simp []
      simp []
  · simp [withInvariant2, withInvariant, simple]
    simp [lvl_start]



def withInv3 {I : Type} {O : I → Type} {S : Type}
    (okernel : (i : I) → S → PMF (O i × S))
    (init : PMF S)
    : RStateOracle O where
    stateType := S
    initialState := init
    queries := okernel



noncomputable def withInvariant3_correct {I : Type} {O : I → Type} {T : Type}
  (q_b : ℕ∞)
  (o : RStateOracle O)
  (ostep : (i : I) → T → PMF (O i × T))
  (cs : T → PMF o.stateType)
  (lvl : T → ℕ∞)
  (reach : T → Prop)
  (Hstep_reach : ∀ (i : I) (τ : T), reach τ → lvl τ + 1 ≤ q_b →
    ∀ p ∈ (ostep i τ).support, lvl p.2 = lvl τ + 1 ∧ reach p.2)
  (HSTEP : ∀ (i : I) (τ : T), reach τ → lvl τ + 1 ≤ q_b →
      (cs τ).bind (o.queries i) =
        (ostep i τ).bind (fun p => (cs p.2).map (fun s' => (p.1, s'))))
  (start : T)
  (reach_unit : lvl start <= q_b ∧ reach start)
  (lvl_start : lvl start = 0)
  (hStart : cs start = o.initialState)
  :
    correctAbstractionBindBound (withInvariant2 q_b ostep lvl reach Hstep_reach start reach_unit)
      o
      (fun x => cs (x.1)) (fun x =>
      by
        simp [withInvariant2] at x
        exact q_b - lvl x.1
      ) q_b := by
    constructor
    · constructor
      · simp [withInvariant2, withInv3, hStart]
      · constructor
        · simp [goodValuation, withInvariant2]
          intro query s b
          have I1 : DecidableEq ENat := Classical.decEq ENat
          have I2 : forall a, Decidable ((ostep query s) a = 0) := by
            intro a
            have T : DecidableEq ENNReal := inferInstance
            apply T ((ostep query s) a) 0
          simp only [withInvariant, withInvariant2_val]
          intro l
          if H : lvl s + 1 ≤ q_b then
            conv =>
              arg 1
              arg 1
              arg 2
              intro x Hx
              simp [H]
            rw [PMF.support_bindOnSupport]
            simp
            intro  a y c
            have Z := (Hstep_reach query s l H (a, y) c).1
            simp at Z
            rw [Z]
            rw [add_assoc, add_comm 1 (lvl s), tsub_add_cancel_of_le H]
          else
            simp [H]
            intro a b c
            calc q_b ≤ q_b - lvl s + lvl s := le_tsub_add
              _ ≤ q_b - lvl s + 1 + lvl s := by gcongr; exact le_self_add
        · intro q
          simp [withInvariant2]
          intro t tR tL
          simp [bindOutputState, bindInputState, StateT.run, withInv3, bindSecond,
            withInvariant]
          -- simp [withInvariant2_val] at tL
          intro W
          have X : lvl t +1 ≤ q_b := Order.add_one_le_of_lt W
          simp [X]
          unfold bindSecond
          simp []
          rw [HSTEP] <;> try assumption
          conv =>
            rhs
            rw [<-PMF.bindOnSupport_eq_bind]
          rw [<-PMF.bindOnSupport_eq_bind]
          rw [PMF.bindOnSupport_bindOnSupport]
          congr 1
          ext1 a
          ext1 h
          simp [PMF.bindOnSupport_eq_bind]
          simp [PMF.map]
          congr 1
    · simp [withInvariant2, lvl_start, withInvariant2_val]

noncomputable def behavioralRestricted {I : Type} {O : OracleSpec I} (o : RStateOracle O) (q_b : ENat) : RStateOracle O :=
  withInvariant2 q_b ((rState2Rstate q_b o).queries)
    (fun τ => (τ.length : ℕ∞)) (reachT o) (Hstep_reach o q_b) []
    ⟨by simp [],  reachT_nil o⟩

noncomputable def behavioralRestricted_val {I : Type} {O : OracleSpec I} (o : RStateOracle O) (q_b : ENat) :
  (behavioralRestricted o q_b).stateType -> ENat :=
    fun x => by
      simp [behavioralRestricted, withInvariant2] at x
      exact q_b - x.1.length


def rState2Rstate_ob_seq {I : Type} {O : OracleSpec I} (o : RStateOracle O) (q_b : ENat) :
 correctAbstractionBindBound (behavioralRestricted o q_b) o
  (fun x => condState o (x.1)) (behavioralRestricted_val o q_b) q_b
 := by
  simp [behavioralRestricted]
  unfold behavioralRestricted_val
  apply withInvariant3_correct q_b o
      ((rState2Rstate q_b o).queries) (condState o) (fun τ => (τ.length : ℕ∞))
      (reachT o) (Hstep_reach o q_b) (hstep o q_b) [] ⟨by simp [],  reachT_nil o⟩ (by simp []) (condState_nil o)

lemma reach_calc {I : Type} {O : OracleSpec I} (o1 o2 : RStateOracle O) (q_b : ENat)
  (H : ObsEqBounded o1 o2 q_b)
  (x : { x // ↑(List.length x) ≤ q_b ∧ reachT o1 x })
  : reachT o2 x := by
    rw [reachT_eq]
    simp [reachT2]
    cases x
    case mk xval Hx =>
    rw [<-H]
    · simp []
      rw [reachT_eq] at Hx
      have Z := Hx.2
      simp [reachT2] at Z
      apply Z
    simp []
    apply Hx.1


lemma map_bindOnSupport_comm {α β γ} (p : PMF α) (f : (a : α) → a ∈ p.support → PMF β)
    (g : β → γ) :
    (p.bindOnSupport f).map g = p.bindOnSupport (fun a h => (f a h).map g) := by
  simp only [PMF.map]
  rw [← PMF.bindOnSupport_eq_bind]
  rw [PMF.bindOnSupport_bindOnSupport]
  congr 1
  funext a ha
  rw [PMF.bindOnSupport_eq_bind]

lemma withInvariant_congr_ostep {I : Type} {O : I → Type} {T : Type} (q_b : ℕ∞)
    (ostep1 ostep2 : (i : I) → T → PMF (O i × T)) (lvl : T → ℕ∞) (reach : T → Prop)
    (H1 : ∀ (i : I) (τ : T), reach τ → lvl τ + 1 ≤ q_b →
      ∀ p ∈ (ostep1 i τ).support, lvl p.2 = lvl τ + 1 ∧ reach p.2)
    (H2 : ∀ (i : I) (τ : T), reach τ → lvl τ + 1 ≤ q_b →
      ∀ p ∈ (ostep2 i τ).support, lvl p.2 = lvl τ + 1 ∧ reach p.2)
    (heq : ostep1 = ostep2)
    (query : I) (t : {x // lvl x ≤ q_b ∧ reach x}) :
    withInvariant q_b ostep1 lvl reach H1 query t
      = withInvariant q_b ostep2 lvl reach H2 query t := by
  subst heq
  rfl

lemma withInvariant_map_eq {I : Type} {O : I → Type} {T : Type} (q_b : ℕ∞)
    (ostep : (i : I) → T → PMF (O i × T)) (lvl : T → ℕ∞)
    (reach1 reach2 : T → Prop)
    (H1 : ∀ (i : I) (τ : T), reach1 τ → lvl τ + 1 ≤ q_b →
      ∀ p ∈ (ostep i τ).support, lvl p.2 = lvl τ + 1 ∧ reach1 p.2)
    (H2 : ∀ (i : I) (τ : T), reach2 τ → lvl τ + 1 ≤ q_b →
      ∀ p ∈ (ostep i τ).support, lvl p.2 = lvl τ + 1 ∧ reach2 p.2)
    (g : {x // lvl x ≤ q_b ∧ reach1 x} → {x // lvl x ≤ q_b ∧ reach2 x})
    (hg : ∀ x, (↑(g x) : T) = ↑x)
    (query : I) (t1 : {x // lvl x ≤ q_b ∧ reach1 x}) (t2 : {x // lvl x ≤ q_b ∧ reach2 x})
    (ht : (↑t1 : T) = ↑t2) :
    (withInvariant q_b ostep lvl reach1 H1 query t1).map (mapSecond g)
      = withInvariant q_b ostep lvl reach2 H2 query t2 := by
  simp only [withInvariant]
  rw [map_bindOnSupport_comm]
  obtain ⟨v1, hv1⟩ := t1
  obtain ⟨v2, hv2⟩ := t2
  simp only at ht
  subst ht
  congr 1
  funext x Hp
  split
  · rw [PMF.pure_map]
    congr 1
    simp only [mapSecond_mk]
    congr 1
    exact Subtype.ext (hg _)
  · rw [PMF.pure_map]
    congr 1
    simp only [mapSecond_mk]
    congr 1
    exact Subtype.ext (hg _)

def behavioralToRestrictedEq {I : Type} {O : OracleSpec I} (o1 o2 : RStateOracle O) (q_b : ENat)
  (H : ObsEqBounded o1 o2 q_b) :
  correctAbstractionBound
    (behavioralRestricted o1 q_b)
    (behavioralRestricted o2 q_b)
    (fun x => by
      simp [behavioralRestricted, withInvariant2]
      simp [behavioralRestricted, withInvariant2] at x
      exact ⟨x.1, ⟨x.2.1, reach_calc o1 o2 q_b H x⟩⟩)
    (fun x => q_b - x.1.length) q_b
    := by
  have Z : rState2Rstate q_b o1 = rState2Rstate q_b o2 := by
    simp [rState2Rstate]
    rw [behavioral_eq_from_obsEq o1 o2 q_b H]
  constructor
  · constructor
    · simp [behavioralRestricted, withInvariant2, PMF.map]
    constructor
    · simp [goodValuation]
      intro query s
      simp [behavioralRestricted, withInvariant2]
      intro l hmem
      simp only [withInvariant] at hmem
      rw [PMF.mem_support_bindOnSupport_iff] at hmem
      obtain ⟨a, ha, hl⟩ := hmem
      simp only [Set.mem_setOf_eq]
      if H : (s.1.length : ℕ∞) + 1 ≤ q_b then
        rw [dif_pos H, PMF.mem_support_pure_iff] at hl
        subst hl
        have Z2 := (Hstep_reach o1 q_b query s.1 s.2.2 H a ha).1
        simp only
        rw [Z2]
        rw [add_assoc, add_comm 1 (s.1.length : ℕ∞), tsub_add_cancel_of_le H]
      else
        rw [dif_neg H, PMF.mem_support_pure_iff] at hl
        subst hl
        simp only
        calc q_b ≤ q_b - (s.1.length : ℕ∞) + (s.1.length : ℕ∞) := le_tsub_add
          _ ≤ q_b - (s.1.length : ℕ∞) + 1 + (s.1.length : ℕ∞) := by gcongr; exact le_self_add
    simp [behavioralRestricted, PMF.map]
    simp [correctAbstractionBound_step]
    intro query s Hs
    simp [withInvariant2, withInvariant]
    simp [mapInputState, mapOutputState]
    simp [StateT.run]
    have Zq : (rState2Rstate q_b o1).queries = (rState2Rstate q_b o2).queries := by
      congr 1
    let s' : {x : List (QueryWithResult O) // (↑(List.length x) : ℕ∞) ≤ q_b ∧ reachT o1 x} := s
    let t2 : {x : List (QueryWithResult O) // (↑(List.length x) : ℕ∞) ≤ q_b ∧ reachT o2 x} :=
      ⟨↑s', ⟨s'.2.1, reach_calc o1 o2 q_b H s'⟩⟩
    refine Eq.trans (withInvariant_map_eq q_b (rState2Rstate q_b o1).queries
      (fun τ => (τ.length : ℕ∞)) (reachT o1) (reachT o2) (Hstep_reach o1 q_b)
      (by rw [Zq]; exact Hstep_reach o2 q_b) _ (fun x => rfl) query s t2 rfl) ?_
    exact withInvariant_congr_ostep q_b (rState2Rstate q_b o1).queries (rState2Rstate q_b o2).queries
      (fun τ => (τ.length : ℕ∞)) (reachT o2) (by rw [Zq]; exact Hstep_reach o2 q_b)
      (Hstep_reach o2 q_b) Zq query t2
  simp [behavioralRestricted, withInvariant2]

  -- for any two o1 o2 that have obsEqBOunded, we have
  --1- correctAbstractionBound: (behavioralRestricted o1 q_b) --> (behavioralRestricted o2 q_b)
  --2- correctAbstractionBindBound: (behavioralRestricted o1 q_b) -> o1
  --3- correctAbstractionBindBound: (behavioralRestricted o2 q_b) -> o2
  -- composing (1) and (3) we got: (behavioralRestricted o1 q_b) -> o2
-- prove that
-- 1. there is correctAbstractionBindBound from (behavioralRestricted o1 q_b) to o2 by using approprite composition lemma
-- 2. formulate completness in on theorem, i.e. that for any o1 o2 with bosEqBOunded that from (behavioralRestricted o1 q_b) correct abstraction to both o1 and o2.
