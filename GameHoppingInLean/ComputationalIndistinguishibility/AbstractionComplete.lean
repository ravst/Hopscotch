import GameHoppingInLean.ComputationalIndistinguishibility.ObsEqComp

/-
# Facts about ObsEq and Abstraction
Here we prove two facts:
1. First that abstraction is able to prove any ObsEq in the following sense: for O1 O2 that are ObsEq there is
 f(O1), such that there are abstractions from f(O1) to both O1 and O2.
 Function f defines behavioral version of the oracle.
2. That ObsEq O1 O2 could be equivalently stated as that for all distinguishers (not even ppt) advantage is exactly zero.
These facts are never used in the rest of the project and are provided for completeness.
-/

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
  : OracleImpl O where
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
  : OracleImpl O where
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
    : OracleImpl O where
    stateType := S
    initialState := init
    queries := okernel



noncomputable def withInvariant3_correct {I : Type} {O : I → Type} {T : Type}
  (q_b : ℕ∞)
  (o : OracleImpl O)
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

noncomputable def behavioralRestricted {I : Type} {O : OracleSpec I} (o : OracleImpl O) (q_b : ENat) : OracleImpl O :=
  withInvariant2 q_b ((rState2Rstate q_b o).queries)
    (fun τ => (τ.length : ℕ∞)) (reachT o) (Hstep_reach o q_b) []
    ⟨by simp [],  reachT_nil o⟩

noncomputable def behavioralRestricted_val {I : Type} {O : OracleSpec I} (o : OracleImpl O) (q_b : ENat) :
  (behavioralRestricted o q_b).stateType -> ENat :=
    fun x => by
      simp [behavioralRestricted, withInvariant2] at x
      exact q_b - x.1.length


def rState2Rstate_ob_seq {I : Type} {O : OracleSpec I} (o : OracleImpl O) (q_b : ENat) :
 correctAbstractionBindBound (behavioralRestricted o q_b) o
  (fun x => condState o (x.1)) (behavioralRestricted_val o q_b) q_b
 := by
  simp [behavioralRestricted]
  unfold behavioralRestricted_val
  apply withInvariant3_correct q_b o
      ((rState2Rstate q_b o).queries) (condState o) (fun τ => (τ.length : ℕ∞))
      (reachT o) (Hstep_reach o q_b) (hstep o q_b) [] ⟨by simp [],  reachT_nil o⟩ (by simp []) (condState_nil o)

lemma reach_calc {I : Type} {O : OracleSpec I} (o1 o2 : OracleImpl O) (q_b : ENat)
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

def behavioralToRestrictedEq {I : Type} {O : OracleSpec I} (o1 o2 : OracleImpl O) (q_b : ENat)
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

/-- Composition of a (map-based) bounded abstraction `A → B` with a (bind-based) bounded
abstraction `B → C` yields a bind-based bounded abstraction `A → C`.
The valuation of `A` is reused, and the hypothesis `hval` states that the valuation only
increases along `f` (so that positivity of `valA s` transfers to positivity of `valB (f s)`,
which is what the step condition of the second abstraction needs). -/
lemma correctAbstractionBound_comp_BindBound {I : Type} {O : OracleSpec I}
    (A B C : OracleImpl O)
    (f : A.stateType → B.stateType) (valA : A.stateType → ENat)
    (g : B.stateType → PMF C.stateType) (valB : B.stateType → ENat)
    (b : ENat)
    (hval : ∀ s, valA s ≤ valB (f s))
    (HAB : correctAbstractionBound A B f valA b)
    (HBC : correctAbstractionBindBound B C g valB b) :
    correctAbstractionBindBound A C (fun x => g (f x)) valA b := by
  obtain ⟨⟨hInitAB, hGoodA, hStepAB⟩, hBoundA⟩ := HAB
  obtain ⟨⟨hInitBC, hGoodB, hStepBC⟩, hBoundB⟩ := HBC
  refine ⟨⟨?_, hGoodA, ?_⟩, hBoundA⟩
  · -- initial state
    rw [← hInitBC, ← hInitAB]
    simp [PMF.map_eq_bind_pure, PMF.bind_bind, PMF.pure_bind]
  · -- step condition
    intro query s hs
    have hsB : valB (f s) > 0 := lt_of_lt_of_le hs (hval s)
    have hAB := hStepAB query s hs
    have hBC := hStepBC query (f s) hsB
    simp only [mapOutputState, mapInputState] at hAB
    simp only [bindOutputState, bindInputState] at hBC ⊢
    rw [← hBC, ← hAB, PMF.map_eq_bind_pure, PMF.bind_bind]
    congr 1
    funext p
    rw [PMF.pure_bind]
    simp [bindSecond, mapSecond]

/-- For observationally-equivalent (up to `q_b` queries) oracles `o1` and `o2`,
the behaviorally-restricted oracle of `o1` is a correct (bind, bounded) abstraction of `o2`.
Obtained by composing the map-abstraction `behavioralRestricted o1 → behavioralRestricted o2`
with the bind-abstraction `behavioralRestricted o2 → o2`. -/
noncomputable def behavioralRestrictedToOther {I : Type} {O : OracleSpec I}
    (o1 o2 : OracleImpl O) (q_b : ENat) (H : ObsEqBounded o1 o2 q_b) :
    correctAbstractionBindBound (behavioralRestricted o1 q_b) o2
      (fun x => condState o2 x.1) (behavioralRestricted_val o1 q_b) q_b := by
  have hcomp := correctAbstractionBound_comp_BindBound
    (behavioralRestricted o1 q_b) (behavioralRestricted o2 q_b) o2
    (fun x => ⟨x.1, ⟨x.2.1, reach_calc o1 o2 q_b H x⟩⟩)
    (behavioralRestricted_val o1 q_b)
    (fun x => condState o2 x.1)
    (behavioralRestricted_val o2 q_b)
    q_b
    (fun s => le_of_eq (by rfl))
    (behavioralToRestrictedEq o1 o2 q_b H)
    (rState2Rstate_ob_seq o2 q_b)
  exact hcomp

/-- Completeness: for any two oracles `o1` and `o2` that are observationally equivalent
up to `q_b` queries, the behaviorally-restricted oracle of `o1` is a correct (bind, bounded)
abstraction of *both* `o1` and `o2`. -/
noncomputable def behavioralRestricted_complete {I : Type} {O : OracleSpec I}
    (o1 o2 : OracleImpl O) (q_b : ENat) (H : ObsEqBounded o1 o2 q_b) :
    correctAbstractionBindBound (behavioralRestricted o1 q_b) o1
        (fun x => condState o1 x.1) (behavioralRestricted_val o1 q_b) q_b ∧
    correctAbstractionBindBound (behavioralRestricted o1 q_b) o2
        (fun x => condState o2 x.1) (behavioralRestricted_val o1 q_b) q_b :=
  ⟨rState2Rstate_ob_seq o1 q_b, behavioralRestrictedToOther o1 o2 q_b H⟩

/- ## Completeness of distinguishing advantage for observational equivalence

The following develops the converse direction to `obsEq_distinquishing`: if *every*
distinguisher has zero advantage separating two oracles `o1` and `o2`, then the two oracles
are observationally equivalent (`ObsEq o1 o2`).

The idea is that a fixed list of queries `ql`, together with a boolean predicate `P` on the
resulting transcript, can be turned into a distinguisher `mkDist ql P`.  Its output
distribution is exactly `(runQueriesOnlyOut o ql).map P`.  Since zero advantage forces the
two output distributions to coincide, choosing `P` to be the indicator of a single transcript
recovers pointwise equality of `runQueriesOnlyOut o1 ql` and `runQueriesOnlyOut o2 ql`. -/

open OracleReduction in
/-- The distinguisher-side computation that replays a fixed list of queries `ql` against the
oracle and records the full transcript (each input paired with the oracle's answer). -/
noncomputable def collectComp {I : Type} {O : OracleSpec I} (ql : List I) :
    OracleComp (withPMFSpec O) (List (QueryWithResult O)) :=
  match ql with
  | [] => pure []
  | q :: qs => do
      let out ← initQuery q
      let rest ← collectComp qs
      return ({input := q, output := out} : QueryWithResult O) :: rest

/-- Simulating `collectComp ql` against `o` reproduces the transcript distribution
`runQueries2Aux o.queries ql`. -/
theorem collectComp_simulateQ_eq {I : Type} {O : OracleSpec I} (o : OracleImpl O)
    (ql : List I) :
    ∀ s, simulateQ (addPMFtoImpl o.queries) (collectComp (O := O) ql) s
      = runQueries2Aux o.queries ql s := by
  induction ql with
  | nil =>
    intro s
    simp only [collectComp, runQueries2Aux, simulateQ_pure]
    rfl
  | cons q qs ih =>
    intro s
    conv_lhs => rw [collectComp]
    rw [simulateQ_query_bind]
    conv_rhs => rw [runQueries2Aux]
    change ((o.queries q) s).bind
        (fun d => simulateQ (addPMFtoImpl o.queries)
          (collectComp qs >>= fun rest => pure (⟨q, d.1⟩ :: rest)) d.2) = _
    simp only [simulateQ_bind, simulateQ_pure]
    congr 1
    funext d
    change ((simulateQ (addPMFtoImpl o.queries) (collectComp qs) d.2).bind
        (fun p => PMF.pure (⟨q, d.1⟩ :: p.1, p.2))) = _
    rw [ih d.2]
    simp only [bind, StateT.bind]
    rfl

/-- The distinguisher obtained from a query list `ql` and a boolean predicate `P` on
transcripts: replay `ql` and output `P` of the observed transcript. -/
noncomputable def mkDist {I : Type} {O : OracleSpec I} (ql : List I)
    (P : List (QueryWithResult O) → Bool) : adversaryT O :=
  collectComp ql >>= fun t => pure (P t)

/-- The output distribution of `mkDist ql P` against `o` is exactly the push-forward of the
transcript distribution `runQueriesOnlyOut o ql` along `P`. -/
theorem runDinstinguisher_mkDist {I : Type} {O : OracleSpec I} (o : OracleImpl O)
    (ql : List I) (P : List (QueryWithResult O) → Bool) :
    runDinstinguisher (mkDist ql P) o = (runQueriesOnlyOut o ql).map P := by
  rw [runDinstinguisher_unfold, runQueriesOnlyOut, runQueries2]
  simp only [PMF.map_comp, ← PMF.bind_map]
  rw [show (o.initialState >>= runQueries2Aux o.queries ql)
      = o.initialState.bind (runQueries2Aux o.queries ql) from rfl]
  rw [PMF.map_bind]
  congr 1
  funext s
  rw [mkDist]
  simp only [simulateQ_bind, simulateQ_pure]
  change PMF.map Prod.fst ((simulateQ (addPMFtoImpl o.queries) (collectComp ql) s).bind
      (fun d => PMF.pure (P d.1, d.2))) = _
  rw [PMF.map_bind, collectComp_simulateQ_eq]
  simp only [PMF.map_comp, PMF.map_pure_eq_pure, Function.comp]
  rw [PMF.map_eq_bind_pure]
  rfl

/-- **Characterizing ObsEq as distinguishing advantage.**  If every distinguisher achieves zero
advantage separating `o1` and `o2`, then `o1` and `o2` are observationally equivalent. -/
theorem obsEq_of_advantage_zero {I : Type} {O : OracleSpec I} (o1 o2 : OracleImpl O)
    (H : ∀ d : adversaryT O, advantage d o1 o2 = 0) : ObsEq o1 o2 := by
  classical
  have Hd : ∀ d : adversaryT O, runDinstinguisher d o1 = runDinstinguisher d o2 :=
    fun d => distanceOnBoolIrreflexive _ _ (H d)
  intro ql
  apply PMF.ext
  intro target
  have h := Hd (mkDist ql (fun x => decide (x = target)))
  rw [runDinstinguisher_mkDist, runDinstinguisher_mkDist] at h
  have h2 := congrArg (fun (p : PMF Bool) => p true) h
  simp only [PMF.map_apply] at h2
  rw [tsum_eq_single target, tsum_eq_single target] at h2
  · simpa using h2
  · intro b hb; simp [hb]
  · intro b hb; simp [hb]

-- eqivalence
theorem obsEq_eq_advantage_zero {I : Type} {O : OracleSpec I} (o1 o2 : OracleImpl O) :
     ObsEq o1 o2 ↔ ∀ d : adversaryT O, advantage d o1 o2 = 0 := by
    constructor
    · intro H d
      simp [advantage, pdistancePMF]
      rw [obsEq_distinquishing_ub o1 o2 H]
      simp []
    · apply obsEq_of_advantage_zero
