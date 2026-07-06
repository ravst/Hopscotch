import GameHoppingInLean.ComputationalIndistinguishibility.AdversaryAdvantage
import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.Misc.SimpAttrLemmas
import Mathlib.Data.ENat.Lattice


noncomputable def FreeM.depth.{uA, uB, uC} {P : PFunctor.{uA, uB}} {α : Type uC} : PFunctor.FreeM P α -> ℕ∞
| PFunctor.FreeM.pure _ => 0
| PFunctor.FreeM.roll _input cont =>
  1 + iSup (fun u => depth (cont u))

lemma abstraction_with_levels_and_reach {I : Type} {O : I → Type} {S T X : Type}
    (q_b : ℕ∞)
    (okernel : (i : I) → S → PMF (O i × S))
    (ostep : (i : I) → T → PMF (O i × T))
    (cs : T → PMF S)
    (lvl : T → ℕ∞)
    (reach : T → Prop)
    (Hstep_reach : ∀ (i : I) (τ : T), reach τ → lvl τ + 1 ≤ q_b →
      ∀ p ∈ (ostep i τ).support, lvl p.2 = lvl τ + 1 ∧ reach p.2)
    (HSTEP : ∀ (i : I) (τ : T), reach τ → lvl τ + 1 ≤ q_b →
      (cs τ).bind (okernel i) =
        (ostep i τ).bind (fun p => (cs p.2).map (fun s' => (p.1, s'))))
    : ∀ (c : OracleComp (withPMFSpec O) X) (τ : T), reach τ → lvl τ + FreeM.depth c ≤ q_b →
        (cs τ).bind (fun s => (simulateQ (addPMFtoImpl okernel) c s).map Prod.fst) =
        (simulateQ (addPMFtoImpl ostep) c τ).map Prod.fst := by
  intro c
  induction c
  case pure val =>
    intro τ hreach hb
    simp only [simulateQ_pure2]
    change
      ((cs τ).bind fun s => PMF.map Prod.fst (PMF.pure (val, s))) =
        PMF.map Prod.fst (PMF.pure (val, τ))
    simp [GameHoppingSimplifyPMF, PMF.bind_const]
  case roll q cont Hind =>
    cases q
    case oracle l =>
      intro τ hreach hb
      rw [FreeM.depth] at hb
      have h1 : lvl τ + 1 ≤ q_b := by
        refine le_trans ?_ hb; gcongr; exact le_self_add
      simp only [simulateQ_roll, addPMFtoImpl]
      simp only [bind, StateT.bind, StateT.run]
      simp only [PMF.map_bind]
      rw [← PMF.bind_bind, HSTEP l τ hreach h1, PMF.bind_bind]
      apply bindCongrOnSupport
      intro p hp
      rw [PMF.bind_map]
      obtain ⟨hlvl, hreach2⟩ := Hstep_reach l τ hreach h1 p hp
      have hbound : lvl p.2 + FreeM.depth (cont p.1) ≤ q_b := by
        rw [hlvl]
        calc lvl τ + 1 + FreeM.depth (cont p.1)
            = lvl τ + (1 + FreeM.depth (cont p.1)) := by rw [add_assoc]
          _ ≤ lvl τ + (1 + iSup (fun u => FreeM.depth (cont u))) := by
              gcongr; exact le_iSup (fun u => FreeM.depth (cont u)) p.1
          _ ≤ q_b := hb
      have hI := Hind p.1 p.2 hreach2 hbound
      simpa [Function.comp] using hI
    case sample l =>
      intro τ hreach hb
      rw [FreeM.depth] at hb
      simp only [simulateQ_roll, addPMFtoImpl]
      simp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, StateT.bind, StateT.run]
      simp only [PMF.bind_bind, PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.map_bind]
      rw [PMF.bind_comm]
      apply bindCongrOnSupport
      intro a ha
      have hbound : lvl τ + FreeM.depth (cont a) ≤ q_b := by
        refine le_trans ?_ hb; gcongr
        exact le_trans (le_iSup (fun u => FreeM.depth (cont u)) a) le_add_self
      exact Hind a τ hreach hbound


-- we want to reprove the following theorem:

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
