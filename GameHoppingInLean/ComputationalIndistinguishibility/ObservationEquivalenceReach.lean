import GameHoppingInLean.ComputationalIndistinguishibility.AdversaryAdvantage
import GameHoppingInLean.ObservationalEq.Defs
import GameHoppingInLean.Tactic.SimpAttrLemmas
import Mathlib.Data.ENat.Lattice

/- # Definition of Abstraction with reachability and levels.
This version of abstraction is used in ObsEqComp.lean. It relates oracle implementation that track number of queries asked (exposed by function lvl) and accompanied by reachability function on its state space.
-/

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
    simp [sPMF, PMF.bind_const]
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
