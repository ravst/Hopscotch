import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform

-- RState: state transformer over the probabilistic Pmf monad
abbrev RState (σ : Type _) (α : Type _) : Type _ := StateT σ PMF α

namespace RState

noncomputable
def run {σ α} (sd : PMF σ) (m : RState σ α) : PMF (α × σ) := do
  let s <- sd
  StateT.run m s

noncomputable
def eval {σ α} (s : PMF σ) (m : RState σ α) : PMF α :=
  (RState.run s m).map Prod.fst

noncomputable
def exec {σ α} (s : PMF σ) (m : RState σ α) : PMF σ :=
  (RState.run s m).map Prod.snd

@[simp] lemma run_pure {σ α} (sd : PMF σ) (a : α) :
    RState.run sd (pure a : RState σ α) = sd.map (fun s => (a, s)) := by
  simpa [PMF.monad_map_eq_map] using (by
    simp [RState.run, PMF.bind_pure_comp] : RState.run sd (pure a : RState σ α) = (Prod.mk a <$> sd))

@[simp] lemma eval_pure {σ α} (sd : PMF σ) (a : α) :
    RState.eval sd (pure a : RState σ α) = PMF.pure a := by
  rw [RState.eval, run_pure]
  rw [PMF.map_comp]
  simpa using (PMF.map_const (p := sd) (b := a))

@[simp] lemma exec_pure {σ α} (sd : PMF σ) (a : α) :
    RState.exec sd (pure a : RState σ α) = sd := by
  rw [RState.exec, run_pure]
  rw [PMF.map_comp]
  simpa using (PMF.map_id (p := sd))

@[simp] lemma run_bind {σ α β} (sd : PMF σ) (m : RState σ α) (f : α → RState σ β) :
    RState.run sd (m >>= f) = (RState.run sd m).bind (fun p => StateT.run (f p.1) p.2) := by
  change sd.bind (fun s => (StateT.run m s).bind (fun p => StateT.run (f p.1) p.2)) =
      (sd.bind fun s => StateT.run m s).bind (fun p => StateT.run (f p.1) p.2)
  exact (PMF.bind_bind (p := sd) (f := fun s => StateT.run m s)
    (g := fun p => StateT.run (f p.1) p.2)).symm

@[simp] lemma eval_bind {σ α β} (sd : PMF σ) (m : RState σ α) (f : α → RState σ β) :
    RState.eval sd (m >>= f) = (RState.run sd m).bind (fun p => (StateT.run (f p.1) p.2).map Prod.fst) := by
  rw [RState.eval, run_bind, PMF.map_bind]

@[simp] lemma exec_bind {σ α β} (sd : PMF σ) (m : RState σ α) (f : α → RState σ β) :
    RState.exec sd (m >>= f) = (RState.run sd m).bind (fun p => (StateT.run (f p.1) p.2).map Prod.snd) := by
  rw [RState.exec, run_bind, PMF.map_bind]

@[simp] lemma run_lift {σ α} (sd : PMF σ) (x : PMF α) :
    RState.run sd (StateT.lift x : RState σ α) = sd.bind (fun s => x.map (fun a => (a, s))) := by
  change sd.bind (fun s => (fun a => (a, s)) <$> x) = sd.bind (fun s => x.map (fun a => (a, s)))
  simp [PMF.monad_map_eq_map]

@[simp] lemma eval_lift {σ α} (sd : PMF σ) (x : PMF α) :
    RState.eval sd (StateT.lift x : RState σ α) = sd.bind (fun _ => x) := by
  rw [RState.eval, run_lift, PMF.map_bind]
  congr
  funext s
  rw [PMF.map_comp]
  simpa [Function.comp_def] using (PMF.map_id (p := x))

@[simp] lemma exec_lift {σ α} (sd : PMF σ) (x : PMF α) :
    RState.exec sd (StateT.lift x : RState σ α) = sd := by
  rw [RState.exec, run_lift, PMF.map_bind]
  have h : (fun s : σ => PMF.map Prod.snd (PMF.map (fun a => (a, s)) x)) = (PMF.pure ∘ (id : σ → σ)) := by
    funext s
    rw [PMF.map_comp]
    change PMF.map (Function.const α s) x = PMF.pure s
    exact PMF.map_const (p := x) (b := s)
  rw [h, PMF.bind_pure_comp]
  simpa using (PMF.map_id (p := sd))

noncomputable
def coinFlip {σ} : RState σ Bool :=
  StateT.lift (PMF.uniformOfFintype Bool)

end RState
