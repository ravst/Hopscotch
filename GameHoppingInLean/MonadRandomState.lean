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

@[simp] lemma liftM_bind {σ α β} (x : PMF α) (f : α → PMF β) :
    (liftM (x >>= f) : RState σ β) =
      ((liftM x : RState σ α) >>= fun a => (liftM (f a) : RState σ β)) := by
  ext s
  simp [StateT.lift, StateT.bind, PMF.bind_bind]

@[simp] lemma liftM_pmf_bind {σ α β} (x : PMF α) (f : α → PMF β) :
    (liftM (x.bind f) : RState σ β) =
      ((liftM x : RState σ α) >>= fun a => (liftM (f a) : RState σ β)) := by
  change (liftM (x >>= f) : RState σ β) =
      ((liftM x : RState σ α) >>= fun a => (liftM (f a) : RState σ β))
  simpa using (liftM_bind (σ := σ) (x := x) (f := f))

@[simp] lemma liftM_pure {σ α} (a : α) :
    (liftM (PMF.pure a) : RState σ α) = (pure a : RState σ α) := by
  funext s
  change StateT.run (StateT.lift (PMF.pure a)) s = StateT.run (pure a : RState σ α) s
  rw [StateT.run_lift, StateT.run_pure]
  simpa [PMF.monad_map_eq_map] using (map_pure (f := PMF) (g := fun a => (a, s)) a)

@[simp] lemma bind_liftM_pmf_bind {σ α β γ}
    (x : PMF α) (g : α → PMF β) (rest : β → RState σ γ) :
    ((liftM (x.bind g) : RState σ β) >>= rest) =
      ((liftM x : RState σ α) >>= fun z => (liftM (g z) : RState σ β) >>= rest) := by
  funext s
  change (((StateT.lift (x.bind g) : RState σ β) >>= rest).run s) =
    (((StateT.lift x : RState σ α) >>= fun z => (StateT.lift (g z) : RState σ β) >>= rest).run s)
  simp [StateT.run_bind, StateT.run_lift]
  convert (PMF.bind_bind (p := x) (f := g) (g := fun a => StateT.run (rest a) s)) using 1

@[simp] lemma do_liftM_pmf_bind {σ α β γ}
    (x : PMF α) (g : α → PMF β) (rest : β → RState σ γ) :
    (do
      let k ← (liftM (x.bind g) : RState σ β)
      rest k) =
    (do
      let x' ← (liftM x : RState σ α)
      let k ← (liftM (g x') : RState σ β)
      rest k) := by
  simpa using (bind_liftM_pmf_bind (σ := σ) (x := x) (g := g) (rest := rest))

@[simp] lemma bind_liftM_ignore {σ α β}
    (X : PMF α) (rest : RState σ β) :
    ((liftM X : RState σ α) >>= fun _ => rest) = rest := by
  funext s
  change StateT.run ((StateT.lift X : RState σ α) >>= fun _ => rest) s = StateT.run rest s
  rw [StateT.run_bind, StateT.run_lift]
  simp [PMF.bind_bind, PMF.bind_pure_comp]
  change X.bind (fun _ => StateT.run rest s) = StateT.run rest s
  rw [PMF.bind_const]

@[simp] lemma do_liftM_ignore {σ α β}
    (X : PMF α) (rest : RState σ β) :
    (do
      let _ ← (liftM X : RState σ α)
      rest) = rest := by
  simpa using (bind_liftM_ignore (σ := σ) (X := X) (rest := rest))

/-- Commuting two independent lifted `PMF` samples in `RState`.

Not marked `[simp]` to avoid commutativity rewrite loops. -/
lemma do_liftM_comm {σ α β γ}
    (A : PMF α) (B : PMF β) (rest : α → β → RState σ γ) :
    (do
      let x ← (liftM A : RState σ α)
      let y ← (liftM B : RState σ β)
      rest x y) =
    (do
      let y ← (liftM B : RState σ β)
      let x ← (liftM A : RState σ α)
      rest x y) := by
  funext s
  change StateT.run ((liftM A : RState σ α) >>= fun x => do
      let y ← (liftM B : RState σ β)
      rest x y) s =
    StateT.run ((liftM B : RState σ β) >>= fun y => do
      let x ← (liftM A : RState σ α)
      rest x y) s
  rw [StateT.run_bind, StateT.run_bind]
  simp [StateT.run_bind]
  simpa using (PMF.bind_comm (p := A) (q := B) (f := fun a b => StateT.run (rest a b) s))

noncomputable
def coinFlip {σ} : RState σ Bool :=
  StateT.lift (PMF.uniformOfFintype Bool)

end RState
