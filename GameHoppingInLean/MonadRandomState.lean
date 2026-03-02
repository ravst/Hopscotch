import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform

-- RState: state transformer over the probabilistic Pmf monad
abbrev RState (σ : Type _) (α : Type _) : Type _ := StateT σ PMF α

namespace PMF

/-- Rewriting a uniform draw over a product type as two independent uniform draws. -/
@[simp] lemma uniformOfFintype_prod_bind
    {A B α : Type}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (f : A × B → PMF α) :
    (PMF.uniformOfFintype (A × B)).bind f =
      (PMF.uniformOfFintype A).bind (fun a =>
        (PMF.uniformOfFintype B).bind (fun b => f (a, b))) := by
  ext x
  have hprod :
      (∑' i : A × B, (f i) x) = ∑' i : A, ∑' j : B, (f (i, j)) x := by
    simpa using (ENNReal.tsum_prod' (f := fun p : A × B => (f p) x))
  simp [PMF.bind_apply, Fintype.card_prod, ENNReal.mul_inv, ENNReal.tsum_mul_left,
    mul_assoc, mul_left_comm, mul_comm, hprod]

end PMF

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

@[simp] lemma liftM_uniformOfFintype_prod
    {σ A B : Type}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] :
    (liftM (PMF.uniformOfFintype (A × B)) : RState σ (A × B)) =
      (liftM
        (do
          let a ← PMF.uniformOfFintype A
          let b ← PMF.uniformOfFintype B
          pure (a, b)) : RState σ (A × B)) := by
  have h :
      PMF.uniformOfFintype (A × B) =
        (do
          let a ← PMF.uniformOfFintype A
          let b ← PMF.uniformOfFintype B
          pure (a, b)) := by
    simpa using
      (PMF.uniformOfFintype_prod_bind (A := A) (B := B)
        (f := fun p : A × B => PMF.pure p))
  simp [h]

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

/-- Rewriting a lifted uniform draw over pairs as two lifted independent uniform draws. -/
@[simp] lemma do_liftM_uniformOfFintype_prod
    {σ A B α : Type}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (rest : A × B → RState σ α) :
    (do
      let p ← (liftM (PMF.uniformOfFintype (A × B)) : RState σ (A × B))
      rest p) =
    (do
      let a ← (liftM (PMF.uniformOfFintype A) : RState σ A)
      let b ← (liftM (PMF.uniformOfFintype B) : RState σ B)
      rest (a, b)) := by
  funext s
  change
    StateT.run (((liftM (PMF.uniformOfFintype (A × B)) : RState σ (A × B)) >>= fun p => rest p) :
      RState σ α) s =
      StateT.run (((liftM (PMF.uniformOfFintype A) : RState σ A) >>= fun a =>
        ((liftM (PMF.uniformOfFintype B) : RState σ B) >>= fun b => rest (a, b))) :
          RState σ α) s
  rw [StateT.run_bind, StateT.run_bind]
  simpa [StateT.run_lift, PMF.bind_bind]

/-- Transporting a uniform `PMF` sample across an equivalence. -/
lemma bind_uniformOfFintype_equiv {X Y α : Type}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (e : X ≃ Y) (g : Y → PMF α) :
    (PMF.uniformOfFintype Y).bind g =
      (PMF.uniformOfFintype X).bind (fun x => g (e x)) := by
  ext a
  have htsum :
      ∑' y : Y, ((Fintype.card Y : ENNReal)⁻¹ * (g y) a) =
        ∑' x : X, ((Fintype.card Y : ENNReal)⁻¹ * (g (e x)) a) := by
    simpa using
      (Equiv.tsum_eq e (fun y : Y => ((Fintype.card Y : ENNReal)⁻¹ * (g y) a))).symm
  calc
    ((PMF.uniformOfFintype Y).bind g) a =
        ∑' y : Y, ((Fintype.card Y : ENNReal)⁻¹ * (g y) a) := by
          simp [PMF.bind_apply, PMF.uniformOfFintype_apply]
    _ = ∑' x : X, ((Fintype.card Y : ENNReal)⁻¹ * (g (e x)) a) := htsum
    _ = ((PMF.uniformOfFintype X).bind (fun x => g (e x))) a := by
          simp [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_congr e]

/-- Transporting a lifted uniform sample across an equivalence in `RState`.

Not marked `[simp]`; use explicitly where needed. -/
lemma do_liftM_uniformOfFintype_equiv {σ X Y α : Type}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (e : X ≃ Y) (g : Y → RState σ α) :
    (do
      let y ← (liftM (PMF.uniformOfFintype Y) : RState σ Y)
      g y) =
    (do
      let x ← (liftM (PMF.uniformOfFintype X) : RState σ X)
      g (e x)) := by
  funext s
  change
    StateT.run (((liftM (PMF.uniformOfFintype Y) : RState σ Y) >>= fun y => g y) : RState σ α) s =
      StateT.run (((liftM (PMF.uniformOfFintype X) : RState σ X) >>= fun x => g (e x)) :
        RState σ α) s
  rw [StateT.run_bind, StateT.run_bind]
  simp [StateT.run_lift]
  simpa using bind_uniformOfFintype_equiv (e := e) (g := fun y => StateT.run (g y) s)

/-- Rewriting a lifted uniform sample via an equivalence, in direct `liftM` form. -/
lemma liftM_uniformOfFintype_equiv {σ X Y : Type}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (e : X ≃ Y) :
    (liftM (PMF.uniformOfFintype Y) : RState σ Y) =
      (liftM
        (do
          let x ← PMF.uniformOfFintype X
          pure (e x)) : RState σ Y) := by
  have h :
      PMF.uniformOfFintype Y =
        (do
          let x ← PMF.uniformOfFintype X
          pure (e x)) := by
    calc
      PMF.uniformOfFintype Y = (PMF.uniformOfFintype Y).bind PMF.pure := by simp
      _ = (PMF.uniformOfFintype X).bind (fun x => PMF.pure (e x)) := by
            simpa using (bind_uniformOfFintype_equiv (e := e) (g := PMF.pure))
      _ = (do
            let x ← PMF.uniformOfFintype X
            pure (e x)) := rfl
  simp [h]

/-- Equivalence between `(BitVec n × BitVec m)` and `BitVec (n + m)` via concatenation. -/
def bitVecAppendEquiv (n m : ℕ) : (BitVec n × BitVec m) ≃ BitVec (n + m) where
  toFun p := p.1 ++ p.2
  invFun z := (z.extractLsb' m n, z.setWidth m)
  left_inv := by
    intro p
    rcases p with ⟨x, y⟩
    apply Prod.ext
    · simpa using
        (BitVec.extractLsb'_append_eq_of_le
          (xhi := x) (xlo := y) (start := m) (len := n)
          (h := Nat.le_refl m))
    · simpa using (BitVec.setWidth_append (x := x) (y := y) (k := m))
  right_inv := by
    intro z
    apply BitVec.eq_of_getElem_eq
    intro i hi
    by_cases hlt : i < m
    · rw [BitVec.getElem_append (x := z.extractLsb' m n) (y := z.setWidth m) (h := hi)]
      simp [hlt]
      exact BitVec.getLsbD_eq_getElem (x := z) (i := i) hi
    · rw [BitVec.getElem_append (x := z.extractLsb' m n) (y := z.setWidth m) (h := hi)]
      simp [hlt]
      have hi' : m + (i - m) = i := by omega
      simpa [hi'] using
        (BitVec.getLsbD_eq_getElem (x := z) (i := m + (i - m)) (h := by omega))

/-- The low `k` bits of `y ++ x` are exactly `x`. -/
@[simp] lemma extractLsb'_zero_append_right {k m : ℕ}
    (x : BitVec k) (y : BitVec m) :
    BitVec.extractLsb' 0 k (y ++ x) = x := by
  rw [← BitVec.setWidth_eq_extractLsb' (x := y ++ x) (w := k) (h := by omega)]
  simp [BitVec.setWidth_append]

/-- The high `k` bits of `x ++ y` (starting at offset `m`) are exactly `x`. -/
@[simp] lemma extractLsb'_append_high_right {k m : ℕ}
    (x : BitVec k) (y : BitVec m) :
    BitVec.extractLsb' m k (x ++ y) = x := by
  simpa using
    (BitVec.extractLsb'_append_eq_of_le
      (xhi := x) (xlo := y) (start := m) (len := k)
      (h := Nat.le_refl m))

/-- Relating generic `cast` on `BitVec` to `BitVec.cast`. -/
lemma cast_congrArg_bitVec_eq_bitVec_cast {n m : ℕ} (h : n = m) (z : BitVec n) :
    (cast (congrArg BitVec h) z : BitVec m) = BitVec.cast h z := by
  cases h
  rfl

/-- Specialized cast-normalization for `BitVec (k + k)` to `BitVec (2 * k)`. -/
@[simp] lemma cast_bitVec_two_mul_eq {k : ℕ} (z : BitVec (k + k)) :
    (cast (by simp [two_mul]) z : BitVec (2 * k)) = BitVec.cast (by simp [two_mul]) z := by
  have h : (k + k) = (2 * k) := by simp [two_mul]
  simpa [h] using (cast_congrArg_bitVec_eq_bitVec_cast (h := h) (z := z))

/-- Direct `liftM` form of the append equivalence rewrite for `BitVec`. -/
@[simp] lemma liftM_uniformOfFintype_bitVec_append
    {σ : Type} {n m : ℕ}
    [Fintype (BitVec n)] [Nonempty (BitVec n)]
    [Fintype (BitVec m)] [Nonempty (BitVec m)]
    [Fintype (BitVec (n + m))] [Nonempty (BitVec (n + m))] :
    (liftM (PMF.uniformOfFintype (BitVec (n + m))) : RState σ (BitVec (n + m))) =
      (liftM
        (do
          let p ← PMF.uniformOfFintype (BitVec n × BitVec m)
          pure (p.1 ++ p.2)) : RState σ (BitVec (n + m))) := by
  simpa [bitVecAppendEquiv] using
    (liftM_uniformOfFintype_equiv (σ := σ)
      (X := BitVec n × BitVec m) (Y := BitVec (n + m))
      (e := bitVecAppendEquiv n m))

/-- Instantiation of `do_liftM_uniformOfFintype_equiv` for `BitVec` concatenation.

Not marked `[simp]`; use explicitly where needed. -/
lemma do_liftM_uniformOfFintype_bitVec_append
    {σ α : Type} {n m : ℕ}
    [Fintype (BitVec n)] [Nonempty (BitVec n)]
    [Fintype (BitVec m)] [Nonempty (BitVec m)]
    [Fintype (BitVec (n + m))] [Nonempty (BitVec (n + m))]
    (g : BitVec (n + m) → RState σ α) :
    (do
      let z ← (liftM (PMF.uniformOfFintype (BitVec (n + m))) : RState σ (BitVec (n + m)))
      g z) =
    (do
      let p ← (liftM (PMF.uniformOfFintype (BitVec n × BitVec m)) : RState σ (BitVec n × BitVec m))
      g (p.1 ++ p.2)) := by
  simpa [bitVecAppendEquiv] using
    (do_liftM_uniformOfFintype_equiv (σ := σ)
      (X := BitVec n × BitVec m) (Y := BitVec (n + m))
      (e := bitVecAppendEquiv n m) (g := g))

/-- Bind-form variant of `do_liftM_uniformOfFintype_bitVec_append`.

Not marked `[simp]`; use explicitly where needed. -/
lemma bind_uniformOfFintype_bitVec_append
    {σ α : Type} {n m : ℕ}
    [Fintype (BitVec n)] [Nonempty (BitVec n)]
    [Fintype (BitVec m)] [Nonempty (BitVec m)]
    [Fintype (BitVec (n + m))] [Nonempty (BitVec (n + m))]
    (g : BitVec (n + m) → RState σ α) :
    ((liftM (PMF.uniformOfFintype (BitVec (n + m))) : RState σ (BitVec (n + m))) >>= g) =
      ((liftM (PMF.uniformOfFintype (BitVec n × BitVec m)) : RState σ (BitVec n × BitVec m)) >>=
        fun p => g (p.1 ++ p.2)) := by
  simpa using do_liftM_uniformOfFintype_bitVec_append (σ := σ) (n := n) (m := m) (g := g)

/-- Equivalence between `BitVec (k + k)` and `BitVec (2 * k)`. -/
def bitVecAddEquivTwoMul (k : ℕ) : BitVec (k + k) ≃ BitVec (2 * k) where
  toFun x := BitVec.cast (by simp [two_mul]) x
  invFun y := BitVec.cast (by simp [two_mul]) y
  left_inv := by intro x; simp
  right_inv := by intro y; simp

/-- Rewriting uniform sampling on `BitVec (2 * k)` as sampling on `BitVec (k + k)`.

Marked `[simp]` so terms that sample `BitVec (2 * k)` can normalize to `k + k` shape. -/
@[simp] lemma do_liftM_uniformOfFintype_bitVec_two_mul
    {σ α : Type} {k : ℕ}
    [Fintype (BitVec (k + k))] [Nonempty (BitVec (k + k))]
    [Fintype (BitVec (2 * k))] [Nonempty (BitVec (2 * k))]
    (g : BitVec (2 * k) → RState σ α) :
    (do
      let y ← (liftM (PMF.uniformOfFintype (BitVec (2 * k))) : RState σ (BitVec (2 * k)))
      g y) =
    (do
      let x ← (liftM (PMF.uniformOfFintype (BitVec (k + k))) : RState σ (BitVec (k + k)))
      g (cast (by simp [two_mul]) x)) := by
  simpa [bitVecAddEquivTwoMul] using
    (do_liftM_uniformOfFintype_equiv (σ := σ)
      (X := BitVec (k + k)) (Y := BitVec (2 * k))
      (e := bitVecAddEquivTwoMul k) (g := g))

@[simp] lemma liftM_uniformOfFintype_bitVec_two_mul
    {σ : Type} {k : ℕ}
    [Fintype (BitVec (k + k))] [Nonempty (BitVec (k + k))]
    [Fintype (BitVec (2 * k))] [Nonempty (BitVec (2 * k))] :
    (liftM (PMF.uniformOfFintype (BitVec (2 * k))) : RState σ (BitVec (2 * k))) =
      (liftM
        (do
          let x ← PMF.uniformOfFintype (BitVec (k + k))
          pure (cast (by simp [two_mul]) x)) : RState σ (BitVec (2 * k))) := by
  simpa [bitVecAddEquivTwoMul] using
    (liftM_uniformOfFintype_equiv (σ := σ)
      (X := BitVec (k + k)) (Y := BitVec (2 * k))
      (e := bitVecAddEquivTwoMul k))

noncomputable
def coinFlip {σ} : RState σ Bool :=
  StateT.lift (PMF.uniformOfFintype Bool)

end RState
