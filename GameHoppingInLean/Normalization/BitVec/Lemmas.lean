import GameHoppingInLean.Normalization.BitVec.Attrs
import GameHoppingInLean.Normalization.PMF.Lemmas
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ToMathlib.General

@[GHSimpPMFBitVec]
theorem pmf_monad_bind_eq_bind {α β : Type u} (p : PMF α) (q : α → PMF β) :
    p >>= q = PMF.bind p q :=
  PMF.monad_bind_eq_bind p q

@[GHSimpPMFBitVec]
theorem bitVec_extractLsb'_cast_eq {n m start len : ℕ} (h : n = m) (x : BitVec n) :
    BitVec.extractLsb' start len (BitVec.cast h x) = BitVec.extractLsb' start len x := by
  cases h
  rfl

@[GHSimpPMFBitVec]
theorem bitVec_cast_symm_cast {n m : ℕ} (h : n = m) (x : BitVec n) :
    BitVec.cast h.symm (BitVec.cast h x) = x := by
  cases h
  rfl

@[GHSimpPMFBitVec]
theorem bitVec_cast_cast_symm {n m : ℕ} (h : n = m) (x : BitVec m) :
    BitVec.cast h (BitVec.cast h.symm x) = x := by
  cases h
  rfl

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

/-- Equivalence between `BitVec (k + k)` and `BitVec (2 * k)`. -/
def bitVecAddEquivTwoMul (k : ℕ) : BitVec (k + k) ≃ BitVec (2 * k) where
  toFun x := BitVec.cast (by simp [two_mul]) x
  invFun y := BitVec.cast (by simp [two_mul]) y
  left_inv := by intro x; simp
  right_inv := by intro y; simp

/-- Relating generic `cast` on `BitVec` to `BitVec.cast`. -/
theorem cast_congrArg_bitVec_eq_bitVec_cast {n m : ℕ} (h : n = m) (z : BitVec n) :
    (cast (congrArg BitVec h) z : BitVec m) = BitVec.cast h z := by
  cases h
  rfl

/-- Specialized cast-normalization for `BitVec (k + k)` to `BitVec (2 * k)`. -/
@[GHSimpPMFBitVec]
theorem cast_bitVec_two_mul_eq {k : ℕ} (z : BitVec (k + k)) :
    (cast (by simp [two_mul]) z : BitVec (2 * k)) = BitVec.cast (by simp [two_mul]) z := by
  have h : (k + k) = (2 * k) := by simp [two_mul]
  simpa [h] using (cast_congrArg_bitVec_eq_bitVec_cast (h := h) (z := z))

/-- The low `k` bits of `y ++ x` are exactly `x`. -/
@[GHSimpPMFBitVec]
theorem extractLsb'_zero_append_right {k m : ℕ}
    (x : BitVec k) (y : BitVec m) :
    BitVec.extractLsb' 0 k (y ++ x) = x := by
  rw [← BitVec.setWidth_eq_extractLsb' (x := y ++ x) (w := k) (h := by omega)]
  simp [BitVec.setWidth_append]

/-- The high `k` bits of `x ++ y` (starting at offset `m`) are exactly `x`. -/
@[GHSimpPMFBitVec]
theorem extractLsb'_append_high_right {k m : ℕ}
    (x : BitVec k) (y : BitVec m) :
    BitVec.extractLsb' m k (x ++ y) = x := by
  simpa using
    (BitVec.extractLsb'_append_eq_of_le
      (xhi := x) (xlo := y) (start := m) (len := k)
      (h := Nat.le_refl m))

theorem bind_uniformOfFintype_bitVec_cast {n m : ℕ} {α : Type}
    (h : n = m) (f : BitVec m → PMF α) :
    PMF.bind (PMF.uniformOfFintype (BitVec n))
      (fun x => f (BitVec.cast h x)) =
    PMF.bind (PMF.uniformOfFintype (BitVec m)) f := by
  cases h
  rfl

theorem bind_uniformOfFintype_bitVec_recast {n m : ℕ} {α : Type}
    (h : n = m) (f : BitVec n → PMF α) :
    PMF.bind (PMF.uniformOfFintype (BitVec n)) f =
    PMF.bind (PMF.uniformOfFintype (BitVec m)) (fun x => f (BitVec.cast h.symm x)) := by
  cases h
  rfl

/-- Rewrite a uniform draw over `BitVec (2 * k)` as the image of a uniform draw over
`BitVec (k + k)` through the standard width cast. -/
theorem uniformOfFintype_bitVec_two_mul_eq_map_cast {k : ℕ} :
    PMF.uniformOfFintype (BitVec (2 * k)) =
      (PMF.uniformOfFintype (BitVec (k + k))).map
        (BitVec.cast (by simp [two_mul]) : BitVec (k + k) → BitVec (2 * k)) := by
  simpa [bitVecAddEquivTwoMul] using
    (PMF.map_uniformOfFintype_equiv (e := bitVecAddEquivTwoMul k)).symm

/-- Two independent uniform bitvector draws, appended together, are the same as one
uniform draw at the appended width. -/
@[GHSimpPMFBitVec]
theorem bind_uniformOfFintype_bitVec_append_do
    {a b : ℕ} {α : Type} (f : BitVec (a + b) → PMF α) :
    (do
      let x₁ ← PMF.uniformOfFintype (BitVec a)
      let x₂ ← PMF.uniformOfFintype (BitVec b)
      f (x₁ ++ x₂)) =
    (do
      let x ← PMF.uniformOfFintype (BitVec (a + b))
      f x) := by
  change (PMF.uniformOfFintype (BitVec a)).bind
      (fun x₁ => (PMF.uniformOfFintype (BitVec b)).bind
        (fun x₂ => f (x₁ ++ x₂))) =
    (PMF.uniformOfFintype (BitVec (a + b))).bind f
  rw [← PMF.uniformOfFintype_prod_bind
    (f := fun p : BitVec a × BitVec b => f (p.1 ++ p.2))]
  exact (PMF.bind_uniformOfFintype_equiv
    (e := bitVecAppendEquiv a b)
    (g := f)).symm


theorem bind_uniformOfFintype_bitVec_append_rev
  {a b : ℕ} {α : Type} (f : BitVec (a + b) → PMF α) :
  (PMF.uniformOfFintype (BitVec (a + b))).bind f
  =
  (do
    let x₁ ← PMF.uniformOfFintype (BitVec a)
    let x₂ ← PMF.uniformOfFintype (BitVec b)
    f (x₁ ++ x₂))
  := by
    apply Eq.symm
    apply bind_uniformOfFintype_bitVec_append_do


/-- A uniform bitvector draw observed only through its high and low slices is equivalent
to two independent uniform bitvector draws. -/
@[GHSimpPMFBitVec]
theorem bind_uniformOfFintype_bitVec_extract_do
    {a b : ℕ} {α : Type} (f : BitVec a → BitVec b → PMF α) :
    (do
      let x ← PMF.uniformOfFintype (BitVec (a + b))
      f (BitVec.extractLsb' b a x) (BitVec.extractLsb' 0 b x)) =
    (do
      let x₁ ← PMF.uniformOfFintype (BitVec a)
      let x₂ ← PMF.uniformOfFintype (BitVec b)
      f x₁ x₂) := by
  rw [← bind_uniformOfFintype_bitVec_append_do
    (f := fun x => f (BitVec.extractLsb' b a x) (BitVec.extractLsb' 0 b x))]
  simp [GHSimpPMFBitVec]

/-- Raw `PMF.bind` form of `bind_uniformOfFintype_bitVec_extract_do`. -/
@[GHSimpPMFBitVec]
theorem bind_uniformOfFintype_bitVec_extract
    {a b : ℕ} {α : Type} (f : BitVec a → BitVec b → PMF α) :
    PMF.bind (PMF.uniformOfFintype (BitVec (a + b)))
      (fun x => f (BitVec.extractLsb' b a x) (BitVec.extractLsb' 0 b x)) =
    PMF.bind (PMF.uniformOfFintype (BitVec a))
      (fun x₁ => PMF.bind (PMF.uniformOfFintype (BitVec b))
        (fun x₂ => f x₁ x₂)) := by
  exact bind_uniformOfFintype_bitVec_extract_do f

/-- A uniform bitvector draw observed only through its low then high slices is equivalent
to two independent uniform bitvector draws. This is the orientation used by terms that
split `BitVec (a + b)` as `extractLsb' 0 a` and `extractLsb' a b`. -/
@[GHSimpPMFBitVec]
theorem bind_uniformOfFintype_bitVec_extract_low_high
    {a b : ℕ} {α : Type} (f : BitVec a → BitVec b → PMF α) :
    PMF.bind (PMF.uniformOfFintype (BitVec (a + b)))
      (fun x => f (BitVec.extractLsb' 0 a x) (BitVec.extractLsb' a b x)) =
    PMF.bind (PMF.uniformOfFintype (BitVec a))
      (fun x₁ => PMF.bind (PMF.uniformOfFintype (BitVec b))
        (fun x₂ => f x₁ x₂)) := by
  let hNat : b + a = a + b := Nat.add_comm b a
  let h : BitVec (b + a) = BitVec (a + b) := congrArg BitVec hNat
  calc
    PMF.bind (PMF.uniformOfFintype (BitVec (a + b)))
        (fun x => f (BitVec.extractLsb' 0 a x) (BitVec.extractLsb' a b x)) =
        PMF.bind (PMF.uniformOfFintype (BitVec (b + a)))
          (fun x => f (BitVec.extractLsb' 0 a ((Equiv.cast h) x))
            (BitVec.extractLsb' a b ((Equiv.cast h) x))) := by
          simpa using
            (PMF.bind_uniformOfFintype_equiv
              (e := Equiv.cast h)
              (g := fun x : BitVec (a + b) =>
                f (BitVec.extractLsb' 0 a x) (BitVec.extractLsb' a b x)))
    _ =
        PMF.bind (PMF.uniformOfFintype (BitVec (b + a)))
          (fun x => f (BitVec.extractLsb' 0 a x) (BitVec.extractLsb' a b x)) := by
          apply congrArg
            (fun g => PMF.bind (PMF.uniformOfFintype (BitVec (b + a))) g)
          funext x
          rw [show ((Equiv.cast h) x : BitVec (a + b)) = BitVec.cast hNat x by
            simpa [h, Equiv.cast] using
              cast_congrArg_bitVec_eq_bitVec_cast (h := hNat) (z := x)]
          simp [GHSimpPMFBitVec]
    _ =
        PMF.bind (PMF.uniformOfFintype (BitVec b))
          (fun y => PMF.bind (PMF.uniformOfFintype (BitVec a))
            (fun x => f x y)) := by
          exact bind_uniformOfFintype_bitVec_extract_do
            (a := b) (b := a)
            (f := fun y x => f x y)
    _ =
        PMF.bind (PMF.uniformOfFintype (BitVec a))
          (fun x => PMF.bind (PMF.uniformOfFintype (BitVec b))
            (fun y => f x y)) := by
          exact PMF.bind_comm (PMF.uniformOfFintype (BitVec b))
            (PMF.uniformOfFintype (BitVec a)) (fun y x => f x y)

/-- Raw PMF form for replacing a uniform `BitVec (2 * k)` draw by a uniform
`BitVec (k + k)` draw transported across the standard width cast. -/
@[GHSimpPMFBitVec]
theorem bind_uniformOfFintype_bitVec_two_mul_cast
    {k : ℕ} {α : Type} (f : BitVec (2 * k) → PMF α) :
    PMF.bind (PMF.uniformOfFintype (BitVec (k + k)))
      (fun x => f (BitVec.cast (by simp [two_mul]) x)) =
    PMF.bind (PMF.uniformOfFintype (BitVec (2 * k))) f := by
  simpa [bitVecAddEquivTwoMul] using
    (PMF.bind_uniformOfFintype_equiv
      (e := bitVecAddEquivTwoMul k)
      (g := f)).symm

/-- The `2 * k` specialization of `bind_uniformOfFintype_bitVec_extract_do`, transported
through the standard `BitVec (k + k) ≃ BitVec (2 * k)` cast. -/
theorem bind_uniformOfFintype_bitVec_two_mul_extract_do
    {k : ℕ} {α : Type} (f : BitVec k → BitVec k → PMF α) :
    (do
      let x ← PMF.uniformOfFintype (BitVec (2 * k))
      f (BitVec.extractLsb' k k x) (BitVec.extractLsb' 0 k x)) =
    (do
      let x₁ ← PMF.uniformOfFintype (BitVec k)
      let x₂ ← PMF.uniformOfFintype (BitVec k)
      f x₁ x₂) := by
  let h : k + k = 2 * k := by simp [two_mul]
  calc
    (do
      let x ← PMF.uniformOfFintype (BitVec (2 * k))
      f (BitVec.extractLsb' k k x) (BitVec.extractLsb' 0 k x)) =
        (do
          let x ← PMF.uniformOfFintype (BitVec (k + k))
          f (BitVec.extractLsb' k k (BitVec.cast h x))
            (BitVec.extractLsb' 0 k (BitVec.cast h x))) := by
          simpa [bitVecAddEquivTwoMul] using
            (PMF.bind_uniformOfFintype_equiv
              (e := bitVecAddEquivTwoMul k)
              (g := fun x : BitVec (2 * k) =>
                f (BitVec.extractLsb' k k x) (BitVec.extractLsb' 0 k x)))
    _ =
        (do
          let x ← PMF.uniformOfFintype (BitVec (k + k))
          f (BitVec.extractLsb' k k x) (BitVec.extractLsb' 0 k x)) := by
          simp [GHSimpPMFBitVec]
    _ =
        (do
          let x₁ ← PMF.uniformOfFintype (BitVec k)
          let x₂ ← PMF.uniformOfFintype (BitVec k)
          f x₁ x₂) := by
          exact bind_uniformOfFintype_bitVec_extract_do f
