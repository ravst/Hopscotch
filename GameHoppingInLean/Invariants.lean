import GameHoppingInLean.Comp.StatefulRandomOracle
import GameHoppingInLean.ObservationalEquvialence
import Mathlib.Logic.Function.Basic

def incl {A : Type a} (phi : A -> Prop) (x : { x // phi x}) : A := x.1

noncomputable def invert {A} (phi : A -> Prop) [Nonempty { x // phi x }] : A -> {x//phi x} := Function.invFun (incl phi)


lemma SupportNonEmpty {A : Type} (p : PMF A) (phi : A -> Prop)
  (HInc : forall a : A, p a > 0 -> phi a) : Nonempty { x // phi x } := by
    simp []
    let ⟨a, b⟩ : p.support.Nonempty := PMF.support_nonempty p
    exists a
    simp [] at b
    apply HInc
    exact (PMF.apply_pos_iff p a).mpr b

-- noncomputable def invertToSupportO {A : Type} (p : PMF A) (phi : A -> Prop)
--   (HInc : forall a : A, p a > 0 -> phi a) : PMF { x // phi x} :=
-- by
--   have Hb : Nonempty { x // phi x } := SupportNonEmpty p phi HInc
--   exact (p.map (invert phi))

noncomputable def invertToSupport {A : Type} (p : PMF A) (phi : A -> Prop)
  (HInc : forall a : A, p a > 0 -> phi a) : PMF { x // phi x} :=
  p.bindOnSupport (fun x d =>
    PMF.pure {val:=x, property := HInc x ((PMF.apply_pos_iff p x).mpr d)})

lemma invertToSupportId {A : Type} (p : PMF A) (phi : A -> Prop)
  (HInc : forall a : A, p a > 0 -> phi a) : (invertToSupport p phi HInc).map (incl phi) = p := by
  simp [PMF.map, incl, invertToSupport, invert]
  have Hb : Nonempty { x // phi x } := SupportNonEmpty p phi HInc
  rw [<- PMF.bindOnSupport_eq_bind]
  rw [PMF.bindOnSupport_bindOnSupport]
  simp [incl]

-- lemma invertToSupportIdO {A : Type} (p : PMF A) (phi : A -> Prop)
--   (HInc : forall a : A, p a > 0 -> phi a) : (invertToSupportO p phi HInc).map (incl phi) = p := by
--   simp [PMF.map, incl, invertToSupportO, invert]
--   have Hb : Nonempty { x // phi x } := SupportNonEmpty p phi HInc
--   have H : forall a, p a > 0 -> ((incl phi) (Function.invFun (incl phi) a) = a) := by
--     intro a Ha
--     apply Function.invFun_eq
--     exact CanLift.prf a (HInc a Ha)
--   have Hc : forall a, a ∈ p.support -> ((Function.invFun (incl phi) a) = a) := by
--     intro a Ha
--     apply H
--     exact (PMF.apply_pos_iff p a).mpr Ha
--   rw [<- PMF.bindOnSupport_eq_bind]
--   conv =>
--     lhs
--     arg 2
--     intro a x
--     rw [Hc a x]
--   simp

noncomputable def addInvariantFunction (f : A -> PMF B) (phi : B -> Prop) (H : forall a x, f a x > 0 -> phi x) : (A -> PMF {x // phi x}) := fun a =>
  invertToSupport (f a) phi (H a)

lemma addInvariantFunctionComm (f : A -> PMF B) (phi : B -> Prop) (H : forall a x, f a x > 0 -> phi x)
  : forall a, (addInvariantFunction f phi H a).map (incl phi) = f a :=
by
  simp [addInvariantFunction]
  intro a
  rw [invertToSupportId]

def reduceElem {B C} {phi : C -> Prop} (elem : {e : (B × C) // phi e.2} ) : B × {x // phi x} := by
    let ⟨e, He⟩ := elem
    exact (e.1, ⟨e.2, He⟩)

noncomputable def addInvariantPair (p : PMF (B × C)) (phi : C -> Prop) (H : forall x, p x > 0 -> phi x.2) : (PMF (B × {x // phi x})) :=
  let x := invertToSupport p (fun (_b, c) => phi c) H
  x.map (reduceElem)

noncomputable def forgetInvFromPair {B C} (phi : C -> Prop) : B × { x // phi x } → B × C
  := fun (a, b) => (a, b.1)

noncomputable def addInvariantPairEq (p : PMF (B × C)) (phi : C -> Prop) (H : forall x, p x > 0 -> phi x.2) :
  (addInvariantPair p phi H).map (forgetInvFromPair phi) = p :=
by
  simp [addInvariantPair]
  conv =>
    lhs
    arg 2
    arg 1
    simp [reduceElem]
  rw [PMF.map_comp]
  conv =>
    lhs
    arg 1
    intro x
    simp [reduceElem]
  exact invertToSupportId p (fun x => phi x.2) (fun x Hx => H x Hx)


-- noncomputable def addInvariantFunction2 (f : A -> PMF (B × C)) (phi : C -> Prop) (H : forall a x, f a x > 0 -> phi x.2) : (A -> PMF (B × {x // phi x})) := fun a =>
--   addInvariantPair (f a) phi (H a)


-- noncomputable def addInvariantFunction2Eq (f : A -> PMF (B × C)) (phi : C -> Prop) {H : forall a x, f a x > 0 -> phi x.2} (a : A) :
--   (addInvariantFunction2 f phi H a).map (forgetInvFromPair phi) = f a :=
-- by
--   simp [addInvariantFunction2, addInvariantPairEq]


-- Now we introdcuce invarints to RStateOracle


def correctInvariantTrans {I : OracleSpec X} (O : RStateOracle I) (φ : O.stateType → Prop) : Prop :=
  forall {i : X} (s : O.stateType) (_hs : φ s) (q : I.domain i) (z : (I.range i) × O.stateType),
  let monadComp := (O.queries.impl i q)
  let outDistr := StateT.run monadComp s
  outDistr z > 0 -> φ z.2

def correctInvariantInit (O : RStateOracle I) (φ : O.stateType → Prop) : Prop :=
  forall x, O.initialState x > 0 -> φ x


def correctInvariant (O : RStateOracle I) (φ : O.stateType → Prop) : Prop :=
  correctInvariantTrans O φ ∧
  correctInvariantInit O φ

noncomputable def withInvariant (O : RStateOracle I) (φ : O.stateType → Prop) (H : correctInvariant O φ): RStateOracle I where
  stateType := {s : O.stateType | φ s}
  initialState := invertToSupport (O.initialState) φ H.2
  queries := {
    impl := (fun i q =>
      fun s => by
        let monadComp := O.queries.impl i q
        exact addInvariantPair (monadComp s) φ (fun z hz => H.1 s s.2 q z hz)
    )
  }

noncomputable def withInvMap (O : RStateOracle I) (φ : O.stateType → Prop)
  : {s : O.stateType | φ s} -> O.stateType
  := fun x => x.1

lemma invariantIsAbstraction (O : RStateOracle I) (φ : O.stateType → Prop) (H : correctInvariant O φ) :
  correctAbstraction (withInvariant O φ H) O (withInvMap O φ) := by
  simp [correctAbstraction]
  constructor
  · simp [withInvMap, withInvariant]
    apply invertToSupportId
  · intro i query
    simp [withInvariant, StateT.run, withInvMap, mapOutputState, mapInputState]
    ext1 n
    simp [mapOutputState, StateT.run]
    apply addInvariantPairEq


-- def fL {A B : Type} (H : A = B) (x : A) : B := H ▸ x
-- def fR {A B : Type} (H : A = B) (x : B) : A := (Eq.symm H) ▸ x

-- lemma fBij {A B : Type} (H : A = B) (x : A) : fR H (fL H x) = x :=
--   by
--     cases H
--     simp [fR, fL]

--     sorry

-- lemma eqWithInv {I : OracleSpec X} (O1 O2 : RStateOracle I)
--   (f : O2.stateType -> O1.stateType) (Hf : Function.Bijective f)
--   (φ : O1.stateType → Prop) (H : correctInvariant O1 φ)
--   (HInit : O2.initialState.map f = O1.initialState )
--   (HEq : forall α s (q : I.OracleQuery α),
--     φ (f s) ->  (O2.queries.impl q s).map (fun (a, b) => (a, f b)) = (O1.queries.impl q (f s)) ) :
--    correctInvariant O2 (fun x => φ (f x)) :=
-- by
--   -- have HRw : forall A B (H : A = B) (x : A), (Eq.symm H) ▸ (H ▸ x) = x := by
--   --   sorry
--   -- have HRw2 : forall {X A B : Type} (H : A = B) (x : PMF (X × B)), (H) ▸ ((Eq.symm  H) ▸ x) = x := by
--   --   sorry
--   -- have HEq2 :  forall α s, forall (q : I.OracleQuery α), φ (HState ▸ s) ->  (O2.queries.impl q s) = HState ▸ (O1.queries.impl q (HState ▸ s)) :=
--   -- by
--   --   intro a s q Hphi
--   --   rw [HEq]
--   --   rw [HRw]
--   --   -- apply [HRw2]
--   --   sorry
--   --   sorry
--   -- --
--     -- simp [HEq]

--   -- conv =>
--   --   rhs
--   --   arg 1
--   --   rw [HEq]

--   -- sorry
--   constructor
--   · simp [correctInvariantTrans]
--     intro α s Hphi q i s Hw
--     -- rw [HEq2] at Hw

--     sorry


--   · intro s Hphi
--     have HI : ((O2.initialState.map f) (f s) = O2.initialState s) :=
--     by

--       sorry
--     apply H.2
--     rw [<- HInit]
--     rw [HI]
--     assumption
