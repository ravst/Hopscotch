import Mathlib.Algebra.Module.Defs
import Mathlib.Logic.Equiv.Defs

/-!
# Scalar coordinates relative to a generator

`CyclicGenerator F V g` states that `a ↦ a • g` is a bijection. For a module
over a field this describes a one-dimensional space with chosen basis vector.
When `F = ZMod q` for prime `q`, it is the additive presentation of a cyclic
group of order `q` with chosen generator. For a general finite field it need
not describe a cyclic additive group.

The coordinate function is mathematical data used in proofs; no efficient
algorithm for computing discrete logarithms is assumed.
-/

namespace Hopscotch

/-- Unique scalar coordinates relative to a chosen generator. -/
structure CyclicGenerator (F V : Type) [SMul F V] (g : V) where
  coordinate : V → F
  reconstruct : ∀ v, coordinate v • g = v
  coordinate_smul : ∀ a, coordinate (a • g) = a

namespace CyclicGenerator

/-- Scalar multiplication by the generator is an equivalence. -/
def toEquiv {F V : Type} [SMul F V] {g : V} (hg : CyclicGenerator F V g) : F ≃ V where
  toFun := fun a => a • g
  invFun := hg.coordinate
  left_inv := hg.coordinate_smul
  right_inv := hg.reconstruct

/-- A bijective scalar action supplies coordinates by classical choice. -/
noncomputable def ofBijective {F V : Type} [SMul F V] (g : V)
    (h : Function.Bijective (fun a : F => a • g)) : CyclicGenerator F V g where
  coordinate := (Equiv.ofBijective (fun a : F => a • g) h).symm
  reconstruct := (Equiv.ofBijective (fun a : F => a • g) h).apply_symm_apply
  coordinate_smul := (Equiv.ofBijective (fun a : F => a • g) h).symm_apply_apply

end CyclicGenerator

end Hopscotch
