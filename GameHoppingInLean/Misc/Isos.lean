import Mathlib.Logic.Equiv.Prod

namespace Equiv

/-- `Unit` is a right identity for type product up to an equivalence. -/
@[simps]
def prodUnit (α : Type) : α × Unit ≃ α :=
  ⟨fun p => p.1, fun a => (a, ()), fun ⟨_, ()⟩ => rfl, fun _ => rfl⟩

/-- `Unit` is a left identity for type product up to an equivalence. -/
@[simps]
def unitProd (α : Type) : Unit × α ≃ α :=
  ⟨fun p => p.2, fun a => ((), a), fun ⟨(), _⟩ => rfl, fun _ => rfl⟩

end Equiv
