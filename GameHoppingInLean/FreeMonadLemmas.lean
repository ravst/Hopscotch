import GameHoppingInLean.VCVio2.ToMathlib.Control.FreeMonad

universe u v w

namespace FreeMonad

variable {f : Type u → Type v} {α : Type u}
variable {m : Type u → Type w} [Monad m]
variable (s : {β : Type u} → f β → m β)

@[simp] lemma mapM_ite (p : Prop) [Decidable p] (oa oa' : FreeMonad f α) :
    (if p then oa else oa').mapM s = if p then oa.mapM s else oa'.mapM s := by
  split_ifs <;> rfl

end FreeMonad
