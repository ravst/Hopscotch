import Hopscotch.Comp.StatefulRandomOracle
import Mathlib.Data.ENat.Lattice

/- # Query depth of free-monad computations -/

noncomputable def FreeM.depth.{uA, uB, uC}
    {P : PFunctor.{uA, uB}} {α : Type uC} : PFunctor.FreeM P α → ℕ∞
  | PFunctor.FreeM.pure _ => 0
  | PFunctor.FreeM.roll _input cont =>
      1 + iSup (fun u => depth (cont u))
