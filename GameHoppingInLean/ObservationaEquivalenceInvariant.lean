import GameHoppingInLean.ObservationalEquvialence
import GameHoppingInLean.Invariants

/-- `o₂` is equal to `o₁` on an invariant when `o₂`'s state can be identified with
the subset of `o₁` states satisfying some invariant `φ`, and one-step query semantics
agree after forgetting the invariant witness. -/
def OraclesEqualOnInvariant {I : Type} (O : OracleSpec I) (o₁ o₂ : RStateOracle O) (h_eq : o₁.stateType = o₂.stateType) (φ : o₁.stateType → Prop) : Prop :=
    o₁.initialState = h_eq ▸ o₂.initialState ∧
    ∀ (i : I) (t : O.domain i) (s : o₁.stateType),
      φ s →
      StateT.run (o₁.queries.impl i t) s =
      h_eq ▸ StateT.run (o₂.queries.impl i t) (h_eq ▸ s)

lemma oraclesEqualOnInvariant_preservesCorrectInvariant
    {I : Type} {O : OracleSpec I}
    {o₁ o₂ : RStateOracle O}
    (h_eq : o₁.stateType = o₂.stateType)
    (φ : o₁.stateType → Prop)
    (hInv₁ : correctInvariant o₁ φ)
    (hEqInv : OraclesEqualOnInvariant O o₁ o₂ h_eq φ) :
    correctInvariant o₂ (fun s => φ (h_eq.symm ▸ s)) := by
  cases o₁ with
  | mk S₁ init₁ queries₁ =>
      cases o₂ with
      | mk S₂ init₂ queries₂ =>
          cases h_eq
          simp [correctInvariant]
          simp [OraclesEqualOnInvariant] at hEqInv
          constructor
          · simp [correctInvariantTrans]
            intros a s q a₁ b hs hsup
            -- obtain ⟨x, y⟩ := a₁
            rw [← hEqInv.2] at hsup <;> try assumption
            simp [correctInvariant, correctInvariantTrans] at hInv₁
            apply hInv₁.1 <;> try assumption
          · simp [correctInvariantInit]
            rw[← hEqInv.1]
            simp [correctInvariant, correctInvariantInit] at hInv₁
            apply hInv₁.2

lemma oraclesEqualOnInvariant_implies_obsEq
    {I : Type} {O : OracleSpec I}
    {o₁ o₂ : RStateOracle O}
    (h_eq : o₁.stateType = o₂.stateType)
    (φ : o₁.stateType → Prop)
    (hInv₁ : correctInvariant o₁ φ)
    (hEqInv : OraclesEqualOnInvariant O o₁ o₂ h_eq φ) :
    ObsEq o₁ o₂ := by
  cases o₁ with
  | mk S₁ init₁ queries₁ =>
      cases o₂ with
      | mk S₂ init₂ queries₂ =>
          cases h_eq
          simp [OraclesEqualOnInvariant] at hEqInv
          rcases hEqInv with ⟨hInitEq, hQueryEq⟩
          let o₁' : RStateOracle O := { stateType := S₁, initialState := init₁, queries := queries₁ }
          let o₂' : RStateOracle O := { stateType := S₁, initialState := init₂, queries := queries₂ }
          have hInv₁' : correctInvariant o₁' φ := by
            simpa [o₁'] using hInv₁
          have hInitEq' : o₁'.initialState = o₂'.initialState := by
            simpa [o₁', o₂'] using hInitEq
          have hQueryEq' :
              ∀ (i : I) (t : O.domain i) (s : S₁),
                φ s →
                StateT.run (o₁'.queries.impl i t) s =
                StateT.run (o₂'.queries.impl i t) s := by
            intro i t s hs
            simpa [o₁', o₂'] using hQueryEq i t s hs
          have hQueryEqGen :
              ∀ {i} (q : O.domain i) (s : S₁),
                φ s →
                StateT.run (o₁'.queries.impl i q) s =
                StateT.run (o₂'.queries.impl i q) s := by
            intro i t s hs
            simpa using hQueryEq' i t s hs
          change ObsEq o₁' o₂'
          let w : RStateOracle O := withInvariant o₁' φ hInv₁'
          have hAbs₁ : correctAbstraction w o₁' (withInvMap o₁' φ) :=
            invariantIsAbstraction o₁' φ hInv₁'
          have hAbs₂ : correctAbstraction w o₂' (withInvMap o₁' φ) := by
            refine ⟨?_, ?_⟩
            · calc
                w.initialState.map (withInvMap o₁' φ) = o₁'.initialState := by
                  simpa [w] using hAbs₁.1
                _ = o₂'.initialState := hInitEq'
            · intro i query
              funext s
              have hw : (mapSecond (withInvMap o₁' φ)) <$> StateT.run (w.queries.impl i query) s =
                  StateT.run (o₁'.queries.impl i query) ((withInvMap o₁' φ) s) := by
                simpa [w] using congrArg (fun g => g s) (hAbs₁.2 i query)
              have hq : StateT.run (o₁'.queries.impl i query) ((withInvMap o₁' φ) s) =
                  StateT.run (o₂'.queries.impl i query) ((withInvMap o₁' φ) s) := by
                simpa [withInvMap] using hQueryEqGen query s.1 s.2
              exact hw.trans hq
          have hObs₁ : ObsEq w o₁' :=
            correctAbstractionImpliesObsEq w o₁' (withInvMap o₁' φ) hAbs₁
          have hObs₂ : ObsEq w o₂' :=
            correctAbstractionImpliesObsEq w o₂' (withInvMap o₁' φ) hAbs₂
          intro queriesList
          calc
            runQueries o₁' queriesList = runQueries w queriesList := (hObs₁ queriesList).symm
            _ = runQueries o₂' queriesList := hObs₂ queriesList
