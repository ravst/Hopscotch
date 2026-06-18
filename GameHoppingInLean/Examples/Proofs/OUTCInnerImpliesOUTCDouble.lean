import GameHoppingInLean.Examples.SecurityDefinitions.OTUC
import GameHoppingInLean.Examples.Constructions.DoubleSymEnc
import GameHoppingInLean.MonadRandomState
import GameHoppingInLean.PMFLiftOrder
import GameHoppingInLean.IndistinguishabilityTactics
import GameHoppingInLean.Misc.PMFLemmas

open scoped OracleReduction

attribute [local game_hopping_unfold] doubleSymEnc doubleSymEncFamily

@[local simp, local OracleReductionSimps]
theorem OTUCSpec_range_ctxt {C : ℕ → Type} {n : ℕ} (m : BitVec n) :
    (OTUCSpec C).Range (OTUCDomain.ctxt n m) = C n := rfl

@[local simp, local OracleReductionSimps]
theorem OTUCDomain_ctxt_fst {n : ℕ} (m : BitVec n) :
    (OTUCDomain.ctxt n m).1 = n := rfl

/-- `R1`: reduction from inner-OTUC (`T`) to outer-OTUC (`Double(S,T)`).
On query `m`, sample an `S` key, encrypt with `S`, then delegate to the input OTUC oracle. -/
@[game_hopping_unfold]
noncomputable def OUTCInner_to_OUTCDouble_R1 {K₁ : Type} {C : ℕ → Type}
    (S : SymEncScheme K₁ BitVec) : OracleReduction (OTUCSpec C) (OTUCSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := fun ⟨n, m⟩ => do
    let ks ← OracleReduction.sample S.keyGen
    let m' ← OracleReduction.sample (S.encrypt ks m)
    OracleReduction.query (OTUCDomain.ctxt n m')

/-- Explicit intermediate game `G1`:
sample an `S` key, encrypt the message with `S`, ignore that result, and output random ciphertext. -/
@[game_hopping_unfold]
noncomputable def OUTC_G1 {K₁ K₂ : Type} {C : ℕ → Type}
    [∀ n, Fintype (C n)] [∀ n, Nonempty (C n)]
    (S : SymEncScheme K₁ BitVec) (_T : SymEncScheme K₂ C) :
    RStateOracle (OTUCSpec C) where
  stateType := Unit
  initialState := pure ()
  queries := fun ⟨n, m⟩ => do
    let ks ← liftM S.keyGen
    let _m' ← liftM (S.encrypt ks m)
    PMF.uniformOfFintype (C n)



/-- OUTC/OTUC of inner scheme `T` implies OUTC/OTUC of `Double(S,T)`, via reduction `R1`. -/
noncomputable def outcInnerImpliesOutcDouble
    {K₁ K₂ : ℕ → Type} {C₂ : ℕ → ℕ → Type}
    (outerFam : SymEncSchemeFamily K₁ (fun _ => BitVec)) (innerFam : SymEncSchemeFamily K₂ C₂)
    [∀ κ n, Fintype (C₂ κ n)] [∀ κ n, Nonempty (C₂ κ n)] :
    OTUCIFam (OTUCAssumptionFam innerFam) (doubleSymEncFamily outerFam innerFam) := by
  intro κ
  let S := outerFam.scheme κ
  let T := innerFam.scheme κ
  game_hopping [
    OTUC_Real (doubleSymEnc S T),
    (OUTCInner_to_OUTCDouble_R1 S) ◇ (OTUC_Real T),
    (OUTCInner_to_OUTCDouble_R1 S) ◇ (OTUC_Rand T),
    OUTC_G1 S T,
    OTUC_Rand (doubleSymEnc S T)
  ]
