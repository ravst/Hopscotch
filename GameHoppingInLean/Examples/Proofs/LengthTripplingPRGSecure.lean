import GameHoppingInLean.Examples.SecurityDefinitions.SecurePRG
import GameHoppingInLean.Examples.Constructions.LengthTripplingPRG
import GameHoppingInLean.Tactic.Defs
import GameHoppingInLean.Tactic.Normalization.BitVec.Simprocs
import GameHoppingInLean.Tactic.Normalization.BitVec.Lemmas


open scoped OracleReduction

/-- `R1`: from secure-PRG game on `2k` output to secure-PRG game on `3k` output.
On query, ask inner oracle for a `2k`-bit string `x || y`, then return `x || prg.draw y`. -/
@[local game_hopping_unfold]
def PRGDouble_to_Tripple_R1 {k : ℕ} (prg : lengthDoublingPRG k) :
    OracleReduction (SecurePRGSpec k k) (SecurePRGSpec k (2 * k)) where
  stateType := Unit
  initialState := pure ()
  queries := fun _ => do
    let xy ← OracleReduction.query ()
    let x : BitVec k := BitVec.extractLsb' k k xy
    let y : BitVec k := BitVec.extractLsb' 0 k xy
    let dy : BitVec (2 * k) := cast (by simp [two_mul]) (prg.draw y)
    pure (BitVec.append x dy)

/-- `R2`: from secure-PRG game on `2k` output to secure-PRG game on `3k` output.
On query, sample random `k` bits `x`, query inner oracle for `y : BitVec (2k)`,
and return `x || y`. -/
@[local game_hopping_unfold]
noncomputable def PRGDouble_to_Tripple_R2 {k : ℕ} :
    OracleReduction (SecurePRGSpec k k) (SecurePRGSpec k (2 * k)) where
  stateType := Unit
  initialState := pure ()
  queries := fun _ => do
    let x ← OracleReduction.sample (PMF.uniformOfFintype (BitVec k))
    let y : BitVec (k + k) ← OracleReduction.query ()
    let y' : BitVec (2 * k) := cast (by simp [two_mul]) y
    pure (BitVec.append x y')

/-- Explicit game `G1`: sample uniform `xy : BitVec (2k)`, split as `x || y`,
return `x || prg.draw y`. -/
@[local game_hopping_unfold]
noncomputable def PRG_G1 {k : ℕ} (prg : lengthDoublingPRG k) :
    RStateOracle (SecurePRGSpec k (2 * k)) where
  stateType := Unit
  initialState := pure ()
  queries := fun _ => do
    let xy ← PMF.uniformOfFintype (BitVec (k + k))
    let x : BitVec k := BitVec.extractLsb' k k xy
    let y : BitVec k := BitVec.extractLsb' 0 k xy
    let dy : BitVec (2 * k) := cast (by simp [two_mul]) (prg.draw y)
    pure (BitVec.append x dy)

/-- Explicit game `G2`: sample independent uniform `x,y : BitVec k`,
return `x || prg.draw y`. -/
@[local game_hopping_unfold]
noncomputable def PRG_G2 {k : ℕ} (prg : lengthDoublingPRG k) :
    RStateOracle (SecurePRGSpec k (2 * k)) where
  stateType := Unit
  initialState := pure ()
  queries := fun _ => do
    let x ← PMF.uniformOfFintype (BitVec k)
    let y ← PMF.uniformOfFintype (BitVec k)
    let dy : BitVec (2 * k) := cast (by simp [two_mul]) (prg.draw y)
    pure (BitVec.append x dy)

/-- Explicit game `G3`: sample independent uniform `x : BitVec k` and
`y : BitVec (2k)`, return `x || y`. -/
@[local game_hopping_unfold]
noncomputable def PRG_G3 {k : ℕ} :
    RStateOracle (SecurePRGSpec k (2 * k)) where
  stateType := Unit
  initialState := pure ()
  queries := fun _ => do
    let x ← PMF.uniformOfFintype (BitVec k)
    let y ← PMF.uniformOfFintype (BitVec (2 * k))
    pure (BitVec.append x y)

attribute [local game_hopping_unfold] LengthTripplingPRG LengthTripplingPRGFamily PRG_real PRG_rand
/-- Family version of length-tripling security from pointwise security of a
length-doubling PRG family. -/
noncomputable def secureLengthTripplingFam_of_secureLengthDoublingFam
    {k : ℕ → ℕ} (prgFam : lengthDoublingPRGFamily k) :
    SecurePRGIFam (SecurePRGAssumptionFam prgFam) (LengthTripplingPRGFamily prgFam) := by
  intro κ
  let prg := prgFam.prg κ
  game_hopping [
    PRG_real (LengthTripplingPRG prg),
    (PRGDouble_to_Tripple_R1 prg) ◇ (PRG_real prg),
    (PRGDouble_to_Tripple_R1 prg) ◇ (PRG_rand (k κ) (k κ)),
    PRG_G1 prg,
    PRG_G2 prg,
    (PRGDouble_to_Tripple_R2) ◇ (PRG_real prg),
    (PRGDouble_to_Tripple_R2) ◇ (PRG_rand (k κ) (k κ)),
    PRG_G3,
    PRG_rand (k κ) (2 * k κ)
  ] using GHSimpPMFBitVec
