module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.SharpErrorWindowFluctuation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ErrorWindowGeneric
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseGamma

@[expose] public section

/-!
# The sharp fluctuation-scale bound

With the field-low slot at the sharp scale of `SharpFieldLowWindow.lean`, the
whole accumulated-error window fluctuation scale fits under the printed
coefficient of `e.cutoff.regularity.error.average`:

  `FluctScaleGen ≤ errorWindowScale M Cw s * √(m + 1 - n)`,
  `errorWindowScale M Cw s = Cw * s ^ (-7 / 2) * delta * √|log delta|`.

Appendix E of `provider-30` costed the five slots of the landed scale and found
four of them strictly inside the target, with only the field-low slot (`s ^ (-4)`)
outside.  With that slot repaired the arithmetic closes, and — worth recording —
it closes **without** the side condition `Kw * delta ^ 2 * |log delta| ≤ s` that
`CutoffParameterizedErrorWindowInput` carries.  That hypothesis existed only to
absorb the `s ^ (-1/2)` shortfall of the lossy field-low slot; the sharp slot
needs no absorption, so the bound here is unconditional on `0 < s ≤ 1`.

## Method

Write `u = (√s)⁻¹` and `v = s⁻¹`, so `s ^ (-7/2) = u * v ^ 3` and
`s ^ (-3/2) = u * v`.  Every model-dependent scale in the assembly is
`(a constant depending only on d) * M.delta`, and every `s`-dependence is a
monomial in `u` and `v` of total weight at most `7 / 2`.  Since `1 ≤ u`,
`1 ≤ v`, `1 ≤ √(m + 1 - n)` and `√(log 2) ≤ √|log delta|`, each slot is
dominated by `(constant) * u * v ^ 3 * delta * √|log delta| * √(m + 1 - n)`,
and the constants combine through the fixed `gammaTriangleConst` nesting.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## Real-power normalizations -/

theorem rpow_neg_seven_halves {s : ℝ} (hs : 0 < s) :
    s ^ (-7 / 2 : ℝ) = (Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 := by
  have hval : s ^ (7 / 2 : ℝ) = Real.sqrt s * s ^ 3 := by
    rw [show (7 / 2 : ℝ) = (1 / 2 : ℝ) + (3 : ℝ) by norm_num, Real.rpow_add hs,
      Real.sqrt_eq_rpow]
    congr 1
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [show (-7 / 2 : ℝ) = -(7 / 2 : ℝ) by norm_num, Real.rpow_neg hs.le, hval,
    mul_inv, inv_pow]

theorem rpow_neg_three_halves {s : ℝ} (hs : 0 < s) :
    s ^ (-3 / 2 : ℝ) = (Real.sqrt s)⁻¹ * s⁻¹ := by
  have hval : s ^ (3 / 2 : ℝ) = Real.sqrt s * s := by
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + (1 : ℝ) by norm_num, Real.rpow_add hs,
      Real.sqrt_eq_rpow, Real.rpow_one]
  rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg hs.le, hval,
    mul_inv]

theorem one_le_inv_sqrt {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (1 : ℝ) ≤ (Real.sqrt s)⁻¹ :=
  one_le_inv_iff₀.mpr ⟨Real.sqrt_pos.mpr hs, Real.sqrt_le_one.mpr hs1⟩

theorem one_le_inv {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) : (1 : ℝ) ≤ s⁻¹ :=
  one_le_inv_iff₀.mpr ⟨hs, hs1⟩

/-- `(√(s / 8))⁻¹ = √8 * (√s)⁻¹`. -/
theorem inv_sqrt_div_eight {s : ℝ} (hs : 0 < s) :
    (Real.sqrt (s / 8))⁻¹ = Real.sqrt 8 * (Real.sqrt s)⁻¹ := by
  rw [div_eq_mul_inv, Real.sqrt_mul hs.le, Real.sqrt_inv, mul_inv, inv_inv]
  ring

/-- `(s / 8)⁻¹ = 8 * s⁻¹`. -/
theorem inv_div_eight (s : ℝ) : (s / 8)⁻¹ = 8 * s⁻¹ := by
  rw [inv_div, div_eq_mul_inv]

/-! ## Model-scale factorizations

Each model-dependent scale is a `d`-constant times `M.delta`. -/

/-- The `d`-constant of `fieldOneGammaDimScale`. -/
def fieldOneGammaDimConst (d : ℕ) : ℝ :=
  ((d : ℝ) + 1) * Real.sqrt (shellCoverLogConst * (d : ℝ)) *
    (1 + Real.log 2) ^ (2 : ℝ)⁻¹

theorem fieldOneGammaDimScale_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    fieldOneGammaDimScale M = fieldOneGammaDimConst d * M.delta := by
  unfold fieldOneGammaDimScale fieldOneGammaDimConst
  ring

theorem fieldOneGammaDimConst_nonneg (d : ℕ) : 0 ≤ fieldOneGammaDimConst d := by
  unfold fieldOneGammaDimConst
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    (Real.rpow_nonneg hlog.le _)

/-- The `d`-constant of `fieldOneCubeMajorantScale M 0 0`. -/
def fieldOneCubeMajorantZeroConst (d : ℕ) : ℝ :=
  ((d : ℝ) + 1) *
    ((3 * Real.log
      ((shellCoverShifts d (((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ))).card : ℝ)) ^ (2 : ℝ)⁻¹ *
      (1 + Real.log 2) ^ (2 : ℝ)⁻¹)

theorem fieldOneCubeMajorantScale_zero_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    fieldOneCubeMajorantScale M 0 0 = fieldOneCubeMajorantZeroConst d * M.delta := by
  unfold fieldOneCubeMajorantScale fieldOneCubeMajorantZeroConst
  ring

theorem fieldOneCubeMajorantZeroConst_nonneg (d : ℕ) :
    0 ≤ fieldOneCubeMajorantZeroConst d := by
  unfold fieldOneCubeMajorantZeroConst
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  exact mul_nonneg (by positivity)
    (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg hlog.le _))

/-- The `d`-constant of `accumulatedGradientOwnRowScale`. -/
def gradientOwnRowConst (d : ℕ) : ℝ :=
  (d : ℝ) * (1 + Real.log 2) ^ (2 : ℝ)⁻¹

theorem accumulatedGradientOwnRowScale_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    accumulatedGradientOwnRowScale M = gradientOwnRowConst d * M.delta := by
  unfold accumulatedGradientOwnRowScale gradientOwnRowConst
  ring

theorem gradientOwnRowConst_nonneg (d : ℕ) : 0 ≤ gradientOwnRowConst d := by
  unfold gradientOwnRowConst
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  exact mul_nonneg (by positivity) (Real.rpow_nonneg hlog.le _)

theorem accumulatedGradientEnvelopeScale_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    accumulatedGradientEnvelopeScale M =
      IndependentSums.gammaTriangleConst 2 * (3 / 2 : ℝ) *
        (gradientOwnRowConst d * M.delta) := by
  unfold accumulatedGradientEnvelopeScale gradientOwnRowConst
  ring

/-- `accumulatedFiniteFieldScaleBound` in factored form. -/
theorem accumulatedFiniteFieldScaleBound_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ} (hs : 0 < s) :
    accumulatedFiniteFieldScaleBound M s =
      IndependentSums.gammaTriangleConst 2 *
        (fieldOneCubeMajorantZeroConst d * M.delta +
          16 * (fieldOneGammaDimConst d * M.delta) *
            (Real.sqrt 8 * (Real.sqrt s)⁻¹) * (8 * s⁻¹)) := by
  unfold accumulatedFiniteFieldScaleBound
  rw [fieldOneCubeMajorantScale_zero_eq, fieldOneGammaDimScale_eq,
    inv_sqrt_div_eight hs, inv_div_eight s]

/-- `sharpFieldLowColumnScaleSum` in factored form. -/
theorem sharpFieldLowColumnScaleSum_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ} (hs : 0 < s) :
    sharpFieldLowColumnScaleSum M s =
      IndependentSums.gammaTriangleConst 2 * (fieldOneGammaDimConst d * M.delta) *
        (32 * (Real.sqrt 8 * (Real.sqrt s)⁻¹) * (8 * s⁻¹) * (8 * s⁻¹)) := by
  unfold sharpFieldLowColumnScaleSum
  rw [fieldOneGammaDimScale_eq, inv_sqrt_div_eight hs, inv_div_eight s]

theorem ch04_gammaTriangleConst_two :
    Ch04.gammaTriangleConst 2 = IndependentSums.gammaTriangleConst 2 := rfl


/-! ## Pure monomial comparisons

Stated on plain real variables so their elaboration never touches the
model constants. -/

theorem one_le_pow_three {v : ℝ} (hv : 1 ≤ v) : (1 : ℝ) ≤ v ^ 3 := one_le_pow₀ hv

theorem pow_two_le_pow_three {v : ℝ} (hv : 1 ≤ v) : v ^ 2 ≤ v ^ 3 :=
  pow_le_pow_right₀ hv (by norm_num)

theorem self_le_pow_three {v : ℝ} (hv : 1 ≤ v) : v ≤ v ^ 3 := by
  simpa using pow_le_pow_right₀ hv (by norm_num : 1 ≤ 3)

/-- Attach a `√(m+1-n) ≥ 1` factor. -/
theorem monoAttachW {u v del Lam W : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hdel : 0 ≤ del) (hLam : 0 ≤ Lam) (hW : 1 ≤ W) :
    u * v ^ 3 * del * Lam ≤ u * v ^ 3 * del * Lam * W :=
  le_mul_of_one_le_right (by positivity) hW

/-- Raise `v ^ 2` to `v ^ 3`. -/
theorem monoRaiseTwo {u v del Lam W : ℝ} (hu : 0 ≤ u) (hv : 1 ≤ v)
    (hdel : 0 ≤ del) (hLam : 0 ≤ Lam) (hW : 0 ≤ W) :
    u * v ^ 2 * del * Lam * W ≤ u * v ^ 3 * del * Lam * W := by
  have hv0 : (0 : ℝ) ≤ v := by linarith
  have h := pow_two_le_pow_three hv
  have h1 : u * v ^ 2 ≤ u * v ^ 3 := mul_le_mul_of_nonneg_left h hu
  have h2 : u * v ^ 2 * del ≤ u * v ^ 3 * del := mul_le_mul_of_nonneg_right h1 hdel
  have h3 : u * v ^ 2 * del * Lam ≤ u * v ^ 3 * del * Lam :=
    mul_le_mul_of_nonneg_right h2 hLam
  exact mul_le_mul_of_nonneg_right h3 hW

/-- Insert the `√(log 2)` floor for a slot carrying no `√|log delta|`. -/
theorem monoInsertLog {u v del Lam W L0 : ℝ}
    (hL0 : 0 < L0) (hLam : L0 ≤ Lam)
    {X : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ u * v ^ 3 * del * W) :
    L0 * X ≤ u * v ^ 3 * del * Lam * W := by
  have hstep : L0 * X ≤ Lam * (u * v ^ 3 * del * W) :=
    mul_le_mul hLam hX hX0 (hL0.le.trans hLam)
  exact hstep.trans_eq (by ring)

theorem monoBaseW {u v del W : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hdel : 0 ≤ del) (hW : 0 ≤ W) : del * W ≤ u * v ^ 3 * del * W := by
  have hK : (1 : ℝ) ≤ u * v ^ 3 := by
    have h3 := one_le_pow_three hv
    nlinarith
  have h : del ≤ u * v ^ 3 * del := le_mul_of_one_le_left hdel hK
  exact mul_le_mul_of_nonneg_right h hW

theorem monoUV2 {u v del W : ℝ} (hu : 0 ≤ u) (hv : 1 ≤ v)
    (hdel : 0 ≤ del) (hW : 1 ≤ W) : u * v ^ 2 * del ≤ u * v ^ 3 * del * W := by
  have h1 : u * v ^ 2 * del ≤ u * v ^ 3 * del :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_two_le_pow_three hv) hu) hdel
  have hv0 : (0 : ℝ) ≤ v := by linarith
  exact h1.trans (le_mul_of_one_le_right (by positivity) hW)

theorem monoUV1W {u v del W : ℝ} (hu : 0 ≤ u) (hv : 1 ≤ v)
    (hdel : 0 ≤ del) (hW : 0 ≤ W) : u * v * del * W ≤ u * v ^ 3 * del * W := by
  have h1 : u * v ≤ u * v ^ 3 := mul_le_mul_of_nonneg_left (self_le_pow_three hv) hu
  have h2 : u * v * del ≤ u * v ^ 3 * del := mul_le_mul_of_nonneg_right h1 hdel
  exact mul_le_mul_of_nonneg_right h2 hW

theorem monoBase {u v del W : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hdel : 0 ≤ del) (hW : 1 ≤ W) : del ≤ u * v ^ 3 * del * W := by
  have hK : (1 : ℝ) ≤ u * v ^ 3 := by
    have h3 := one_le_pow_three hv
    nlinarith
  have h : del ≤ u * v ^ 3 * del := le_mul_of_one_le_left hdel hK
  exact h.trans (le_mul_of_one_le_right (by nlinarith [one_le_pow_three hv]) hW)

/-! ## The master monomial -/

/-- `s ^ (-7/2) * delta * √|log delta| * √(m + 1 - n)`, written multiplicatively. -/
def windowMasterScale {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s : ℝ) (n m : ℕ) : ℝ :=
  (Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta * Real.sqrt |Real.log M.delta| *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ)

theorem errorWindowScale_mul_sqrt_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {Cw s : ℝ} (hs : 0 < s) (n m : ℕ) :
    errorWindowScale M Cw s * Real.sqrt ((m + 1 - n : ℕ) : ℝ) =
      Cw * windowMasterScale M s n m := by
  unfold errorWindowScale windowMasterScale
  rw [rpow_neg_seven_halves hs]
  ring

/-- Divide a slot constant by the `√(log 2)` floor. -/
theorem slot_of_insertLog {C X Master L0 : ℝ} (hC : 0 ≤ C) (hL0 : 0 < L0)
    (h : L0 * X ≤ Master) : C * X ≤ C / L0 * Master := by
  rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
  calc C * X * L0 = C * (L0 * X) := by ring
    _ ≤ C * Master := mul_le_mul_of_nonneg_left h hC

/-! ## Slot constants -/

def responseSlotConst (d : ℕ) (Crow : ℝ) : ℝ :=
  (128 * IndependentSums.gammaTriangleConst 2 ^ 2 +
      16 * IndependentSums.gammaTriangleConst 2 ^ 2 * ((responseScoreRange d : ℕ) : ℝ) *
        Ch04.gammaSigmaIndependentSumConst 2 *
        (1 + IndependentSums.gammaMomentConst 2)) *
    (Real.exp 1 * Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow))

def fieldLowSlotConst (d : ℕ) : ℝ :=
  4096 * Real.sqrt 8 * IndependentSums.gammaTriangleConst 2 ^ 2 *
    fieldOneGammaDimConst d / Real.sqrt (Real.log 2)

def fieldActiveSlotConst (d : ℕ) : ℝ :=
  2 * Ch04.gammaSigmaIndependentSumConst 2 * (1 + IndependentSums.gammaMomentConst 2) *
      IndependentSums.gammaTriangleConst 2 * fieldOneCubeMajorantZeroConst d /
      Real.sqrt (Real.log 2) +
    256 * Ch04.gammaSigmaIndependentSumConst 2 *
      (1 + IndependentSums.gammaMomentConst 2) *
      IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 * fieldOneGammaDimConst d /
      Real.sqrt (Real.log 2)

def gradientActiveSlotConst (d : ℕ) : ℝ :=
  (3 / 2 : ℝ) * Ch04.gammaSigmaIndependentSumConst 2 *
    (1 + IndependentSums.gammaMomentConst 2) * gradientOwnRowConst d /
    Real.sqrt (Real.log 2)

def gradientTailSlotConst (d : ℕ) : ℝ :=
  (9 / 4 : ℝ) * IndependentSums.gammaTriangleConst 2 * gradientOwnRowConst d /
    Real.sqrt (Real.log 2)

/-! ## Common facts -/

theorem log_two_sqrt_pos : (0 : ℝ) < Real.sqrt (Real.log 2) :=
  Real.sqrt_pos.mpr (Real.log_pos (by norm_num))

theorem sqrt_log_two_le_sqrt_abs_log_delta {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    Real.sqrt (Real.log 2) ≤ Real.sqrt |Real.log M.delta| :=
  Real.sqrt_le_sqrt (log_two_le_abs_log_delta M)

theorem one_le_sqrt_window {n m : ℕ} (hnm : n ≤ m) :
    (1 : ℝ) ≤ Real.sqrt ((m + 1 - n : ℕ) : ℝ) := by
  have hnat : (1 : ℝ) ≤ ((m + 1 - n : ℕ) : ℝ) := by
    have h : 1 ≤ m + 1 - n := by omega
    exact_mod_cast h
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt hnat

/-! ## The five slot bounds -/

theorem gradientTailSlot_le {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {n m : ℕ} (hnm : n ≤ m) :
    (3 / 2 : ℝ) * accumulatedGradientEnvelopeScale M ≤
      gradientTailSlotConst d * windowMasterScale M s n m := by
  have hu := one_le_inv_sqrt hs hs1
  have hv := one_le_inv hs hs1
  have hW := one_le_sqrt_window (n := n) (m := m) hnm
  have hdel := M.shellPrefix.delta_pos
  have hL0 := log_two_sqrt_pos
  have hLam := sqrt_log_two_le_sqrt_abs_log_delta M
  have hT : (0:ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hcg := gradientOwnRowConst_nonneg d
  have hbase := monoInsertLog (u := (Real.sqrt s)⁻¹) (v := s⁻¹) (del := M.delta)
    (Lam := Real.sqrt |Real.log M.delta|)
    (W := Real.sqrt ((m + 1 - n : ℕ) : ℝ)) hL0 hLam hdel.le
    (monoBase hu hv hdel.le hW)
  have hC : (0:ℝ) ≤ (9 / 4 : ℝ) * IndependentSums.gammaTriangleConst 2 *
      gradientOwnRowConst d :=
    mul_nonneg (mul_nonneg (by norm_num) hT.le) hcg
  calc (3 / 2 : ℝ) * accumulatedGradientEnvelopeScale M
      = ((9 / 4 : ℝ) * IndependentSums.gammaTriangleConst 2 *
          gradientOwnRowConst d) * M.delta := by
        rw [accumulatedGradientEnvelopeScale_eq]; ring
    _ ≤ ((9 / 4 : ℝ) * IndependentSums.gammaTriangleConst 2 *
          gradientOwnRowConst d) / Real.sqrt (Real.log 2) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta *
            Real.sqrt |Real.log M.delta| *
            Real.sqrt ((m + 1 - n : ℕ) : ℝ)) := slot_of_insertLog hC hL0 hbase
    _ = gradientTailSlotConst d * windowMasterScale M s n m := by
        unfold gradientTailSlotConst windowMasterScale; ring

theorem gradientActiveSlot_le {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {n m : ℕ} (hnm : n ≤ m) :
    (3 / 2 : ℝ) * (Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
        ((1 + IndependentSums.gammaMomentConst 2) *
          accumulatedGradientOwnRowScale M)) ≤
      gradientActiveSlotConst d * windowMasterScale M s n m := by
  have hu := one_le_inv_sqrt hs hs1
  have hv := one_le_inv hs hs1
  have hW := one_le_sqrt_window (n := n) (m := m) hnm
  have hdel := M.shellPrefix.delta_pos
  have hL0 := log_two_sqrt_pos
  have hLam := sqrt_log_two_le_sqrt_abs_log_delta M
  have hIC : (0:ℝ) < Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hMo : (0:ℝ) < 1 + IndependentSums.gammaMomentConst 2 :=
    add_pos one_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hcg := gradientOwnRowConst_nonneg d
  have hbase := monoInsertLog (u := (Real.sqrt s)⁻¹) (v := s⁻¹) (del := M.delta)
    (Lam := Real.sqrt |Real.log M.delta|)
    (W := Real.sqrt ((m + 1 - n : ℕ) : ℝ)) hL0 hLam
    (by positivity) (monoBaseW hu hv hdel.le (by linarith))
  have hC : (0:ℝ) ≤ (3 / 2 : ℝ) * Ch04.gammaSigmaIndependentSumConst 2 *
      (1 + IndependentSums.gammaMomentConst 2) * gradientOwnRowConst d :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hIC.le) hMo.le) hcg
  calc (3 / 2 : ℝ) * (Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
          ((1 + IndependentSums.gammaMomentConst 2) *
            accumulatedGradientOwnRowScale M))
      = ((3 / 2 : ℝ) * Ch04.gammaSigmaIndependentSumConst 2 *
          (1 + IndependentSums.gammaMomentConst 2) * gradientOwnRowConst d) *
          (M.delta * Real.sqrt ((m + 1 - n : ℕ) : ℝ)) := by
        rw [accumulatedGradientOwnRowScale_eq]; ring
    _ ≤ ((3 / 2 : ℝ) * Ch04.gammaSigmaIndependentSumConst 2 *
          (1 + IndependentSums.gammaMomentConst 2) * gradientOwnRowConst d) /
          Real.sqrt (Real.log 2) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta *
            Real.sqrt |Real.log M.delta| *
            Real.sqrt ((m + 1 - n : ℕ) : ℝ)) := slot_of_insertLog hC hL0 hbase
    _ = gradientActiveSlotConst d * windowMasterScale M s n m := by
        unfold gradientActiveSlotConst windowMasterScale; ring

theorem fieldLowSlot_le {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {n m : ℕ} (hnm : n ≤ m) :
    2 * sharpFieldLowWindowScale M s ≤
      fieldLowSlotConst d * windowMasterScale M s n m := by
  have hu := one_le_inv_sqrt hs hs1
  have hv := one_le_inv hs hs1
  have hW := one_le_sqrt_window (n := n) (m := m) hnm
  have hdel := M.shellPrefix.delta_pos
  have hL0 := log_two_sqrt_pos
  have hLam := sqrt_log_two_le_sqrt_abs_log_delta M
  have hT : (0:ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hcD := fieldOneGammaDimConst_nonneg d
  have hS8 : (0:ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hbase := monoInsertLog (u := (Real.sqrt s)⁻¹) (v := s⁻¹) (del := M.delta)
    (Lam := Real.sqrt |Real.log M.delta|)
    (W := Real.sqrt ((m + 1 - n : ℕ) : ℝ)) hL0 hLam
    (by positivity) (monoUV2 (by linarith) hv hdel.le hW)
  have hC : (0:ℝ) ≤ 4096 * Real.sqrt 8 *
      IndependentSums.gammaTriangleConst 2 ^ 2 * fieldOneGammaDimConst d :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hS8.le) (by positivity)) hcD
  calc 2 * sharpFieldLowWindowScale M s
      = (4096 * Real.sqrt 8 * IndependentSums.gammaTriangleConst 2 ^ 2 *
          fieldOneGammaDimConst d) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 2 * M.delta) := by
        unfold sharpFieldLowWindowScale
        rw [sharpFieldLowColumnScaleSum_eq M hs]; ring
    _ ≤ (4096 * Real.sqrt 8 * IndependentSums.gammaTriangleConst 2 ^ 2 *
          fieldOneGammaDimConst d) / Real.sqrt (Real.log 2) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta *
            Real.sqrt |Real.log M.delta| *
            Real.sqrt ((m + 1 - n : ℕ) : ℝ)) := slot_of_insertLog hC hL0 hbase
    _ = fieldLowSlotConst d * windowMasterScale M s n m := by
        unfold fieldLowSlotConst windowMasterScale; ring

theorem fieldActiveSlot_le {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {n m : ℕ} (hnm : n ≤ m) :
    2 * (Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
        ((1 + IndependentSums.gammaMomentConst 2) *
          accumulatedFiniteFieldScaleBound M s)) ≤
      fieldActiveSlotConst d * windowMasterScale M s n m := by
  have hu := one_le_inv_sqrt hs hs1
  have hv := one_le_inv hs hs1
  have hW := one_le_sqrt_window (n := n) (m := m) hnm
  have hdel := M.shellPrefix.delta_pos
  have hL0 := log_two_sqrt_pos
  have hLam := sqrt_log_two_le_sqrt_abs_log_delta M
  have hT : (0:ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hIC : (0:ℝ) < Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hMo : (0:ℝ) < 1 + IndependentSums.gammaMomentConst 2 :=
    add_pos one_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hcD := fieldOneGammaDimConst_nonneg d
  have hc0 := fieldOneCubeMajorantZeroConst_nonneg d
  have hS8 : (0:ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hbase1 := monoInsertLog (u := (Real.sqrt s)⁻¹) (v := s⁻¹) (del := M.delta)
    (Lam := Real.sqrt |Real.log M.delta|)
    (W := Real.sqrt ((m + 1 - n : ℕ) : ℝ)) hL0 hLam
    (by positivity) (monoBaseW hu hv hdel.le (by linarith))
  have hbase2 := monoInsertLog (u := (Real.sqrt s)⁻¹) (v := s⁻¹) (del := M.delta)
    (Lam := Real.sqrt |Real.log M.delta|)
    (W := Real.sqrt ((m + 1 - n : ℕ) : ℝ)) hL0 hLam
    (by positivity) (monoUV1W (by linarith) hv hdel.le (by linarith))
  have hC1 : (0:ℝ) ≤ 2 * Ch04.gammaSigmaIndependentSumConst 2 *
      (1 + IndependentSums.gammaMomentConst 2) *
      IndependentSums.gammaTriangleConst 2 * fieldOneCubeMajorantZeroConst d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hIC.le) hMo.le) hT.le) hc0
  have hC2 : (0:ℝ) ≤ 256 * Ch04.gammaSigmaIndependentSumConst 2 *
      (1 + IndependentSums.gammaMomentConst 2) *
      IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 * fieldOneGammaDimConst d :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (by norm_num) hIC.le) hMo.le) hT.le) hS8.le) hcD
  have hstep1 := slot_of_insertLog hC1 hL0 hbase1
  have hstep2 := slot_of_insertLog hC2 hL0 hbase2
  calc 2 * (Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
          ((1 + IndependentSums.gammaMomentConst 2) *
            accumulatedFiniteFieldScaleBound M s))
      = (2 * Ch04.gammaSigmaIndependentSumConst 2 *
            (1 + IndependentSums.gammaMomentConst 2) *
            IndependentSums.gammaTriangleConst 2 *
            fieldOneCubeMajorantZeroConst d) *
          (M.delta * Real.sqrt ((m + 1 - n : ℕ) : ℝ)) +
        (256 * Ch04.gammaSigmaIndependentSumConst 2 *
            (1 + IndependentSums.gammaMomentConst 2) *
            IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
            fieldOneGammaDimConst d) *
          ((Real.sqrt s)⁻¹ * s⁻¹ * M.delta *
            Real.sqrt ((m + 1 - n : ℕ) : ℝ)) := by
        rw [accumulatedFiniteFieldScaleBound_eq M hs]; ring
    _ ≤ (2 * Ch04.gammaSigmaIndependentSumConst 2 *
            (1 + IndependentSums.gammaMomentConst 2) *
            IndependentSums.gammaTriangleConst 2 *
            fieldOneCubeMajorantZeroConst d) / Real.sqrt (Real.log 2) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta *
            Real.sqrt |Real.log M.delta| *
            Real.sqrt ((m + 1 - n : ℕ) : ℝ)) +
        (256 * Ch04.gammaSigmaIndependentSumConst 2 *
            (1 + IndependentSums.gammaMomentConst 2) *
            IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
            fieldOneGammaDimConst d) / Real.sqrt (Real.log 2) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta *
            Real.sqrt |Real.log M.delta| *
            Real.sqrt ((m + 1 - n : ℕ) : ℝ)) := add_le_add hstep1 hstep2
    _ = fieldActiveSlotConst d * windowMasterScale M s n m := by
        unfold fieldActiveSlotConst windowMasterScale; ring

theorem responseSlot_le {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {Crow s : ℝ} (hCrow : 0 < Crow) (hs : 0 < s) (hs1 : s ≤ 1)
    {n m : ℕ} (hnm : n ≤ m) :
    cutoffParameterizedAccumulatedResponseWindowFluctuationScale d s
        (Real.exp 1 * cutoffParameterizedResponseGammaScale M Crow s) n m ≤
      responseSlotConst d Crow * windowMasterScale M s n m := by
  have hu := one_le_inv_sqrt hs hs1
  have hv := one_le_inv hs hs1
  have hW := one_le_sqrt_window (n := n) (m := m) hnm
  have hdel := M.shellPrefix.delta_pos
  have hLam0 : (0:ℝ) ≤ Real.sqrt |Real.log M.delta| := Real.sqrt_nonneg _
  have hT : (0:ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hIC : (0:ℝ) < Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hMo : (0:ℝ) < 1 + IndependentSums.gammaMomentConst 2 :=
    add_pos one_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hcoeff : (0:ℝ) < cutoffParameterizedResponseGammaCoeff d Crow := by
    unfold cutoffParameterizedResponseGammaCoeff
    have hd : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hcA : (0:ℝ) ≤ Real.exp 1 *
      Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow) :=
    mul_nonneg (Real.exp_pos 1).le (Real.sqrt_nonneg _)
  have hRS : (0:ℝ) ≤ ((responseScoreRange d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA : Real.exp 1 * cutoffParameterizedResponseGammaScale M Crow s
      = (Real.exp 1 *
          Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow)) *
        ((Real.sqrt s)⁻¹ * s⁻¹) * M.delta * Real.sqrt |Real.log M.delta| := by
    rw [cutoffParameterizedResponseGammaScale_eq_rpow M hCrow hs,
      rpow_neg_three_halves hs]
    ring
  have hC1 : (0:ℝ) ≤ 128 * IndependentSums.gammaTriangleConst 2 ^ 2 *
      (Real.exp 1 * Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow)) :=
    mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hcA
  have hC2 : (0:ℝ) ≤ 16 * IndependentSums.gammaTriangleConst 2 ^ 2 *
      ((responseScoreRange d : ℕ) : ℝ) * Ch04.gammaSigmaIndependentSumConst 2 *
      (1 + IndependentSums.gammaMomentConst 2) *
      (Real.exp 1 * Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (by norm_num) (by positivity)) hRS) hIC.le) hMo.le) hcA
  have hstep1 := mul_le_mul_of_nonneg_left
    (monoAttachW (u := (Real.sqrt s)⁻¹) (v := s⁻¹) (del := M.delta)
      (Lam := Real.sqrt |Real.log M.delta|)
      (W := Real.sqrt ((m + 1 - n : ℕ) : ℝ))
      (by linarith) (by linarith) hdel.le hLam0 hW) hC1
  have hstep2 := mul_le_mul_of_nonneg_left
    (monoRaiseTwo (u := (Real.sqrt s)⁻¹) (v := s⁻¹) (del := M.delta)
      (Lam := Real.sqrt |Real.log M.delta|)
      (W := Real.sqrt ((m + 1 - n : ℕ) : ℝ))
      (by linarith) hv hdel.le hLam0 (by linarith)) hC2
  calc cutoffParameterizedAccumulatedResponseWindowFluctuationScale d s
        (Real.exp 1 * cutoffParameterizedResponseGammaScale M Crow s) n m
      = (128 * IndependentSums.gammaTriangleConst 2 ^ 2 *
            (Real.exp 1 *
              Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow))) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta *
            Real.sqrt |Real.log M.delta|) +
        (16 * IndependentSums.gammaTriangleConst 2 ^ 2 *
            ((responseScoreRange d : ℕ) : ℝ) *
            Ch04.gammaSigmaIndependentSumConst 2 *
            (1 + IndependentSums.gammaMomentConst 2) *
            (Real.exp 1 *
              Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow))) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 2 * M.delta *
            Real.sqrt |Real.log M.delta| *
            Real.sqrt ((m + 1 - n : ℕ) : ℝ)) := by
        unfold cutoffParameterizedAccumulatedResponseWindowFluctuationScale
        rw [hA]
        simp only [div_eq_mul_inv]
        ring
    _ ≤ (128 * IndependentSums.gammaTriangleConst 2 ^ 2 *
            (Real.exp 1 *
              Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow))) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta *
            Real.sqrt |Real.log M.delta| *
            Real.sqrt ((m + 1 - n : ℕ) : ℝ)) +
        (16 * IndependentSums.gammaTriangleConst 2 ^ 2 *
            ((responseScoreRange d : ℕ) : ℝ) *
            Ch04.gammaSigmaIndependentSumConst 2 *
            (1 + IndependentSums.gammaMomentConst 2) *
            (Real.exp 1 *
              Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow))) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta *
            Real.sqrt |Real.log M.delta| *
            Real.sqrt ((m + 1 - n : ℕ) : ℝ)) := add_le_add hstep1 hstep2
    _ = responseSlotConst d Crow * windowMasterScale M s n m := by
        unfold responseSlotConst windowMasterScale; ring

/-! ## The assembled bound -/

/-- Monotonicity of the fixed `gammaTriangleConst` nesting. -/
theorem nest_le {T r f fa ga gt r' f' fa' ga' gt' : ℝ} (hT : 0 ≤ T)
    (h1 : r ≤ r') (h2 : f ≤ f') (h3 : fa ≤ fa') (h4 : ga ≤ ga') (h5 : gt ≤ gt') :
    T * (T * (T * (T * (r + f) + fa) + ga) + gt) ≤
      T * (T * (T * (T * (r' + f') + fa') + ga') + gt') := by
  have e1 : r + f ≤ r' + f' := add_le_add h1 h2
  have e2 := add_le_add (mul_le_mul_of_nonneg_left e1 hT) h3
  have e3 := add_le_add (mul_le_mul_of_nonneg_left e2 hT) h4
  have e4 := add_le_add (mul_le_mul_of_nonneg_left e3 hT) h5
  exact mul_le_mul_of_nonneg_left e4 hT

/-- The constant of the sharp fluctuation-scale bound. -/
def sharpErrorWindowConst (d : ℕ) (Crow : ℝ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 *
    (IndependentSums.gammaTriangleConst 2 *
      (IndependentSums.gammaTriangleConst 2 *
        (IndependentSums.gammaTriangleConst 2 *
          (responseSlotConst d Crow + fieldLowSlotConst d) +
            fieldActiveSlotConst d) + gradientActiveSlotConst d) +
      gradientTailSlotConst d)

theorem sharpErrorWindowConst_pos {d : ℕ} {Crow : ℝ} (hCrow : 0 < Crow) :
    0 < sharpErrorWindowConst d Crow := by
  have hT : (0:ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hIC : (0:ℝ) < Ch04.gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_two_pos
  have hMo : (0:ℝ) < 1 + IndependentSums.gammaMomentConst 2 :=
    add_pos one_pos (IndependentSums.gammaMomentConst_pos (by norm_num))
  have hcoeff : (0:ℝ) < cutoffParameterizedResponseGammaCoeff d Crow := by
    unfold cutoffParameterizedResponseGammaCoeff
    have hd : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hL0 := log_two_sqrt_pos
  have hS8 : (0:ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hRS : (0:ℝ) ≤ ((responseScoreRange d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcD := fieldOneGammaDimConst_nonneg d
  have hc0 := fieldOneCubeMajorantZeroConst_nonneg d
  have hcg := gradientOwnRowConst_nonneg d
  have hR : 0 < responseSlotConst d Crow := by
    unfold responseSlotConst
    have hcA : (0:ℝ) < Real.exp 1 *
        Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow) :=
      mul_pos (Real.exp_pos 1) (Real.sqrt_pos.mpr hcoeff)
    have hfirst : (0:ℝ) < 128 * IndependentSums.gammaTriangleConst 2 ^ 2 := by
      positivity
    have hsecond : (0:ℝ) ≤ 16 * IndependentSums.gammaTriangleConst 2 ^ 2 *
        ((responseScoreRange d : ℕ) : ℝ) * Ch04.gammaSigmaIndependentSumConst 2 *
        (1 + IndependentSums.gammaMomentConst 2) := by positivity
    exact mul_pos (by linarith) hcA
  have hF : 0 ≤ fieldLowSlotConst d := by unfold fieldLowSlotConst; positivity
  have hFa : 0 ≤ fieldActiveSlotConst d := by
    unfold fieldActiveSlotConst
    have h1 : (0:ℝ) ≤ 2 * Ch04.gammaSigmaIndependentSumConst 2 *
        (1 + IndependentSums.gammaMomentConst 2) *
        IndependentSums.gammaTriangleConst 2 * fieldOneCubeMajorantZeroConst d /
        Real.sqrt (Real.log 2) := by positivity
    have h2 : (0:ℝ) ≤ 256 * Ch04.gammaSigmaIndependentSumConst 2 *
        (1 + IndependentSums.gammaMomentConst 2) *
        IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
        fieldOneGammaDimConst d / Real.sqrt (Real.log 2) := by positivity
    linarith
  have hGa : 0 ≤ gradientActiveSlotConst d := by
    unfold gradientActiveSlotConst; positivity
  have hGt : 0 ≤ gradientTailSlotConst d := by
    unfold gradientTailSlotConst; positivity
  unfold sharpErrorWindowConst
  have i1 : 0 < responseSlotConst d Crow + fieldLowSlotConst d := by linarith
  have i2 : 0 < IndependentSums.gammaTriangleConst 2 *
      (responseSlotConst d Crow + fieldLowSlotConst d) + fieldActiveSlotConst d := by
    have := mul_pos hT i1
    linarith
  have i3 : 0 < IndependentSums.gammaTriangleConst 2 *
      (IndependentSums.gammaTriangleConst 2 *
        (responseSlotConst d Crow + fieldLowSlotConst d) + fieldActiveSlotConst d) +
      gradientActiveSlotConst d := by
    have := mul_pos hT i2
    linarith
  have i4 : 0 < IndependentSums.gammaTriangleConst 2 *
      (IndependentSums.gammaTriangleConst 2 *
        (IndependentSums.gammaTriangleConst 2 *
          (responseSlotConst d Crow + fieldLowSlotConst d) +
            fieldActiveSlotConst d) + gradientActiveSlotConst d) +
      gradientTailSlotConst d := by
    have := mul_pos hT i3
    linarith
  exact mul_pos hT i4

/-- **The sharp fluctuation-scale bound.**  With the field-low slot at the sharp
scale of `SharpFieldLowWindow.lean`, the whole accumulated-error window
fluctuation scale is dominated by the printed coefficient
`Cw * s ^ (-7/2) * delta * √|log delta|` times `√(m + 1 - n)`.

There is **no** `Kw * delta ^ 2 * |log delta| ≤ s` side condition: that
hypothesis existed only to absorb the lossy field-low slot, and the sharp slot
needs no absorption. -/
theorem cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen_sharp_le
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {Crow s : ℝ}
    (hCrow : 0 < Crow) (hs : 0 < s) (hs1 : s ≤ 1) {n m : ℕ} (hnm : n ≤ m) :
    cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s
        (Real.exp 1 * cutoffParameterizedResponseGammaScale M Crow s) n m
        (sharpFieldLowWindowScale M s) ≤
      errorWindowScale M (sharpErrorWindowConst d Crow) s *
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) := by
  have hT : (0:ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have h1 := responseSlot_le M hCrow hs hs1 hnm
  have h2 := fieldLowSlot_le M hs hs1 hnm
  have h3 := fieldActiveSlot_le M hs hs1 hnm
  have h4 := gradientActiveSlot_le M hs hs1 hnm
  have h5 := gradientTailSlot_le M hs hs1 hnm
  rw [errorWindowScale_mul_sqrt_eq M hs]
  unfold cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen
  refine (nest_le hT.le h1 h2 h3 h4 h5).trans (le_of_eq ?_)
  unfold sharpErrorWindowConst
  ring

/-- Existential form, matching the shape of
`CutoffParameterizedErrorWindowInput`'s fluctuation half. -/
theorem exists_fluctuationScaleGen_sharp_le {d : ℕ} {Crow : ℝ} (hCrow : 0 < Crow) :
    ∃ Cw : ℝ, 0 < Cw ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ), 0 < s → s ≤ 1 →
        ∀ n m : ℕ, n ≤ m →
          cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s
              (Real.exp 1 * cutoffParameterizedResponseGammaScale M Crow s) n m
              (sharpFieldLowWindowScale M s) ≤
            errorWindowScale M Cw s * Real.sqrt ((m + 1 - n : ℕ) : ℝ) :=
  ⟨sharpErrorWindowConst d Crow, sharpErrorWindowConst_pos hCrow,
    fun M _ hs hs1 _ _ hnm ↦
      cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen_sharp_le
        M hCrow hs hs1 hnm⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
