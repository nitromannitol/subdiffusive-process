module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.SharpFluctuationScaleBound

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## Monomial comparisons without the window factor -/

theorem monoInsertLogNoW {u v del Lam L0 : ℝ} (hL0 : 0 < L0) (hLam : L0 ≤ Lam)
    {X : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ u * v ^ 3 * del) :
    L0 * X ≤ u * v ^ 3 * del * Lam := by
  have hstep : L0 * X ≤ Lam * (u * v ^ 3 * del) :=
    mul_le_mul hLam hX hX0 (hL0.le.trans hLam)
  exact hstep.trans_eq (by ring)

theorem monoBaseNoW {u v del : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) (hdel : 0 ≤ del) :
    del ≤ u * v ^ 3 * del := by
  have hK : (1 : ℝ) ≤ u * v ^ 3 := by
    have h3 := one_le_pow_three hv
    nlinarith
  exact le_mul_of_one_le_left hdel hK

theorem monoUV1NoW {u v del : ℝ} (hu : 0 ≤ u) (hv : 1 ≤ v) (hdel : 0 ≤ del) :
    u * v * del ≤ u * v ^ 3 * del :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (self_le_pow_three hv) hu) hdel

theorem monoRaiseTwoNoW {u v del Lam : ℝ} (hu : 0 ≤ u) (hv : 1 ≤ v)
    (hdel : 0 ≤ del) (hLam : 0 ≤ Lam) :
    u * v ^ 2 * del * Lam ≤ u * v ^ 3 * del * Lam := by
  have h1 : u * v ^ 2 ≤ u * v ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_two_le_pow_three hv) hu
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h1 hdel) hLam

/-! ## The mean master monomial -/

/-- `s ^ (-7/2) * delta * √|log delta|`, written multiplicatively. -/
def windowMeanMasterScale {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) : ℝ :=
  (Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta * Real.sqrt |Real.log M.delta|

theorem errorWindowScale_eq_meanMaster {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {Cw s : ℝ} (hs : 0 < s) :
    errorWindowScale M Cw s = Cw * windowMeanMasterScale M s := by
  unfold errorWindowScale windowMeanMasterScale
  rw [rpow_neg_seven_halves hs]
  ring

/-! ## Slot constants -/

def meanResponseSlotConst (d : ℕ) (Crow : ℝ) : ℝ :=
  16 * IndependentSums.gammaMomentConst 2 *
    (Real.exp 1 * Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow))

def meanFieldSlotConst (d : ℕ) : ℝ :=
  2 * IndependentSums.gammaMomentConst 2 *
      IndependentSums.gammaTriangleConst 2 * fieldOneCubeMajorantZeroConst d /
      Real.sqrt (Real.log 2) +
    256 * IndependentSums.gammaMomentConst 2 *
      IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
      fieldOneGammaDimConst d / Real.sqrt (Real.log 2)

def meanGradientSlotConst (d : ℕ) : ℝ :=
  (3 / 2 : ℝ) * IndependentSums.gammaMomentConst 2 * gradientOwnRowConst d /
    Real.sqrt (Real.log 2)

/-- The constant of the mean half. -/
def sharpErrorWindowMeanConst (d : ℕ) (Crow : ℝ) : ℝ :=
  meanResponseSlotConst d Crow + meanFieldSlotConst d + meanGradientSlotConst d

theorem sharpErrorWindowMeanConst_pos {d : ℕ} {Crow : ℝ} (hCrow : 0 < Crow) :
    0 < sharpErrorWindowMeanConst d Crow := by
  have hmom : (0:ℝ) < IndependentSums.gammaMomentConst 2 :=
    IndependentSums.gammaMomentConst_pos (by norm_num)
  have hT : (0:ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hL0 := log_two_sqrt_pos
  have hS8 : (0:ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hcD := fieldOneGammaDimConst_nonneg d
  have hc0 := fieldOneCubeMajorantZeroConst_nonneg d
  have hcg := gradientOwnRowConst_nonneg d
  have hcoeff : (0:ℝ) < cutoffParameterizedResponseGammaCoeff d Crow := by
    unfold cutoffParameterizedResponseGammaCoeff
    have hd : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hR : 0 < meanResponseSlotConst d Crow := by
    unfold meanResponseSlotConst
    exact mul_pos (by positivity)
      (mul_pos (Real.exp_pos 1) (Real.sqrt_pos.mpr hcoeff))
  have hF : 0 ≤ meanFieldSlotConst d := by
    unfold meanFieldSlotConst
    have h1 : (0:ℝ) ≤ 2 * IndependentSums.gammaMomentConst 2 *
        IndependentSums.gammaTriangleConst 2 * fieldOneCubeMajorantZeroConst d /
        Real.sqrt (Real.log 2) := by positivity
    have h2 : (0:ℝ) ≤ 256 * IndependentSums.gammaMomentConst 2 *
        IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
        fieldOneGammaDimConst d / Real.sqrt (Real.log 2) := by positivity
    linarith
  have hG : 0 ≤ meanGradientSlotConst d := by
    unfold meanGradientSlotConst; positivity
  unfold sharpErrorWindowMeanConst
  linarith

/-! ## The three mean slots -/

theorem meanResponseSlot_le {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {Crow s : ℝ} (hCrow : 0 < Crow) (hs : 0 < s) (hs1 : s ≤ 1) :
    2 * (8 / s) * (IndependentSums.gammaMomentConst 2 *
        (Real.exp 1 * cutoffParameterizedResponseGammaScale M Crow s)) ≤
      meanResponseSlotConst d Crow * windowMeanMasterScale M s := by
  have hu := one_le_inv_sqrt hs hs1
  have hv := one_le_inv hs hs1
  have hdel := M.shellPrefix.delta_pos
  have hLam0 : (0:ℝ) ≤ Real.sqrt |Real.log M.delta| := Real.sqrt_nonneg _
  have hmom : (0:ℝ) < IndependentSums.gammaMomentConst 2 :=
    IndependentSums.gammaMomentConst_pos (by norm_num)
  have hcA : (0:ℝ) ≤ Real.exp 1 *
      Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow) :=
    mul_nonneg (Real.exp_pos 1).le (Real.sqrt_nonneg _)
  have hA : Real.exp 1 * cutoffParameterizedResponseGammaScale M Crow s
      = (Real.exp 1 *
          Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow)) *
        ((Real.sqrt s)⁻¹ * s⁻¹) * M.delta * Real.sqrt |Real.log M.delta| := by
    rw [cutoffParameterizedResponseGammaScale_eq_rpow M hCrow hs,
      rpow_neg_three_halves hs]
    ring
  have hC : (0:ℝ) ≤ 16 * IndependentSums.gammaMomentConst 2 *
      (Real.exp 1 * Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow)) :=
    mul_nonneg (by positivity) hcA
  calc 2 * (8 / s) * (IndependentSums.gammaMomentConst 2 *
          (Real.exp 1 * cutoffParameterizedResponseGammaScale M Crow s))
      = (16 * IndependentSums.gammaMomentConst 2 *
          (Real.exp 1 *
            Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow))) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 2 * M.delta *
            Real.sqrt |Real.log M.delta|) := by
        rw [hA]; simp only [div_eq_mul_inv]; ring
    _ ≤ (16 * IndependentSums.gammaMomentConst 2 *
          (Real.exp 1 *
            Real.sqrt (cutoffParameterizedResponseGammaCoeff d Crow))) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta *
            Real.sqrt |Real.log M.delta|) :=
        mul_le_mul_of_nonneg_left
          (monoRaiseTwoNoW (by linarith) hv hdel.le hLam0) hC
    _ = meanResponseSlotConst d Crow * windowMeanMasterScale M s := by
        unfold meanResponseSlotConst windowMeanMasterScale; ring

theorem meanFieldSlot_le {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    2 * (IndependentSums.gammaMomentConst 2 *
        accumulatedFiniteFieldScaleBound M s) ≤
      meanFieldSlotConst d * windowMeanMasterScale M s := by
  have hu := one_le_inv_sqrt hs hs1
  have hv := one_le_inv hs hs1
  have hdel := M.shellPrefix.delta_pos
  have hL0 := log_two_sqrt_pos
  have hLam := sqrt_log_two_le_sqrt_abs_log_delta M
  have hmom : (0:ℝ) < IndependentSums.gammaMomentConst 2 :=
    IndependentSums.gammaMomentConst_pos (by norm_num)
  have hT : (0:ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hS8 : (0:ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hcD := fieldOneGammaDimConst_nonneg d
  have hc0 := fieldOneCubeMajorantZeroConst_nonneg d
  have hbase1 := monoInsertLogNoW (u := (Real.sqrt s)⁻¹) (v := s⁻¹)
    (del := M.delta) (Lam := Real.sqrt |Real.log M.delta|) hL0 hLam
    hdel.le (monoBaseNoW hu hv hdel.le)
  have hbase2 := monoInsertLogNoW (u := (Real.sqrt s)⁻¹) (v := s⁻¹)
    (del := M.delta) (Lam := Real.sqrt |Real.log M.delta|) hL0 hLam
    (by positivity) (monoUV1NoW (by linarith) hv hdel.le)
  have hC1 : (0:ℝ) ≤ 2 * IndependentSums.gammaMomentConst 2 *
      IndependentSums.gammaTriangleConst 2 * fieldOneCubeMajorantZeroConst d :=
    mul_nonneg (mul_nonneg (by positivity) hT.le) hc0
  have hC2 : (0:ℝ) ≤ 256 * IndependentSums.gammaMomentConst 2 *
      IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
      fieldOneGammaDimConst d :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hT.le) hS8.le) hcD
  have hstep1 := slot_of_insertLog hC1 hL0 hbase1
  have hstep2 := slot_of_insertLog hC2 hL0 hbase2
  calc 2 * (IndependentSums.gammaMomentConst 2 *
          accumulatedFiniteFieldScaleBound M s)
      = (2 * IndependentSums.gammaMomentConst 2 *
            IndependentSums.gammaTriangleConst 2 *
            fieldOneCubeMajorantZeroConst d) * M.delta +
        (256 * IndependentSums.gammaMomentConst 2 *
            IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
            fieldOneGammaDimConst d) *
          ((Real.sqrt s)⁻¹ * s⁻¹ * M.delta) := by
        rw [accumulatedFiniteFieldScaleBound_eq M hs]; ring
    _ ≤ (2 * IndependentSums.gammaMomentConst 2 *
            IndependentSums.gammaTriangleConst 2 *
            fieldOneCubeMajorantZeroConst d) / Real.sqrt (Real.log 2) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta *
            Real.sqrt |Real.log M.delta|) +
        (256 * IndependentSums.gammaMomentConst 2 *
            IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
            fieldOneGammaDimConst d) / Real.sqrt (Real.log 2) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta *
            Real.sqrt |Real.log M.delta|) := add_le_add hstep1 hstep2
    _ = meanFieldSlotConst d * windowMeanMasterScale M s := by
        unfold meanFieldSlotConst windowMeanMasterScale; ring

theorem meanGradientSlot_le {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (3 / 2 : ℝ) * (IndependentSums.gammaMomentConst 2 *
        accumulatedGradientOwnRowScale M) ≤
      meanGradientSlotConst d * windowMeanMasterScale M s := by
  have hu := one_le_inv_sqrt hs hs1
  have hv := one_le_inv hs hs1
  have hdel := M.shellPrefix.delta_pos
  have hL0 := log_two_sqrt_pos
  have hLam := sqrt_log_two_le_sqrt_abs_log_delta M
  have hmom : (0:ℝ) < IndependentSums.gammaMomentConst 2 :=
    IndependentSums.gammaMomentConst_pos (by norm_num)
  have hcg := gradientOwnRowConst_nonneg d
  have hbase := monoInsertLogNoW (u := (Real.sqrt s)⁻¹) (v := s⁻¹)
    (del := M.delta) (Lam := Real.sqrt |Real.log M.delta|) hL0 hLam
    hdel.le (monoBaseNoW hu hv hdel.le)
  have hC : (0:ℝ) ≤ (3 / 2 : ℝ) * IndependentSums.gammaMomentConst 2 *
      gradientOwnRowConst d := mul_nonneg (by positivity) hcg
  calc (3 / 2 : ℝ) * (IndependentSums.gammaMomentConst 2 *
          accumulatedGradientOwnRowScale M)
      = ((3 / 2 : ℝ) * IndependentSums.gammaMomentConst 2 *
          gradientOwnRowConst d) * M.delta := by
        rw [accumulatedGradientOwnRowScale_eq]; ring
    _ ≤ ((3 / 2 : ℝ) * IndependentSums.gammaMomentConst 2 *
          gradientOwnRowConst d) / Real.sqrt (Real.log 2) *
          ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta *
            Real.sqrt |Real.log M.delta|) := slot_of_insertLog hC hL0 hbase
    _ = meanGradientSlotConst d * windowMeanMasterScale M s := by
        unfold meanGradientSlotConst windowMeanMasterScale; ring

/-! ## The mean half -/

/-- **The mean half of the window input.** -/
theorem cutoffParameterizedAccumulatedErrorWindowMeanBound_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {Crow s : ℝ}
    (hCrow : 0 < Crow) (hs : 0 < s) (hs1 : s ≤ 1) (n m : ℕ) :
    cutoffParameterizedAccumulatedErrorWindowMeanBound M s
        (Real.exp 1 * cutoffParameterizedResponseGammaScale M Crow s) n m ≤
      ((m + 1 - n : ℕ) : ℝ) *
        errorWindowScale M (sharpErrorWindowMeanConst d Crow) s := by
  have h1 := meanResponseSlot_le M hCrow hs hs1
  have h2 := meanFieldSlot_le (M := M) hs hs1
  have h3 := meanGradientSlot_le (M := M) hs hs1
  have hW : (0:ℝ) ≤ ((m + 1 - n : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold cutoffParameterizedAccumulatedErrorWindowMeanBound
  rw [errorWindowScale_eq_meanMaster M hs]
  refine mul_le_mul_of_nonneg_left ?_ hW
  refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
  unfold sharpErrorWindowMeanConst
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
