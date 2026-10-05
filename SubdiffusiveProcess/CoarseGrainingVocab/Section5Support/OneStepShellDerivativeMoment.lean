module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellW1pPackaging
public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity

@[expose] public section

/-!
# Fourth moments of the differentiated one-step shell block

The spatial derivative of shell `n + 1 + k`, measured in units of the
scale-`n` parent cube, carries the geometric weight `3^(-(k+1))`.  This file
packages the resulting finite `Gamma_2` envelope and proves its uniform
fourth-moment bound.  It is the stochastic half of the `delta^17` cell
estimate.
-/

open MeasureTheory Homogenization Homogenization.IndependentSums
open scoped BigOperators ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- The dimensionless derivative gauge of the last `h` shells on a
scale-`n` parent cube centered at `z`. -/
def oneStepShellDerivativeGauge {d : ℕ} (n h : ℕ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  ∑ k ∈ Finset.range h,
    ((3 : ℝ) ^ (k + 1))⁻¹ *
      translatedShellG2 (n + 1 + k)
        ((((3 : ℝ) ^ (n + 1 + k))⁻¹) • z) omega

theorem measurable_oneStepShellDerivativeGauge {d : ℕ}
    (n h : ℕ) (z : Vec d) :
    Measurable (oneStepShellDerivativeGauge (d := d) n h z) := by
  unfold oneStepShellDerivativeGauge
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.mul (measurable_translatedShellG2 _ _)

theorem oneStepShellDerivativeGauge_nonneg {d : ℕ}
    (n h : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ oneStepShellDerivativeGauge n h z omega := by
  unfold oneStepShellDerivativeGauge
  exact Finset.sum_nonneg fun k _ => mul_nonneg (by positivity)
    (translatedShellG2_nonneg _ _ _)

private theorem sum_range_inv_three_succ_eq (h : ℕ) :
    ∑ k ∈ Finset.range h, ((3 : ℝ) ^ (k + 1))⁻¹ =
      1 / 2 - (1 / 2) * ((3 : ℝ) ^ h)⁻¹ := by
  induction h with
  | zero => norm_num
  | succ h ih =>
      rw [Finset.sum_range_succ, ih]
      have hpow : ((3 : ℝ) ^ (h + 1))⁻¹ = ((3 : ℝ) ^ h)⁻¹ / 3 := by
        rw [pow_succ]
        have hne : (3 : ℝ) ^ h ≠ 0 := by positivity
        field_simp
      rw [hpow]
      ring

theorem sum_range_inv_three_succ_le_half (h : ℕ) :
    ∑ k ∈ Finset.range h, ((3 : ℝ) ^ (k + 1))⁻¹ ≤ 1 / 2 := by
  rw [sum_range_inv_three_succ_eq]
  have hnonneg : (0 : ℝ) ≤ ((3 : ℝ) ^ h)⁻¹ := by positivity
  linarith

/-- The geometric derivative envelope has a `Gamma_2` scale bounded
independently of the shell-block length. -/
theorem isBigO_oneStepShellDerivativeGauge {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (z : Vec d)
    (hh : 0 < h) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (oneStepShellDerivativeGauge n h z)
      (gammaTriangleConst 2 *
        ((∑ k ∈ Finset.range h, ((3 : ℝ) ^ (k + 1))⁻¹) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))) := by
  let s := Finset.range h
  let X : ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun k omega =>
    ((3 : ℝ) ^ (k + 1))⁻¹ *
      translatedShellG2 (n + 1 + k)
        ((((3 : ℝ) ^ (n + 1 + k))⁻¹) • z) omega
  let a : ℕ → ℝ := fun k =>
    ((3 : ℝ) ^ (k + 1))⁻¹ *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)
  have hs : s.Nonempty := by
    exact ⟨0, Finset.mem_range.mpr hh⟩
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  have ha : ∀ k ∈ s, 0 < a k := by
    intro k _
    dsimp [a]
    exact mul_pos (inv_pos.mpr (pow_pos (by norm_num) _))
      (mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos)
  have hX : ∀ k ∈ s,
      IsBigO M.P.toMeasure (gammaSigma 2) (X k) (a k) := by
    intro k _
    have hg := (isBigOWith_gammaTwo_translatedShellG2 M (n + 1 + k)
      ((((3 : ℝ) ^ (n + 1 + k))⁻¹) • z)).const_mul
        (show 0 ≤ ((3 : ℝ) ^ (k + 1))⁻¹ by positivity)
    rw [IsBigO]
    convert hg using 1
    funext omega
    rw [abs_of_nonneg]
    exact mul_nonneg (by positivity) (translatedShellG2_nonneg _ _ _)
  have hXm : ∀ k ∈ s, Measurable (X k) := by
    intro k _
    exact measurable_const.mul (measurable_translatedShellG2 _ _)
  have hsum := isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) s (by norm_num : (0 : ℝ) < 2) hs ha hX hXm
  have haSum : ∑ k ∈ s, a k =
      (∑ k ∈ Finset.range h, ((3 : ℝ) ^ (k + 1))⁻¹) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
    simp only [s, a, Finset.sum_mul]
  simpa only [oneStepShellDerivativeGauge, X, s, haSum] using! hsum

/-- Uniform fourth moment of the dimensionless differentiated-shell gauge. -/
theorem integral_oneStepShellDerivativeGauge_fourth_root_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (z : Vec d)
    (hh : 0 < h) :
    (∫ omega, |oneStepShellDerivativeGauge n h z omega| ^ (4 : ℝ)
        ∂M.P.toMeasure) ^ (4 : ℝ)⁻¹ ≤
      gammaMomentConst 2 * Real.sqrt 4 *
        (gammaTriangleConst 2 *
          ((1 / 2) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))) := by
  let A : ℝ := gammaTriangleConst 2 *
    ((∑ k ∈ Finset.range h, ((3 : ℝ) ^ (k + 1))⁻¹) *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))
  have hsumPos : 0 < ∑ k ∈ Finset.range h,
      ((3 : ℝ) ^ (k + 1))⁻¹ := by
    exact Finset.sum_pos' (fun _ _ => inv_nonneg.mpr (pow_nonneg (by norm_num) _))
      ⟨0, Finset.mem_range.mpr hh, inv_pos.mpr (pow_pos (by norm_num) _)⟩
  have hA : 0 < A := by
    dsimp [A]
    have hlog : 0 < 1 + Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    have htri : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
    exact mul_pos htri (mul_pos hsumPos
      (mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos))
  have hm := integral_abs_rpow_le_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (X := oneStepShellDerivativeGauge n h z)
    (K := A) (σ := 2) (p := 4) (by norm_num) hA (by norm_num)
    (measurable_oneStepShellDerivativeGauge n h z).aemeasurable
    (isBigO_oneStepShellDerivativeGauge M n h z hh)
  have hroot := Real.rpow_le_rpow
    (integral_nonneg fun omega => Real.rpow_nonneg (abs_nonneg _) _)
    hm (by positivity : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
  have hscale : A ≤ gammaTriangleConst 2 *
      ((1 / 2) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
    dsimp [A]
    apply mul_le_mul_of_nonneg_left _ (gammaTriangleConst_pos (σ := 2)).le
    apply mul_le_mul_of_nonneg_right (sum_range_inv_three_succ_le_half h)
    exact mul_nonneg (Real.rpow_nonneg (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _) M.shellPrefix.delta_pos.le
  calc
    (∫ omega, |oneStepShellDerivativeGauge n h z omega| ^ (4 : ℝ)
        ∂M.P.toMeasure) ^ (4 : ℝ)⁻¹ ≤
        ((gammaMomentConst 2 * (4 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (4 : ℝ)) ^
          (4 : ℝ)⁻¹ := hroot
    _ = gammaMomentConst 2 * Real.sqrt 4 * A := by
      have hbase : 0 < gammaMomentConst 2 * (4 : ℝ) ^ (2 : ℝ)⁻¹ * A := by
        exact mul_pos (mul_pos (gammaMomentConst_pos (by norm_num))
          (Real.rpow_pos_of_pos (by norm_num) _)) hA
      rw [← Real.rpow_mul hbase.le]
      rw [mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), Real.rpow_one]
      rw [show (4 : ℝ) ^ (2 : ℝ)⁻¹ = Real.sqrt 4 by
        rw [Real.sqrt_eq_rpow]
        congr 1
        norm_num]
    _ ≤ gammaMomentConst 2 * Real.sqrt 4 *
        (gammaTriangleConst 2 *
          ((1 / 2) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))) := by
      exact mul_le_mul_of_nonneg_left hscale
        (mul_nonneg (gammaMomentConst_pos (by norm_num)).le (Real.sqrt_nonneg _))

/-- The eighth moment used by Hölder against the lognormal multiplier. -/
theorem integral_oneStepShellDerivativeGauge_eighth_root_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (z : Vec d)
    (hh : 0 < h) :
    (∫ omega, |oneStepShellDerivativeGauge n h z omega| ^ (8 : ℝ)
        ∂M.P.toMeasure) ^ (8 : ℝ)⁻¹ ≤
      gammaMomentConst 2 * Real.sqrt 8 *
        (gammaTriangleConst 2 *
          ((1 / 2) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))) := by
  let A : ℝ := gammaTriangleConst 2 *
    ((∑ k ∈ Finset.range h, ((3 : ℝ) ^ (k + 1))⁻¹) *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))
  have hsumPos : 0 < ∑ k ∈ Finset.range h,
      ((3 : ℝ) ^ (k + 1))⁻¹ := by
    exact Finset.sum_pos' (fun _ _ => inv_nonneg.mpr (pow_nonneg (by norm_num) _))
      ⟨0, Finset.mem_range.mpr hh, inv_pos.mpr (pow_pos (by norm_num) _)⟩
  have hA : 0 < A := by
    dsimp [A]
    have hlog : 0 < 1 + Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    exact mul_pos (gammaTriangleConst_pos (σ := 2)) (mul_pos hsumPos
      (mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos))
  have hm := integral_abs_rpow_le_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (X := oneStepShellDerivativeGauge n h z)
    (K := A) (σ := 2) (p := 8) (by norm_num) hA (by norm_num)
    (measurable_oneStepShellDerivativeGauge n h z).aemeasurable
    (isBigO_oneStepShellDerivativeGauge M n h z hh)
  have hroot := Real.rpow_le_rpow
    (integral_nonneg fun omega => Real.rpow_nonneg (abs_nonneg _) _)
    hm (by positivity : (0 : ℝ) ≤ (8 : ℝ)⁻¹)
  have hscale : A ≤ gammaTriangleConst 2 *
      ((1 / 2) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
    dsimp [A]
    apply mul_le_mul_of_nonneg_left _ (gammaTriangleConst_pos (σ := 2)).le
    apply mul_le_mul_of_nonneg_right (sum_range_inv_three_succ_le_half h)
    exact mul_nonneg (Real.rpow_nonneg (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _) M.shellPrefix.delta_pos.le
  calc
    (∫ omega, |oneStepShellDerivativeGauge n h z omega| ^ (8 : ℝ)
        ∂M.P.toMeasure) ^ (8 : ℝ)⁻¹ ≤
        ((gammaMomentConst 2 * (8 : ℝ) ^ (2 : ℝ)⁻¹ * A) ^ (8 : ℝ)) ^
          (8 : ℝ)⁻¹ := hroot
    _ = gammaMomentConst 2 * Real.sqrt 8 * A := by
      have hbase : 0 < gammaMomentConst 2 * (8 : ℝ) ^ (2 : ℝ)⁻¹ * A := by
        exact mul_pos (mul_pos (gammaMomentConst_pos (by norm_num))
          (Real.rpow_pos_of_pos (by norm_num) _)) hA
      rw [← Real.rpow_mul hbase.le]
      rw [mul_inv_cancel₀ (by norm_num : (8 : ℝ) ≠ 0), Real.rpow_one]
      rw [show (8 : ℝ) ^ (2 : ℝ)⁻¹ = Real.sqrt 8 by
        rw [Real.sqrt_eq_rpow]
        congr 1
        norm_num]
    _ ≤ gammaMomentConst 2 * Real.sqrt 8 *
        (gammaTriangleConst 2 *
          ((1 / 2) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))) := by
      exact mul_le_mul_of_nonneg_left hscale
        (mul_nonneg (gammaMomentConst_pos (by norm_num)).le (Real.sqrt_nonneg _))

theorem memLp_eight_oneStepShellDerivativeGauge {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (z : Vec d)
    (hh : 0 < h) :
    MemLp (oneStepShellDerivativeGauge n h z) 8 M.P.toMeasure := by
  let A : ℝ := gammaTriangleConst 2 *
    ((∑ k ∈ Finset.range h, ((3 : ℝ) ^ (k + 1))⁻¹) *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))
  have hsumPos : 0 < ∑ k ∈ Finset.range h,
      ((3 : ℝ) ^ (k + 1))⁻¹ := by
    exact Finset.sum_pos' (fun _ _ => inv_nonneg.mpr (pow_nonneg (by norm_num) _))
      ⟨0, Finset.mem_range.mpr hh, inv_pos.mpr (pow_pos (by norm_num) _)⟩
  have hA : 0 < A := by
    dsimp [A]
    have hlog : 0 < 1 + Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    exact mul_pos (gammaTriangleConst_pos (σ := 2)) (mul_pos hsumPos
      (mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos))
  have hint : Integrable
      (fun omega => |oneStepShellDerivativeGauge n h z omega| ^ (8 : ℝ))
      M.P.toMeasure := by
    exact integrable_rpow_of_isBigOWith_gammaSigma
      (μ := M.P.toMeasure)
      (Y := fun omega => |oneStepShellDerivativeGauge n h z omega|)
      (K := A) (σ := 2) (p := 8) (by norm_num) hA (by norm_num)
      (fun _ => abs_nonneg _)
      (measurable_oneStepShellDerivativeGauge n h z).norm.aemeasurable
      (by simpa [IsBigO] using isBigO_oneStepShellDerivativeGauge M n h z hh)
  have h8zero : (8 : ℝ≥0∞) ≠ 0 := by norm_num
  have h8top : (8 : ℝ≥0∞) ≠ ∞ := by norm_num
  apply (integrable_norm_rpow_iff
    (measurable_oneStepShellDerivativeGauge n h z).aestronglyMeasurable
    h8zero h8top).1
  simpa [Real.norm_eq_abs] using! hint

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
