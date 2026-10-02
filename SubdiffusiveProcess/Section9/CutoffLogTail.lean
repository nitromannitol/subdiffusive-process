/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import SubdiffusiveProcess.Section9.CutoffLowerTail
import SubdiffusiveProcess.Section9.CutoffSmallDisorderTail
import SubdiffusiveProcess.Assumptions.OGammaBridge
import Homogenization.Probability.IndependentSums.Triangle

/-! # Two-sided logarithmic tails for cutoff cube masses -/

namespace SubdiffusiveProcess.Section9

open MeasureTheory Homogenization Homogenization.IndependentSums
open SubdiffusiveProcess.Frozen.Assumptions

private theorem cutoffOriginCube_logLower_isBigO {d : ℕ} (M : GMCModel d)
    (m : ℕ) {cstar a : ℝ} (hcstar : 0 < cstar) (ha : 0 < a)
    (hlower : ∀ u : ℝ, Real.log 2 ≤ u →
      cutoffLowerTailSup M u ≤
        Real.exp (-a * smallDisorderExponent cstar M.delta * u)) :
    IsBigO M.P.toMeasure (gammaSigma 1)
      (fun omega ↦ max
        (-Real.log (cutoffOriginCubeAverage M m omega) - Real.log 2) 0)
      (1 / (a * smallDisorderExponent cstar M.delta)) := by
  have hp : 0 < smallDisorderExponent cstar M.delta := by
    have hlog : Real.log M.delta < 0 := Real.log_neg M.shellPrefix.delta_pos
      (lt_of_le_of_lt M.shellPrefix.delta_le_half (by norm_num))
    unfold smallDisorderExponent
    exact mul_pos (mul_pos hcstar (sq_pos_of_ne_zero (inv_ne_zero M.shellPrefix.delta_pos.ne')))
      (sq_pos_of_ne_zero (inv_ne_zero (abs_ne_zero.mpr hlog.ne)))
  have hA : 0 < 1 / (a * smallDisorderExponent cstar M.delta) := by positivity
  rw [isBigO_gammaSigma_iff]
  intro t ht
  let A : ℝ := 1 / (a * smallDisorderExponent cstar M.delta)
  let u : ℝ := Real.log 2 + A * t
  have hu : Real.log 2 ≤ u := le_add_of_nonneg_right (mul_nonneg hA.le (by linarith))
  have hsubset : absTailEvent
      (fun omega ↦ max
        (-Real.log (cutoffOriginCubeAverage M m omega) - Real.log 2) 0)
      (A * t) ⊆
      {omega | cutoffOriginCubeAverage M m omega ≤ Real.exp (-u)} := by
    intro omega homega
    have hAt : 0 < A * t := mul_pos hA (by linarith)
    have hmax : A * t <
        max (-Real.log (cutoffOriginCubeAverage M m omega) - Real.log 2) 0 := by
      change A * t < |max
        (-Real.log (cutoffOriginCubeAverage M m omega) - Real.log 2) 0| at homega
      rw [abs_of_nonneg (show 0 ≤ max
        (-Real.log (cutoffOriginCubeAverage M m omega) - Real.log 2) 0 from
          le_max_right _ _)] at homega
      exact homega
    have hlog : Real.log (cutoffOriginCubeAverage M m omega) < -u := by
      have hraw : 0 < -Real.log (cutoffOriginCubeAverage M m omega) - Real.log 2 := by
        by_contra h
        rw [max_eq_right (le_of_not_gt h)] at hmax
        linarith
      rw [max_eq_left hraw.le] at hmax
      dsimp only [u]
      linarith
    exact (Real.log_lt_iff_lt_exp (cutoffOriginCubeAverage_pos M m omega)).mp hlog |>.le
  have hmSup : M.P.toMeasure.real
      {omega | cutoffOriginCubeAverage M m omega ≤ Real.exp (-u)} ≤
      cutoffLowerTailSup M u := by
    unfold cutoffLowerTailSup
    exact le_ciSup (f := fun j : ℕ ↦ M.P.toMeasure.real {omega |
      cutoffOriginCubeAverage M j omega ≤ Real.exp (-u)})
      (⟨1, fun y hy ↦ by rcases hy with ⟨j, rfl⟩; exact measureReal_le_one⟩) m
  have htail := (measureReal_mono hsubset (measure_ne_top M.P.toMeasure _)).trans
    (hmSup.trans (hlower u hu))
  have hcancel : a * smallDisorderExponent cstar M.delta * (A * t) = t := by
    dsimp only [A]
    field_simp [ha.ne', hp.ne']
  calc
    M.P.toMeasure.real (absTailEvent
        (fun omega ↦ max
          (-Real.log (cutoffOriginCubeAverage M m omega) - Real.log 2) 0)
        ((1 / (a * smallDisorderExponent cstar M.delta)) * t))
        ≤ Real.exp (-a * smallDisorderExponent cstar M.delta * u) := htail
    _ ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by
      dsimp only [u]
      rw [mul_add]
      have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith [mul_nonneg (mul_nonneg ha.le hp.le) hlog, hcancel])
    _ = Real.exp (-(t ^ (1 : ℝ))) := by rw [Real.rpow_one]

/-- Actual finite-cutoff origin-cube logarithms obey the two-sided source-rate
Gamma-one estimate, uniformly in the cutoff scale. -/
theorem exists_cutoffOriginCube_logAbs_ogamma (d : ℕ) :
    ∃ C δzero : ℝ, 0 < C ∧ 0 < δzero ∧
      ∀ M : GMCModel d, M.delta ≤ δzero → ∀ m : ℕ,
        SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
          (C * M.delta ^ 2 * |Real.log M.delta| ^ 2)
          (fun omega ↦ |Real.log (cutoffOriginCubeAverage M m omega)| - Real.log 2) := by
  obtain ⟨cLower, a, δLower, hcLower, ha, hδLower, hlower⟩ :=
    exists_cutoffLowerTailSup_smallDisorder d
  obtain ⟨cUpper, δUpper, hcUpper, hδUpper, hupper⟩ :=
    exists_cutoffOriginCube_smallDisorder_tail d
  let cup : ℝ := 1 + Real.log 2
  let C : ℝ := 4 * gammaTriangleConst 1 *
    (cup / cUpper + (1 / a) / cLower)
  let δzero : ℝ := min (min δLower δUpper) (1 / 2)
  have hcup : 0 < cup := by dsimp only [cup]; positivity
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (mul_pos (by norm_num) (gammaTriangleConst_pos (σ := 1)))
      (add_pos (div_pos hcup hcUpper) (div_pos (one_div_pos.mpr ha) hcLower))
  have hδzero : 0 < δzero := lt_min (lt_min hδLower hδUpper) (by norm_num)
  refine ⟨C, δzero, hC, hδzero, ?_⟩
  intro M hM m
  have hMLower : M.delta ≤ δLower := hM.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hMUpper : M.delta ≤ δUpper := hM.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hMhalf : M.delta ≤ 1 / 2 := hM.trans (min_le_right _ _)
  obtain ⟨hpUpper, hUpper, -⟩ := hupper M hMUpper m
  have hpU : 0 < smallDisorderExponent cUpper M.delta := lt_of_lt_of_le (by norm_num) hpUpper
  have hpL : 0 < smallDisorderExponent cLower M.delta := by
    have hlog : Real.log M.delta < 0 := Real.log_neg M.shellPrefix.delta_pos
      (lt_of_le_of_lt hMhalf (by norm_num))
    unfold smallDisorderExponent
    exact mul_pos (mul_pos hcLower (sq_pos_of_ne_zero
      (inv_ne_zero M.shellPrefix.delta_pos.ne')))
      (sq_pos_of_ne_zero (inv_ne_zero (abs_ne_zero.mpr hlog.ne)))
  let Y : PotentialSample d → ℝ := fun omega ↦
    max (Real.log (cutoffOriginCubeAverage M m omega) - Real.log (9 / 8 : ℝ)) 0
  let X : PotentialSample d → ℝ := fun omega ↦
    max (-Real.log (cutoffOriginCubeAverage M m omega) - Real.log 2) 0
  have hYm : Measurable Y :=
    ((measurable_cutoffOriginCubeAverage M m).log.sub measurable_const).max measurable_const
  have hXm : Measurable X :=
    ((measurable_cutoffOriginCubeAverage M m).log.neg.sub measurable_const).max measurable_const
  have hUpperY : SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
      (smallDisorderExponent cUpper M.delta)⁻¹ Y := by
    simpa only [Y, SubdiffusiveProcess.OGammaLE, max_eq_left (le_max_right _ _)] using hUpper
  have hYbig : IsBigO M.P.toMeasure (gammaSigma 1) Y
      (cup * (smallDisorderExponent cUpper M.delta)⁻¹) := by
    simpa only [cup, inv_one, Real.rpow_one] using
      SubdiffusiveProcess.OGammaBridge.isBigO_gammaSigma_of_ogammaLE (by norm_num)
        (inv_pos.mpr hpU) (fun _ ↦ le_max_right _ _) hUpperY
  have hXbig : IsBigO M.P.toMeasure (gammaSigma 1) X
      (1 / (a * smallDisorderExponent cLower M.delta)) :=
    cutoffOriginCube_logLower_isBigO M m hcLower ha (hlower M hMLower)
  let Z : Fin 2 → PotentialSample d → ℝ := fun i ↦ if i = 0 then Y else X
  let s : Finset (Fin 2) := Finset.univ
  let scale : Fin 2 → ℝ := fun i ↦ if i = 0 then
    cup * (smallDisorderExponent cUpper M.delta)⁻¹ else
      1 / (a * smallDisorderExponent cLower M.delta)
  have hsum : IsBigO M.P.toMeasure (gammaSigma 1) (fun omega ↦ Y omega + X omega)
      (gammaTriangleConst 1 *
        (cup * (smallDisorderExponent cUpper M.delta)⁻¹ +
          1 / (a * smallDisorderExponent cLower M.delta))) := by
    have hscalePos : ∀ i ∈ s, 0 < scale i := by
      intro i hi
      fin_cases i
      · simp only [scale]
        positivity
      · simp only [scale]
        positivity
    have hfamily : ∀ i ∈ s,
        IsBigO M.P.toMeasure (gammaSigma 1) (Z i) (scale i) := by
      intro i hi
      fin_cases i
      · simpa only [Z, scale, if_true] using hYbig
      · simpa only [Z, scale, one_ne_zero, if_false] using hXbig
    have hfamilyMeas : ∀ i ∈ s, Measurable (Z i) := by
      intro i hi
      fin_cases i
      · simpa only [Z, if_true] using hYm
      · simpa only [Z, one_ne_zero, if_false] using hXm
    have hsumRaw := isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := M.P.toMeasure) (X := Z) (a := scale) (σ := (1 : ℝ)) s
      (by norm_num) Finset.univ_nonempty hscalePos hfamily hfamilyMeas
    simpa only [Z, s, scale, Fin.sum_univ_two, Fin.isValue, if_true,
      one_ne_zero, if_false] using hsumRaw
  have hWm : Measurable (fun omega ↦
      max (|Real.log (cutoffOriginCubeAverage M m omega)| - Real.log 2) 0) :=
    ((measurable_cutoffOriginCubeAverage M m).log.norm.sub measurable_const).max measurable_const
  have hWle : ∀ omega, max (|Real.log (cutoffOriginCubeAverage M m omega)| -
      Real.log 2) 0 ≤ Y omega + X omega := by
    intro omega
    dsimp only [Y, X]
    apply max_le
    · by_cases hz : 0 ≤ Real.log (cutoffOriginCubeAverage M m omega)
      · rw [abs_of_nonneg hz]
        have hlog : Real.log (9 / 8 : ℝ) ≤ Real.log 2 :=
          Real.log_le_log (by norm_num) (by norm_num)
        calc
          Real.log (cutoffOriginCubeAverage M m omega) - Real.log 2
              ≤ Real.log (cutoffOriginCubeAverage M m omega) - Real.log (9 / 8 : ℝ) :=
            sub_le_sub_left hlog _
          _ ≤ max (Real.log (cutoffOriginCubeAverage M m omega) -
              Real.log (9 / 8 : ℝ)) 0 := le_max_left _ _
          _ ≤ max (Real.log (cutoffOriginCubeAverage M m omega) -
              Real.log (9 / 8 : ℝ)) 0 +
              max (-Real.log (cutoffOriginCubeAverage M m omega) - Real.log 2) 0 :=
            le_add_of_nonneg_right (le_max_right _ _)
      · rw [abs_of_nonpos (le_of_not_ge hz)]
        exact (le_max_left
          (-Real.log (cutoffOriginCubeAverage M m omega) - Real.log 2) 0).trans
          (le_add_of_nonneg_left (le_max_right _ _))
    · exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hWbig : IsBigO M.P.toMeasure (gammaSigma 1)
      (fun omega ↦ max (|Real.log (cutoffOriginCubeAverage M m omega)| - Real.log 2) 0)
      (gammaTriangleConst 1 *
        (cup * (smallDisorderExponent cUpper M.delta)⁻¹ +
          1 / (a * smallDisorderExponent cLower M.delta))) := by
    rw [isBigO_gammaSigma_iff] at hsum ⊢
    intro t ht
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (hsum ht)
    intro omega homega
    change gammaTriangleConst 1 *
      (cup * (smallDisorderExponent cUpper M.delta)⁻¹ +
        1 / (a * smallDisorderExponent cLower M.delta)) * t <
      |max (|Real.log (cutoffOriginCubeAverage M m omega)| - Real.log 2) 0| at homega
    change gammaTriangleConst 1 *
      (cup * (smallDisorderExponent cUpper M.delta)⁻¹ +
        1 / (a * smallDisorderExponent cLower M.delta)) * t < |Y omega + X omega|
    rw [abs_of_nonneg (le_max_right _ _)] at homega
    rw [abs_of_nonneg (add_nonneg (by dsimp only [Y]; exact le_max_right _ _)
      (by dsimp only [X]; exact le_max_right _ _))]
    exact homega.trans_le (hWle omega)
  let A := gammaTriangleConst 1 *
    (cup * (smallDisorderExponent cUpper M.delta)⁻¹ +
      1 / (a * smallDisorderExponent cLower M.delta))
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (gammaTriangleConst_pos (σ := 1))
      (add_pos (mul_pos hcup (inv_pos.mpr hpU))
        (one_div_pos.mpr (mul_pos ha hpL)))
  have hOg := SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (X := fun omega ↦
      max (|Real.log (cutoffOriginCubeAverage M m omega)| - Real.log 2) 0)
    (σ := (1 : ℝ)) (A := A) (by norm_num) hA hWm hWbig
  have hδlog : Real.log M.delta ≠ 0 := by
    have hlt : M.delta < 1 := lt_of_le_of_lt hMhalf (by norm_num)
    exact (Real.log_neg M.shellPrefix.delta_pos hlt).ne
  have hscale : (4 : ℝ) ^ (1 : ℝ)⁻¹ * A =
      C * M.delta ^ 2 * |Real.log M.delta| ^ 2 := by
    rw [inv_one, Real.rpow_one]
    dsimp only [A, C]
    rw [smallDisorderExponent_eq_div M.shellPrefix.delta_pos.ne' hδlog,
      smallDisorderExponent_eq_div M.shellPrefix.delta_pos.ne' hδlog]
    field_simp [hcUpper.ne', hcLower.ne', ha.ne', M.shellPrefix.delta_pos.ne',
      abs_ne_zero.mpr hδlog]
  rw [hscale] at hOg
  simpa only [SubdiffusiveProcess.OGammaLE, max_eq_left (le_max_right _ _)] using hOg

end SubdiffusiveProcess.Section9
