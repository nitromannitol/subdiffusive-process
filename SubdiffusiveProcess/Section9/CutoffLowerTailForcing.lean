
module

public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity

@[expose] public section

/-!
# Actual-model forcing tail for the cutoff lower-tail recursion
-/

open MeasureTheory Homogenization Homogenization.IndependentSums

namespace SubdiffusiveProcess.Section9

open SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model

/-- The single coarse-shell forcing in the mass recursion has a dimensional
Gaussian lower tail, uniformly in the model and shell index. -/
theorem exists_cutoffLowerTail_forcing (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : GMCModel d) (m : ℕ) (u : ℝ), 0 ≤ u →
        M.P.toMeasure.real {omega |
            u / 4 < (d : ℝ) * Real.log 3 + tauSq M.P +
              translatedShellG2 m 0 omega} ≤
          C * Real.exp (-c * max (u - C) 0 ^ 2 / M.delta ^ 2) := by
  let α : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹
  let D : ℝ := (d : ℝ) * Real.log 3
  let C : ℝ := 1 + 4 * (D + Real.log 2 / 8 + α)
  let c : ℝ := 1 / (16 * α ^ 2)
  have hα : 0 < α := Real.rpow_pos_of_pos (by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith) _
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hC : 0 < C := by dsimp [C]; positivity
  have hCone : 1 ≤ C := by
    dsimp [C]
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro M m u hu
  by_cases huC : u ≤ C
  · have hprob : M.P.toMeasure.real {omega |
        u / 4 < (d : ℝ) * Real.log 3 + tauSq M.P +
          translatedShellG2 m 0 omega} ≤ 1 := by
      exact measureReal_le_one
    have hmax : max (u - C) 0 = 0 := max_eq_right (sub_nonpos.mpr huC)
    simp only [hmax, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      zero_div, Real.exp_zero]
    exact hprob.trans (by simpa only [mul_one] using hCone)
  · have hCu : C < u := lt_of_not_ge huC
    have hdeltaHalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
    have htau := tauSq_le_delta_sq M
    have htauBound : tauSq M.P ≤ Real.log 2 / 8 := by
      have hsq : M.delta ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [M.shellPrefix.delta_pos]
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    let t : ℝ := 1 + (u - C) / (4 * α * M.delta)
    have ht : 1 ≤ t := by
      dsimp [t]
      have : 0 ≤ (u - C) / (4 * α * M.delta) :=
        div_nonneg (sub_nonneg.mpr hCu.le)
          (mul_nonneg (mul_nonneg (by norm_num) hα.le) M.shellPrefix.delta_pos.le)
      linarith
    have hthreshold : D + tauSq M.P + α * M.delta * t ≤ u / 4 := by
      dsimp [t, C]
      have hδpos := M.shellPrefix.delta_pos
      field_simp [hα.ne', hδpos.ne']
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hsubset : {omega : PotentialSample d |
          u / 4 < D + tauSq M.P + translatedShellG2 m (0 : Homogenization.Vec d) omega} ⊆
        {omega : PotentialSample d |
          α * M.delta * t < translatedShellG2 m (0 : Homogenization.Vec d) omega} := by
      intro omega homega
      dsimp [D] at homega hthreshold
      have hsum := lt_of_le_of_lt hthreshold homega
      exact (add_lt_add_iff_left ((d : ℝ) * Real.log 3 + tauSq M.P)).mp
        (by simpa only [add_assoc] using hsum)
    have htail := isBigOWith_gammaTwo_translatedShellG2 M m 0 ht
    have hmeasure : M.P.toMeasure.real {omega : PotentialSample d |
          u / 4 < D + tauSq M.P + translatedShellG2 m (0 : Homogenization.Vec d) omega} ≤
        M.P.toMeasure.real {omega : PotentialSample d |
          α * M.delta * t < translatedShellG2 m (0 : Homogenization.Vec d) omega} :=
      measureReal_mono hsubset (measure_ne_top _ _)
    have hraw := hmeasure.trans (by
      simpa only [Homogenization.IndependentSums.upperTailEvent, α] using htail)
    have htSq : ((u - C) / (4 * α * M.delta)) ^ 2 ≤ t ^ 2 := by
      dsimp [t]
      have : 0 ≤ (u - C) / (4 * α * M.delta) :=
        div_nonneg (sub_nonneg.mpr hCu.le)
          (mul_nonneg (mul_nonneg (by norm_num) hα.le) M.shellPrefix.delta_pos.le)
      nlinarith
    have hexp : Real.exp (-(t ^ (2 : ℝ))) ≤
        Real.exp (-c * (u - C) ^ 2 / M.delta ^ 2) := by
      rw [Real.rpow_two]
      apply Real.exp_le_exp.mpr
      dsimp [c]
      field_simp [hα.ne', M.shellPrefix.delta_pos.ne'] at htSq ⊢
      nlinarith
    have hmax : max (u - C) 0 = u - C := max_eq_left (sub_nonneg.mpr hCu.le)
    rw [gammaSigma_inv] at hraw
    rw [hmax]
    dsimp [D] at hraw
    exact hraw.trans (hexp.trans (le_mul_of_one_le_left (Real.exp_nonneg _) hCone))

end SubdiffusiveProcess.Section9
