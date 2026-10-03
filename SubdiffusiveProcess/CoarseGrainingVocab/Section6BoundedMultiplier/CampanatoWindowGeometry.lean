module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.AmbientCampanatoRestriction

@[expose] public section

/-!
# Interior top windows for the bounded-multiplier Campanato readout

A middle-half target has two full triadic scales of collar inside the parent.
This is the deterministic window used when the ambient theta-Campanato
contract is applied to restrictions of the parent solution.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- Monotonicity of concentric translated cubes in their integer scale. -/
theorem translatedCube_subset_translatedCube_sameCenter
    {ell top : ℤ} (hscale : ell ≤ top) (z : Vec d) :
    translatedCube d ell z ⊆ translatedCube d top z := by
  rw [translatedCube_eq_metricBall, translatedCube_eq_metricBall]
  apply Metric.ball_subset_ball
  exact mul_le_mul_of_nonneg_left
    (zpow_le_zpow_right₀ (by norm_num) hscale) (by norm_num)

/-- A middle-half target of relative depth at least two is contained in a
concentric scale-`m-2` top window, and that top window remains inside the
original parent cube. -/
theorem exists_middleHalfSubcube_predTwo_window
    {m : ℤ} {z : Vec d} {j : ℕ} {B' : Set (Vec d)}
    (hB' : IsMiddleHalfSubcube m z j B') (hj : 2 ≤ j) :
    ∃ z' : Vec d,
      B' = translatedCube d (m - j) z' ∧
      B' ⊆ translatedCube d (m - 2) z' ∧
      translatedCube d (m - 2) z' ⊆ translatedCube d m z := by
  obtain ⟨z', hB'eq, hcenter, _hball⟩ :=
    exists_middleHalfSubcube_center_and_subset_ball hB'
  refine ⟨z', hB'eq, ?_, ?_⟩
  · rw [hB'eq]
    apply translatedCube_subset_translatedCube_sameCenter (z := z')
    omega
  · rw [translatedCube_eq_metricBall, translatedCube_eq_metricBall]
    apply Metric.ball_subset_ball'
    rw [dist_eq_norm]
    have hpow : (3 : ℝ) ^ (m - 2) = (3 : ℝ) ^ m / 9 := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    rw [hpow]
    have hscalePos : 0 < (3 : ℝ) ^ m := by positivity
    nlinarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
