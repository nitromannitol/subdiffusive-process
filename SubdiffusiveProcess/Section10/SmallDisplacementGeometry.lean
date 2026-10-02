import SubdiffusiveProcess.Section10.EndpointPathsScalar

/-! The cube uses the supremum norm and radius 3^(-k)/2; the literal maximum
uses the Euclidean norm. The factor four leaves a strict margin at exit. -/
open Filter MeasureTheory ProbabilityTheory MarkovProcess Set Topology SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.SmallDisplacement
open EndpointPaths

lemma maximum_lsc {d : ℕ} (t : ℝ≥0) :
    LowerSemicontinuous (maximum (d := d) t) := by
  apply lowerSemicontinuous_ciSup (fun w => maximum_bddAbove w t)
  intro s
  have hc : Continuous (fun w : DiffusionPath d => euclideanNorm (w s - w 0)) := by
    simp only [euclideanNorm, vecNormSq, vecDot]
    fun_prop
  exact hc.lowerSemicontinuous

lemma maximum_measurable {d : ℕ} (t : ℝ≥0) : Measurable (maximum (d := d) t) :=
  (maximum_lsc t).measurable

/-- Euclidean small displacement forces survival in the larger centred cube. -/
lemma smallExit_gt_of_maximum_le {d : ℕ} (w : DiffusionPath d)
    (t : ℝ≥0) (k : ℕ) (r : ℝ) (hr : 0 < r)
    (hscale : 4 * r ≤ (3 : ℝ) ^ (-(k : ℤ))) (hmax : maximum t w ≤ r) :
    (t : ℝ≥0∞) < smallExit k w := by
  apply lt_of_not_ge
  intro hbad
  have hrad := (radius_le_maximum_of_smallExit_le w k t hbad).trans hmax
  linarith

/-- The paper's exact geometric selection, including the initial scale. -/
lemma exists_small_displacement_scale (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ 1 / 12) :
    ∃ k : ℕ, 4 * r ≤ (3 : ℝ) ^ (-(k : ℤ)) ∧ (3 : ℝ) ^ (-(k : ℤ)) < 12 * r := by
  obtain ⟨k, hlt, hle⟩ := exists_nat_pow_near_of_lt_one
    (show 0 < 4 * r by positivity) (show 4 * r ≤ 1 by linarith)
    (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1)
  have heq : (3 : ℝ) ^ (-(k : ℤ)) = (1 / 3 : ℝ) ^ k := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, one_div]
  refine ⟨k, by simpa only [heq] using hle, ?_⟩
  rw [pow_succ] at hlt
  rw [heq]
  linarith

end SubdiffusiveProcess.Section10.SmallDisplacement
