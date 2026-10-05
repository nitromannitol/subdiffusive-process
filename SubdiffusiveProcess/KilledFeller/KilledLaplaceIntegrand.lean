module

public import SubdiffusiveProcess.KilledFeller.LaplaceBounds
public import SubdiffusiveProcess.KilledFeller.KillPath

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.KilledFeller

/-- The zero-extended test read along a path before its first exit. -/
def killedTest {d : ℕ} (U : Set (SpatialCoordinates d))
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (w : DiffusionPath d) (t : ℝ) : ℝ :=
  if ENNReal.ofReal t < ContinuousPath.exitTime U w then f (w (Real.toNNReal t)) else 0

/-- The killed test is jointly Borel measurable in path and time. -/
theorem measurable_killedTest {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Measurable (fun p : DiffusionPath d × ℝ => killedTest U f p.1 p.2) := by
  classical
  have hs : MeasurableSet {p : DiffusionPath d × ℝ |
      ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
      ((ContinuousPath.measurable_exitTime U hU).comp measurable_fst)
  have hc : Continuous (fun p : DiffusionPath d × ℝ => f (p.1 (Real.toNNReal p.2))) :=
    f.continuous.comp (ContinuousEval.continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd)))
  exact Measurable.ite hs hc.measurable measurable_const

/-- A killed test is bounded by the original sup norm. -/
theorem abs_killedTest_le {d : ℕ} (U : Set (SpatialCoordinates d))
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (w : DiffusionPath d) (t : ℝ) :
    |killedTest U f w t| ≤ ‖f‖ := by
  classical
  unfold killedTest
  split_ifs
  · exact (Real.norm_eq_abs _).symm ▸ f.norm_coe_le_norm _
  · simpa only [abs_zero] using norm_nonneg f

/-- The scalar killed Laplace integral is Borel measurable in the path. -/
theorem measurable_killedLaplace {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (lam : ℝ) :
    Measurable (fun w : DiffusionPath d => ∫ t in Ioi (0 : ℝ),
      Real.exp (-lam * t) * killedTest U f w t) := by
  have hm : Measurable (fun p : DiffusionPath d × ℝ =>
      Real.exp (-lam * p.2) * killedTest U f p.1 p.2) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
      (measurable_killedTest U hU f)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- A normalized killed Laplace integral is bounded by the test's sup norm. -/
theorem abs_normalized_killedLaplace_le {d : ℕ} (U : Set (SpatialCoordinates d))
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (w : DiffusionPath d)
    {lam : ℝ} (hlam : 0 < lam) :
    |lam * (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * killedTest U f w t)| ≤ ‖f‖ := by
  have hbound : |∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * killedTest U f w t| ≤
      lam⁻¹ * ‖f‖ := by
    rw [← MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hlam,
      ← integral_mul_const, ← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hlam).mul_const ‖f‖)
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (abs_killedTest_le U f w t) (Real.exp_pos _).le
  rw [abs_mul, abs_of_pos hlam]
  calc
    lam * |∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * killedTest U f w t| ≤
        lam * (lam⁻¹ * ‖f‖) := mul_le_mul_of_nonneg_left hbound hlam.le
    _ = ‖f‖ := by rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]

/-- The survival-indicator expression is exactly the killed-test expression. -/
theorem indicator_exp_eq_exp_killedTest {d : ℕ} (U : Set (SpatialCoordinates d))
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (w : DiffusionPath d)
    (lam t : ℝ) :
    {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U w}.indicator
      (fun s => Real.exp (-lam * s) * f (w (Real.toNNReal s))) t =
      Real.exp (-lam * t) * killedTest U f w t := by
  classical
  unfold killedTest
  by_cases ht : ENNReal.ofReal t < ContinuousPath.exitTime U w
  · rw [ite_eq_left ht, indicator_of_mem (show t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U w} from ht)]
  · rw [ite_eq_right ht, indicator_of_notMem (show t ∉ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U w} from ht), mul_zero]

/-- A short-time displacement event is open in the compact-open path topology. -/
theorem isOpen_displacement_event {d : ℕ} (x : SpatialCoordinates d) (h r : ℝ) :
    IsOpen {w : DiffusionPath d | ∃ t : ℝ≥0, (t : ℝ) ≤ h ∧ r < dist (w t) x} := by
  have heq : {w : DiffusionPath d | ∃ t : ℝ≥0, (t : ℝ) ≤ h ∧ r < dist (w t) x} =
      ⋃ t : {s : ℝ≥0 | (s : ℝ) ≤ h}, {w : DiffusionPath d | r < dist (w t.1) x} := by
    ext w
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨t, ht, hd⟩
      exact ⟨⟨t, ht⟩, hd⟩
    · rintro ⟨t, hd⟩
      exact ⟨t.1, t.2, hd⟩
  rw [heq]
  exact isOpen_iUnion fun t => isOpen_lt continuous_const
    ((continuous_eval_const t.1).dist continuous_const)

end SubdiffusiveProcess.KilledFeller
