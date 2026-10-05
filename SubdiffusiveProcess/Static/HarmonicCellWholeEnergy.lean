module

public import SubdiffusiveProcess.Static.HarmonicCellSmoothDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BoundaryDataStability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.ComparisonConvergence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastScalarBridge

@[expose] public section

/-! # The native weighted whole-cell energy of a harmonic extension -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Weighted energy minimality and the smooth datum bound price the whole
unit cell, in the literal lower-integral carrier and in every dimension. -/
theorem harmonicCell_whole_energy_le {d : ℕ}
    (a : Vec d → ℝ) (ha : Continuous a) (hapos : ∀ x, 0 < a x)
    {R : ℝ} (hR : 1 ≤ R)
    (hacoef : ∀ x ∈ openCubeSet (originCube d 0), R⁻¹ ≤ a x ∧ a x ≤ R)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (B : ℝ) (hB : 0 ≤ B) (hfB : HarmonicCutoffDatumSizeBound f B)
    (u : H1Function (openCubeSet (originCube d 0)))
    (hu : IsWeaklyHarmonicOn a (openCubeSet (originCube d 0)) u)
    (htr : HasZeroTraceDifferenceOn (openCubeSet (originCube d 0)) u
      (cutoffHarmonicCellDatum f hf hc)) :
    ∫⁻ x in openCubeSet (originCube d 0),
      ENNReal.ofReal (a x * vecNormSq (u.grad x)) ≤
      ENNReal.ofReal (R * (d : ℝ) ^ 2 * B ^ 2) := by
  let h := cutoffHarmonicCellDatum f hf hc
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hEll := Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
    (isOpen_openCubeSet _).measurableSet ha.continuousOn (inv_pos.mpr hRpos) hacoef
  obtain ⟨v, _, hgrad⟩ := htr
  have hminimal := Section6Dirichlet.integral_coefficient_mul_grad_sq_le_of_boundaryDifference
    hEll (fun x _ => (hapos x).le) hu v hgrad
  have huInt := Section6TheoremC.integrableOn_mul_vecNormSq_grad hEll u
  have hhInt := Section6TheoremC.integrableOn_mul_vecNormSq_grad hEll h
  have huRead : ENNReal.ofReal (∫ x in openCubeSet (originCube d 0),
      a x * vecNormSq (u.grad x)) =
      ∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal (a x * vecNormSq (u.grad x)) :=
    ofReal_integral_eq_lintegral_ofReal huInt (Filter.Eventually.of_forall
      fun x => mul_nonneg (hapos x).le (vecNormSq_nonneg _))
  have hhRead : ENNReal.ofReal (∫ x in openCubeSet (originCube d 0),
      a x * vecNormSq (h.grad x)) =
      ∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal (a x * vecNormSq (h.grad x)) :=
    ofReal_integral_eq_lintegral_ofReal hhInt (Filter.Eventually.of_forall
      fun x => mul_nonneg (hapos x).le (vecNormSq_nonneg _))
  rw [← huRead]
  refine (ENNReal.ofReal_le_ofReal hminimal).trans ?_
  rw [hhRead]
  calc
    _ ≤ ∫⁻ _x in openCubeSet (originCube d 0),
        ENNReal.ofReal (R * (d : ℝ) ^ 2 * B ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (isOpen_openCubeSet _).measurableSet] with x hx
      apply ENNReal.ofReal_le_ofReal
      have hsq : vecNormSq (h.grad x) ≤ ((d : ℝ) * B) ^ 2 := by
        rw [← euclideanNorm_sq]
        exact (sq_le_sq₀ (euclideanNorm_nonneg _) (by positivity)).mpr
          (cutoffHarmonicCellDatum_gradient_le f hf hc hB hfB x)
      calc
        _ ≤ R * vecNormSq (h.grad x) :=
          mul_le_mul_of_nonneg_right (hacoef x hx).2 (vecNormSq_nonneg _)
        _ ≤ R * ((d : ℝ) * B) ^ 2 := mul_le_mul_of_nonneg_left hsq hRpos.le
        _ = _ := by ring
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, volume_openCubeSet_originCube_zero]
      exact mul_one _

end SubdiffusiveProcess.Static
