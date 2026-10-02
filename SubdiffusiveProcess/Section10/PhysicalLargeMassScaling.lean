import SubdiffusiveProcess.Section10.PhysicalSobolevBankBounds
import SubdiffusiveProcess.Section10.PhysicalLocalTransportCoefficients
import SubdiffusiveProcess.Lane4.CubeDilation

open MeasureTheory SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

theorem mass_affine_dist {d : ℕ} {s : ℝ} (hs : 0 < s)
    (t x y : SpatialCoordinates d) :
    dist (t + s • y) x = s * dist y (s⁻¹ • (x - t)) := by
  rw [dist_eq_norm, dist_eq_norm]
  have heq : t + s • y - x = s • (y - s⁻¹ • (x - t)) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hs]

/-- Exact spatial change of variables, independent of all process theory. -/
theorem mass_affine_ball {d : ℕ} (b : SpatialCoordinates d → ℝ)
    {s r : ℝ} (hs : 0 < s) (t x : SpatialCoordinates d) :
    weightedMeasure b (Metric.ball x r) = ENNReal.ofReal (s ^ d) *
      weightedMeasure (fun y => b (t + s • y)) (Metric.ball (s⁻¹ • (x - t)) (r / s)) := by
  let e := Lane4.cubeDilationEquiv t (0 : SpatialCoordinates d) hs.ne'
  have he : ⇑e = fun y => t + s • y := by funext y i; simp [e, Lane4.cubeDilationEquiv]
  have hpre : (fun y => t + s • y) ⁻¹' Metric.ball x r =
      Metric.ball (s⁻¹ • (x - t)) (r / s) := by
    ext y
    simp only [Set.mem_preimage, Metric.mem_ball, mass_affine_dist hs]
    rw [lt_div_iff₀ hs, mul_comm]
  have hm : Measurable (fun y : SpatialCoordinates d => t + s • y) :=
    measurable_const.add (measurable_const.smul measurable_id)
  have hmap : Measure.map (fun y => t + s • y)
      (volume.restrict (Metric.ball (s⁻¹ • (x - t)) (r / s))) =
      ENNReal.ofReal ((s ^ d)⁻¹) • volume.restrict (Metric.ball x r) := by
    rw [← hpre, ← Measure.restrict_map hm measurableSet_ball]
    have hfun : (fun y => t + s • y) = Lane4.cubeDilation t (0 : SpatialCoordinates d) s := by
      funext y i; simp [Lane4.cubeDilation]
    rw [hfun, Lane4.map_cubeDilation_volume t 0 hs.ne', Measure.restrict_smul,
      abs_of_pos (inv_pos.mpr (pow_pos hs d))]
  have h := lintegral_map_equiv
    (μ := volume.restrict (Metric.ball (s⁻¹ • (x - t)) (r / s)))
    (fun y => ENNReal.ofReal (b y)) e
  rw [he, hmap, lintegral_smul_measure, smul_eq_mul] at h
  simp only [weightedMeasure, withDensity_apply _ measurableSet_ball]
  rw [← h, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hs.le d),
    mul_inv_cancel₀ (pow_pos hs d).ne', ENNReal.ofReal_one, one_mul]

/-- Every translated microbank uses precisely the retained physical fields. -/
theorem mass_physical_micro_density {d : ℕ} (M : GMCModel d) (l k : ℕ)
    (z t : SpatialCoordinates d) (ω : AnchoredC11Sample d) (y : SpatialCoordinates d) :
    localSpeed M l (l + k) z ω (t + (3 : ℝ) ^ (-(k : ℤ)) • y) =
      localSpeed M l l (z + (3 : ℝ) ^ (l + k) • t) ω y := by
  rw [localSpeed, localSpeed, localFactor_eq_one M (by omega),
    localFactor_eq_one M le_rfl]
  simp only [inv_one, one_mul]
  congr 1
  have hscale : (3 : ℝ) ^ (l + k) * (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ l := by
    rw [pow_add, zpow_neg, zpow_natCast, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  rw [smul_add, smul_smul, hscale]
  abel


end SubdiffusiveProcess.Section10
