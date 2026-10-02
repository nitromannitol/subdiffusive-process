import SubdiffusiveProcess.Sobolev.CoordinateL2Integral
import SubdiffusiveProcess.Geometry.UpstreamCube
import SubdiffusiveProcess.CoarseGrainingVocab.Norms

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section

namespace SubdiffusiveProcess

private theorem raw_coordinate_integral_eq_sum_norm_sq
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (f : Fin d → DomainL2 Ω) :
    (∫ x in (Ω : Set (SpatialCoordinates d)),
      ∑ i : Fin d, (f i x) ^ 2) = ∑ i : Fin d, ‖f i‖ ^ 2 := by
  let μ := volume.restrict (Ω : Set (SpatialCoordinates d))
  have hi (i : Fin d) : Integrable (fun x => (f i x) ^ 2) μ :=
    (Lp.memLp (f i)).integrable_sq
  have hsum : Integrable (fun x => ∑ i : Fin d, (f i x) ^ 2) μ :=
    integrable_finset_sum Finset.univ (fun i _ => hi i)
  have hnonneg : 0 ≤ᵐ[μ] (fun x => ∑ i : Fin d, (f i x) ^ 2) :=
    ae_of_all μ fun x => Finset.sum_nonneg fun i _ => sq_nonneg (f i x)
  have hnonneg' : ∀ x, 0 ≤ ∑ i : Fin d, (f i x) ^ 2 :=
    fun x => Finset.sum_nonneg fun i _ => sq_nonneg (f i x)
  have h := congrArg ENNReal.toReal (lintegral_coordinate_sq_eq_sum_norm_sq f)
  rw [← ofReal_integral_eq_lintegral_ofReal hsum hnonneg,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => sq_nonneg ‖f i‖)] at h
  rw [ENNReal.toReal_ofReal (integral_nonneg hnonneg')] at h
  simpa only [μ, MeasureTheory.Measure.restrict_apply_univ] using h

/-- Coordinate L2 normalization agrees exactly with the imported normalized Euclidean L2 norm. -/
theorem cubeCoordinateL2Normalization_eq_normalizedEuclideanLpENorm
    {d : ℕ} (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (f : Fin d → SubdiffusiveProcess.DomainL2
      (SubdiffusiveProcess.centeredCube (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr)) :
    Real.sqrt (∑ i : Fin d, ‖f i‖ ^ 2) /
        Real.sqrt (volume.real
          (SubdiffusiveProcess.centeredCube (Homogenization.cubeCenter Q)
            (Homogenization.cubeScaleFactor Q) hr :
              Set (SubdiffusiveProcess.SpatialCoordinates d))) =
      ((Homogenization.cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
        Homogenization.FiniteLpExponent.two.exponent (fun x i ↦ f i x)).toReal := by
  let Ω : Opens (SpatialCoordinates d) := centeredCube (Homogenization.cubeCenter Q)
    (Homogenization.cubeScaleFactor Q) hr
  let g : SpatialCoordinates d → Homogenization.Vec d := fun x i => f i x
  have hhilbert : MemLp (fun x => Homogenization.HilbertVec.ofVec (g x))
      (2 : ℝ≥0∞) (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    simpa only [g, Homogenization.HilbertVec.ofVec, PiLp.toLp_apply] using
      (Lp.memLp (f i))
  have hrawmem : MemLp (fun x => Homogenization.euclideanNorm (g x))
      (2 : ℝ≥0∞) (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    simpa only [Homogenization.euclideanNorm_eq_norm_ofVec] using hhilbert.norm
  have hnormint :
      (∫ x in (Ω : Set (SpatialCoordinates d)),
        Homogenization.euclideanNorm (g x) ^ 2) = ∑ i : Fin d, ‖f i‖ ^ 2 := by
    calc
      (∫ x in (Ω : Set (SpatialCoordinates d)),
          Homogenization.euclideanNorm (g x) ^ 2) =
          ∫ x in (Ω : Set (SpatialCoordinates d)), ∑ i : Fin d, (f i x) ^ 2 := by
            apply integral_congr_ae
            filter_upwards with x
            rw [Homogenization.euclideanNorm_sq]
            simp only [g, Homogenization.vecNormSq, Homogenization.vecDot, pow_two]
      _ = ∑ i : Fin d, ‖f i‖ ^ 2 := by
        exact raw_coordinate_integral_eq_sum_norm_sq f
  let U := Homogenization.cubeBoundedMeasurableDomain Q
  have hrawmemU : MemLp (fun x => Homogenization.euclideanNorm (g x))
      (2 : ℝ≥0∞) U.restrictedVolume := by
    rw [Homogenization.cubeBoundedMeasurableDomain_restrictedVolume_eq_cubeMeasure]
    rw [← centeredCube_restrict_volume_eq_cubeMeasure Q hr]
    exact hrawmem
  have hnormmemU : MemLp (fun x => Homogenization.euclideanNorm (g x))
      (2 : ℝ≥0∞) U.normalizedVolume := by
    exact (U.memLp_normalizedVolume_iff (2 : ℝ≥0∞) _).mpr hrawmemU
  have hformula := U.normalizedEuclideanLpNorm_eq_integral_rpow
    (2 : ℝ≥0∞) (by norm_num) (by norm_num) g hnormmemU
  have hvol : volume.real (U : Set (SpatialCoordinates d)) =
      volume.real (Ω : Set (SpatialCoordinates d)) := by
    have hm := congrArg (fun m : Measure (SpatialCoordinates d) => m Set.univ)
      (centeredCube_restrict_volume_eq_cubeMeasure Q hr)
    have hm' : volume (Ω : Set (SpatialCoordinates d)) =
        volume (U : Set (SpatialCoordinates d)) := by
      change volume (Ω : Set (SpatialCoordinates d)) =
        volume (Homogenization.cubeSet Q)
      simpa only [Measure.restrict_apply_univ,
        Homogenization.cubeMeasure_apply_univ] using hm
    have hm'' := hm'.symm
    exact congrArg ENNReal.toReal hm''
  have hvol' : (volume (U : Set (SpatialCoordinates d))).toReal =
      (volume (Ω : Set (SpatialCoordinates d))).toReal := by
    exact hvol
  have hrestrict : U.restrictedVolume =
      volume.restrict (Ω : Set (SpatialCoordinates d)) := by
    rw [Homogenization.cubeBoundedMeasurableDomain_restrictedVolume_eq_cubeMeasure,
      ← centeredCube_restrict_volume_eq_cubeMeasure Q hr]
  have hnormintU :
      (∫ x, Homogenization.euclideanNorm (g x) ^ 2 ∂U.normalizedVolume) =
        (volume.real (Ω : Set (SpatialCoordinates d)))⁻¹ *
          (∑ i : Fin d, ‖f i‖ ^ 2) := by
    rw [Homogenization.BoundedMeasurableDomain.normalizedVolume,
      MeasureTheory.integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
    rw [hvol']
    rw [hrestrict]
    rw [hnormint]
    rfl
  have hext :
      ((Homogenization.cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
        Homogenization.FiniteLpExponent.two.exponent (fun x i ↦ f i x)).toReal =
        U.normalizedEuclideanLpNorm (2 : ℝ≥0∞) g hnormmemU := by
    change (MeasureTheory.eLpNorm
        (fun x => Homogenization.euclideanNorm (g x)) (2 : ℝ≥0∞)
          U.normalizedVolume).toReal = _
    rfl
  have hformula' :
      U.normalizedEuclideanLpNorm (2 : ℝ≥0∞) g hnormmemU =
        (∫ x, Homogenization.euclideanNorm (g x) ^ (2 : ℝ)
          ∂U.normalizedVolume) ^ (1 / 2 : ℝ) := by
    convert hformula using 1
    · norm_num
  have hVpos : 0 < volume.real (Ω : Set (SpatialCoordinates d)) := by
    change 0 < (volume (Ω : Set (SpatialCoordinates d))).toReal
    rw [show (Ω : Set (SpatialCoordinates d)) = Homogenization.openCubeSet Q by
      simpa only [Ω] using centeredCube_eq_openCubeSet Q hr]
    simpa using Homogenization.cubeVolume_pos Q
  have hSnonneg : 0 ≤ ∑ i : Fin d, ‖f i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg ‖f i‖
  have hrpow_integral :
      (∫ x, Homogenization.euclideanNorm (g x) ^ (2 : ℝ)
          ∂U.normalizedVolume) =
        ∫ x, Homogenization.euclideanNorm (g x) ^ (2 : ℕ)
          ∂U.normalizedVolume := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.rpow_two]
  rw [hext, hformula', hrpow_integral, hnormintU]
  change Real.sqrt (∑ i : Fin d, ‖f i‖ ^ 2) /
      Real.sqrt (volume.real (Ω : Set (SpatialCoordinates d))) = _
  rw [Real.mul_rpow (inv_nonneg.mpr hVpos.le) hSnonneg]
  rw [Real.inv_rpow]
  · rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    ring
  · exact hVpos.le

end SubdiffusiveProcess
