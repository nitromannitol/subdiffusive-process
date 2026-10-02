import SubdiffusiveProcess.Main.CubeFractionalL2Norm
import SubdiffusiveProcess.Sobolev.CubeL2Upstream
import SubdiffusiveProcess.Sobolev.FractionalUpstream

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section

namespace SubdiffusiveProcess

/-- The approved additive fractional norm agrees exactly with the imported paper norm.
Both extended-real summands are finite on the approved fractional L2 carrier. -/
theorem cubeFractionalL2Norm_eq_paperFractionalFullNorm
    {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (s : Set.Ioo (0 : ℝ) 1)
    (f : CubeFractionalL2 (k := d) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s) :
    cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr s f =
      (SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalFullNorm Q s
        Homogenization.FiniteLpExponent.two (fun x i => f.val i x)).toReal := by
  let Ω : Opens (SpatialCoordinates d) := centeredCube
    (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr
  let g : SpatialCoordinates d → Homogenization.Vec d :=
    fun x i => f.val i x
  have hhilbert : MemLp (fun x => Homogenization.HilbertVec.ofVec (g x))
      (2 : ℝ≥0∞) (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    simpa only [g, Homogenization.HilbertVec.ofVec, PiLp.toLp_apply] using
      (Lp.memLp (f.val i))
  have hrawmem : MemLp (fun x => Homogenization.euclideanNorm (g x))
      (2 : ℝ≥0∞) (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    simpa only [Homogenization.euclideanNorm_eq_norm_ofVec] using hhilbert.norm
  let U := Homogenization.cubeBoundedMeasurableDomain Q
  have hrawmemU : MemLp (fun x => Homogenization.euclideanNorm (g x))
      (2 : ℝ≥0∞) U.restrictedVolume := by
    rw [Homogenization.cubeBoundedMeasurableDomain_restrictedVolume_eq_cubeMeasure]
    rw [← centeredCube_restrict_volume_eq_cubeMeasure Q hr]
    exact hrawmem
  have hnormmemU : MemLp (fun x => Homogenization.euclideanNorm (g x))
      (2 : ℝ≥0∞) U.normalizedVolume := by
    exact (U.memLp_normalizedVolume_iff (2 : ℝ≥0∞) _).mpr hrawmemU
  have hnormtop : U.normalizedEuclideanLpENorm (2 : ℝ≥0∞) g < ∞ := by
    unfold Homogenization.BoundedMeasurableDomain.normalizedEuclideanLpENorm
    exact hnormmemU.eLpNorm_lt_top
  have hseminormtop :
      SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalSeminorm Q s
        Homogenization.FiniteLpExponent.two g < ∞ := by
    rw [← cubeFractionalL2Seminorm_eq_paperFractionalSeminorm hd Q hr s f.val]
    exact f.property
  have hnormtop' :
      (Homogenization.cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
        Homogenization.FiniteLpExponent.two.exponent
        (fun x i => f.val i x) < ∞ := by
    simpa only [U, g, Homogenization.FiniteLpExponent.two_exponent] using hnormtop
  have hseminormtop' :
      SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalSeminorm Q s
        Homogenization.FiniteLpExponent.two (fun x i => f.val i x) < ∞ := by
    simpa only [g] using hseminormtop
  have hcoefficienttop :
      (ENNReal.ofReal (Homogenization.cubeScaleFactor Q)) ^ (-s.1) < ∞ := by
    rw [ENNReal.ofReal_rpow_of_pos hr]
    exact ENNReal.ofReal_lt_top
  have hproducttop :
      (ENNReal.ofReal (Homogenization.cubeScaleFactor Q)) ^ (-s.1) *
          (Homogenization.cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
            Homogenization.FiniteLpExponent.two.exponent (fun x i => f.val i x) < ∞ := by
    exact ENNReal.mul_lt_top hcoefficienttop hnormtop'
  unfold cubeFractionalL2Norm
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalFullNorm
  rw [cubeFractionalL2Seminorm_eq_paperFractionalSeminorm hd Q hr s f.val]
  rw [cubeCoordinateL2Normalization_eq_normalizedEuclideanLpENorm Q hr
    (fun i => f.val i)]
  rw [ENNReal.toReal_add hseminormtop'.ne hproducttop.ne]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.ofReal_rpow_of_pos hr]
  rw [ENNReal.toReal_ofReal]
  exact Real.rpow_nonneg hr.le _

end SubdiffusiveProcess
