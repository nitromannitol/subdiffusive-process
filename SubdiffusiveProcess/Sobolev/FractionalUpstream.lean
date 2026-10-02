import SubdiffusiveProcess.Main.CubeFractionalL2Seminorm
import SubdiffusiveProcess.Geometry.UpstreamCube
import SubdiffusiveProcess.CoarseGrainingVocab.Norms
import Homogenization.Sobolev.Fractional.EuclideanWspPowerTwoBridge

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section

namespace SubdiffusiveProcess

private theorem kernel_two_integrand_eq {d : ℕ}
    (s : Homogenization.FractionalOrder) (F : Homogenization.Vec d → Homogenization.Vec d)
    (z : Homogenization.Vec d × Homogenization.Vec d) :
    ‖Homogenization.cubeEuclideanWspKernel s Homogenization.FiniteLpExponent.two F z‖ₑ ^
        (2 : ℝ) =
      ENNReal.ofReal (∑ i : Fin d, (F z.1 i - F z.2 i) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (z.1 j - z.2 j) ^ 2))) ^
          ((d : ℝ) + 2 * (s : ℝ)) := by
  rw [← ofReal_norm_eq_enorm]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
  rw [Homogenization.norm_cubeEuclideanWspKernel]
  norm_num
  let a : ℝ := s.1 * 2 + (d : ℝ)
  rw [show (d : ℝ) + 2 * s.1 = a by simp [a, add_comm, mul_comm]]
  rw [show -((d : ℝ) / 2) + -s.1 = -a / 2 by dsimp [a]; ring]
  by_cases hxy : z.1 = z.2
  · rw [hxy]
    simp
  · have hpos : 0 < Homogenization.euclideanDist z.1 z.2 := by
      apply lt_of_le_of_ne (Homogenization.euclideanDist_nonneg _ _)
      intro hzero
      exact hxy (Homogenization.euclideanDist_eq_zero_iff.mp hzero.symm)
    rw [mul_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (-a / 2) * (2 : ℝ) = -a by ring]
    rw [Real.rpow_neg hpos.le]
    rw [mul_comm, ← div_eq_mul_inv]
    rw [ENNReal.ofReal_div_of_pos]
    rw [← ENNReal.ofReal_rpow_of_pos hpos]
    unfold Homogenization.euclideanDist Homogenization.euclideanNorm
    unfold Homogenization.vecNormSq Homogenization.vecDot
    simp only [Pi.sub_apply, pow_two]
    rw [show Real.sqrt (∑ i : Fin d, (F z.1 i - F z.2 i) * (F z.1 i - F z.2 i)) *
        Real.sqrt (∑ i : Fin d, (F z.1 i - F z.2 i) * (F z.1 i - F z.2 i)) =
        ∑ i : Fin d, (F z.1 i - F z.2 i) * (F z.1 i - F z.2 i) by
      rw [← pow_two, Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg _)]]
    all_goals exact Real.rpow_pos_of_pos hpos _

/-- On every triadic cube, the approved Euclidean seminorm equals the imported paper-normalized Wsp seminorm at p = 2, with its exact s and volume factors. -/
theorem cubeFractionalL2Seminorm_eq_paperFractionalSeminorm
    {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin d → SubdiffusiveProcess.DomainL2
      (SubdiffusiveProcess.centeredCube (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr)) :
    SubdiffusiveProcess.cubeFractionalL2Seminorm hd
      (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr s f =
      SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalSeminorm Q s
        Homogenization.FiniteLpExponent.two (fun x i => f i x) := by
  unfold cubeFractionalL2Seminorm SubdiffusiveProcess.CoarseGrainingVocab.paperFractionalSeminorm
  rw [Homogenization.cubeEuclideanWspESeminorm_eq_lintegral]
  norm_num only [Homogenization.FiniteLpExponent.two_exponent, ENNReal.toReal_ofNat]
  have hmeasure := centeredCube_restrict_volume_eq_cubeMeasure Q hr
  have hvolume : volume (centeredCube (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d)) =
      ENNReal.ofReal (Homogenization.cubeVolume Q) := by
    calc
      volume (centeredCube (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d)) =
          (volume.restrict (centeredCube (Homogenization.cubeCenter Q)
            (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d))) Set.univ := by
              rw [Measure.restrict_apply_univ]
      _ = Homogenization.cubeMeasure Q Set.univ := by rw [hmeasure]
      _ = ENNReal.ofReal (Homogenization.cubeVolume Q) :=
        Homogenization.cubeMeasure_apply_univ_eq Q
  rw [hvolume]
  rw [Homogenization.Gagliardo.lintegral_gagliardoCubeMeasure_eq]
  let U : Set (SpatialCoordinates d) := centeredCube (Homogenization.cubeCenter Q)
    (Homogenization.cubeScaleFactor Q) hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  let g : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (∑ i : Fin d, (f i z.1 - f i z.2) ^ 2) /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (z.1 j - z.2 j) ^ 2))) ^
        ((d : ℝ) + 2 * (s : ℝ))
  have hcoord (i : Fin d) : AEMeasurable (fun z : SpatialCoordinates d × SpatialCoordinates d =>
      (f i z.1 : ℝ) - f i z.2) (μ.prod μ) := by
    have hf : AEStronglyMeasurable (fun x : SpatialCoordinates d => (f i x : ℝ)) μ := by
      simpa only [μ, U] using Lp.aestronglyMeasurable (f i)
    exact (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).aemeasurable.sub
      (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).aemeasurable
  have hnum : AEMeasurable (fun z : SpatialCoordinates d × SpatialCoordinates d =>
      ∑ i : Fin d, ((f i z.1 : ℝ) - f i z.2) ^ 2) (μ.prod μ) := by
    exact Finset.aemeasurable_fun_sum Finset.univ fun i _ => (hcoord i).pow_const 2
  have hden : Measurable (fun z : SpatialCoordinates d × SpatialCoordinates d =>
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (z.1 j - z.2 j) ^ 2))) ^
        ((d : ℝ) + 2 * (s : ℝ))) := by
    apply Measurable.pow
    · apply Measurable.ennreal_ofReal
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun j _ =>
        (((measurable_pi_apply j).comp measurable_fst).sub
          ((measurable_pi_apply j).comp measurable_snd)).pow_const 2
    · exact measurable_const
  have hg : AEMeasurable g (μ.prod μ) := by
    exact hnum.ennreal_ofReal.div hden.aemeasurable
  have hintegral :
      (∫⁻ x in U, ∫⁻ y in U,
        ENNReal.ofReal (∑ i : Fin d, (f i x - f i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ))) =
      ∫⁻ z in Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q,
        ‖Homogenization.cubeEuclideanWspKernel s Homogenization.FiniteLpExponent.two
          (fun x i => f i x) z‖ₑ ^ (2 : ℝ) ∂(volume.prod volume) := by
    change (∫⁻ x, ∫⁻ y, g (x, y) ∂μ ∂μ) = _
    rw [← lintegral_prod g hg]
    have hμ : μ = Homogenization.cubeMeasure Q := by
      simpa only [μ, U] using hmeasure
    rw [hμ, Homogenization.cubeMeasure, Measure.prod_restrict]
    apply lintegral_congr
    intro z
    exact (kernel_two_integrand_eq s (fun x i => f i x) z).symm
  change (ENNReal.ofReal (s : ℝ) / ENNReal.ofReal (Homogenization.cubeVolume Q) *
      (∫⁻ x in U, ∫⁻ y in U,
        ENNReal.ofReal (∑ i : Fin d, (f i x - f i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ)))) ^ (1 / 2 : ℝ) = _
  rw [hintegral]
  rw [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg,
    ENNReal.mul_rpow_of_nonneg]
  · rw [ENNReal.ofReal_inv_of_pos (Homogenization.cubeVolume_pos Q), mul_assoc]
  all_goals norm_num

end SubdiffusiveProcess
