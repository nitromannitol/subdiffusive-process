import SubdiffusiveProcess.Sobolev.FractionalUpstream
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalTransport

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_inputs_extension_seminorm_kernel {d : ℕ}
    (s : ℝ) (F : Homogenization.Vec d → Homogenization.Vec d)
    (z : Homogenization.Vec d × Homogenization.Vec d) :
    ‖SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s F z‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (∑ i : Fin d, (F z.1 i - F z.2 i) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (z.1 j - z.2 j) ^ 2))) ^
          ((d : ℝ) + 2 * s) := by
  by_cases hxy : z.1 = z.2
  · simp [SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel, hxy,
      Homogenization.euclideanNorm, Homogenization.vecNormSq,
      Homogenization.vecDot]
  have hpos : 0 < Homogenization.euclideanNorm (z.1 - z.2) := by
    change 0 < Homogenization.euclideanDist z.1 z.2
    exact lt_of_le_of_ne (Homogenization.euclideanDist_nonneg _ _)
      (fun h => hxy (Homogenization.euclideanDist_eq_zero_iff.mp h.symm))
  have hnonneg : 0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s F z := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel
    exact div_nonneg (Homogenization.euclideanNorm_nonneg _)
      (Real.rpow_nonneg (Homogenization.euclideanNorm_nonneg _) _)
  rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg hnonneg,
    ENNReal.ofReal_rpow_of_nonneg hnonneg (by norm_num)]
  norm_num only [Real.rpow_two]
  unfold SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel
  rw [div_pow]
  have hden : (Homogenization.euclideanNorm (z.1 - z.2) ^ (s + (d : ℝ) / 2)) ^ 2 =
      Homogenization.euclideanNorm (z.1 - z.2) ^ ((d : ℝ) + 2 * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    push_cast
    ring
  rw [hden, ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hpos _),
    ← ENNReal.ofReal_rpow_of_pos hpos]
  unfold Homogenization.euclideanNorm Homogenization.vecNormSq Homogenization.vecDot
  simp only [Pi.sub_apply]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg _)]
  simp only [pow_two]

theorem inputs_extension_seminorm {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1) (f : Fin d → DomainL2 (centeredCube z r hr)) :
    (SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
      (centeredCube z r hr : Set (SpatialCoordinates d)) s.1 (fun x i => f i x) =
      cubeFractionalL2Seminorm hd z r hr s f) := by
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
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
  have hI :
      (∫⁻ w, ‖SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s.1 (fun x i => f i x) w‖ₑ ^
          (2 : ℝ) ∂(μ.prod μ)) = ∫⁻ x, ∫⁻ y, g (x, y) ∂μ ∂μ := by
    calc
      _ = ∫⁻ w, g w ∂(μ.prod μ) := by
        apply lintegral_congr
        intro w
        exact aux_inputs_extension_seminorm_kernel s.1 (fun x i => f i x) w
      _ = _ := lintegral_prod g hg
  unfold SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn cubeFractionalL2Seminorm
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  change (ENNReal.ofReal s.1 / volume U) ^ (1 / 2 : ℝ) *
      (∫⁻ w, ‖SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s.1 (fun x i => f i x) w‖ₑ ^
        (2 : ℝ) ∂(μ.prod μ)) ^ (1 / 2 : ℝ) =
    ((ENNReal.ofReal s.1 / volume U) * (∫⁻ x, ∫⁻ y, g (x, y) ∂μ ∂μ)) ^ (1 / 2 : ℝ)
  rw [hI, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]

end Paper

