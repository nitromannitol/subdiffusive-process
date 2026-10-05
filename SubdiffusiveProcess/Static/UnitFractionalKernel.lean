module

public import SubdiffusiveProcess.Static.FractionalReadout
public import SubdiffusiveProcess.Analysis.FractionalCellVariance

@[expose] public section

/-! # The literal lower-integral kernel on the unit cube -/

open MeasureTheory Homogenization
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The unnormalized double integral in the specified static statement. -/
def fractionalSeminormSq {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in U, ∫⁻ z in U,
    ENNReal.ofReal ((u x - u z) ^ 2) /
      ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))

private theorem unit_fractional_kernel_eq {d : ℕ} (u : Vec d → ℝ) (z : Vec d × Vec d) :
    ‖Gagliardo.gagliardoKernel (3 / 4) 2 u z‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal ((u z.1 - u z.2) ^ 2) /
        ENNReal.ofReal (‖z.1 - z.2‖ ^ ((d : ℝ) + 3 / 2)) := by
  by_cases hdiag : z.1 = z.2
  · simp [Gagliardo.gagliardoKernel, hdiag]
  · have hdist : 0 < ‖z.1 - z.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hdiag)
    have hk := Gagliardo.enorm_gagliardoKernel_rpow (3 / 4)
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) u z
    norm_num only [ENNReal.toReal_ofNat] at hk
    rw [hk]
    norm_num only [ENNReal.toReal_ofNat]
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, dist_eq_norm]
    rw [show -((3 / 2 : ℝ) + (d : ℝ)) = -((d : ℝ) + 3 / 2) by ring,
      Real.rpow_neg hdist.le, ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hdist _),
      div_eq_mul_inv, mul_comm]
    simp only [div_eq_mul_inv]

/-- The native scalar fractional norm has exactly the literal kernel of the
static statement; the unit cube has volume one. -/
theorem unit_fractionalSeminormSq_eq {d : ℕ} (u : Vec d → ℝ)
    (hu : AEStronglyMeasurable u (volume.restrict (openCubeSet (originCube d 0)))) :
    fractionalSeminormSq (openCubeSet (originCube d 0)) u =
      Gagliardo.cubeGagliardoESeminorm (originCube d 0) (3 / 4) 2 u ^ 2 := by
  let U := openCubeSet (originCube d 0)
  let μ := volume.restrict U
  let f : Vec d × Vec d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal ((u z.1 - u z.2) ^ 2) /
      ENNReal.ofReal (‖z.1 - z.2‖ ^ ((d : ℝ) + 3 / 2))
  have hnum : AEMeasurable (fun z : Vec d × Vec d => (u z.1 - u z.2) ^ 2) (μ.prod μ) :=
    ((hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).aemeasurable.sub
      (hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).aemeasurable).pow_const 2
  have hden : Measurable (fun z : Vec d × Vec d =>
      ENNReal.ofReal (‖z.1 - z.2‖ ^ ((d : ℝ) + 3 / 2))) := by fun_prop
  have hf : AEMeasurable f (μ.prod μ) := hnum.ennreal_ofReal.div hden.aemeasurable
  have hμ : μ = cubeMeasure (originCube d 0) := by
    unfold μ U cubeMeasure
    exact (Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet _)).symm
  have hnormalized : normalizedCubeMeasure (originCube d 0) = cubeMeasure (originCube d 0) := by
    simp [normalizedCubeMeasure, cubeVolume, cubeScaleFactor, originCube]
  have hk : AEStronglyMeasurable (Gagliardo.gagliardoKernel (3 / 4) 2 u) (μ.prod μ) := by
    have hdist : Measurable (fun z : Vec d × Vec d =>
      dist z.1 z.2 ^ (-Gagliardo.kernelExponent d (3 / 4) 2)) := by fun_prop
    simpa only [Gagliardo.gagliardoKernel] using! hdist.aestronglyMeasurable.smul
      ((hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).sub
        (hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))
  have hkg : AEStronglyMeasurable (Gagliardo.gagliardoKernel (3 / 4) 2 u)
      (Gagliardo.gagliardoCubeMeasure (originCube d 0)) := by
    rw [Gagliardo.gagliardoCubeMeasure, hnormalized, ← hμ]
    exact hk
  unfold fractionalSeminormSq
  change (∫⁻ x, ∫⁻ y, f (x, y) ∂μ ∂μ) = _
  rw [← lintegral_prod f hf]
  rw [← ENNReal.rpow_two,
    Gagliardo.Internal.cubeGagliardoESeminorm_eq_lintegral (by norm_num) (by norm_num) hkg,
    ← ENNReal.rpow_mul]
  norm_num only [ENNReal.toReal_ofNat, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
    ENNReal.rpow_one]
  rw [Gagliardo.gagliardoCubeMeasure, hnormalized, ← hμ]
  exact lintegral_congr fun z => (unit_fractional_kernel_eq u z).symm

/-- Fractional readout in the exact unnormalized lower-integral form. -/
theorem exists_unit_fractional_kernel_readout (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ H : H1Function (openCubeSet (originCube d 0)),
        fractionalSeminormSq (openCubeSet (originCube d 0)) H.toFun ≤
          ENNReal.ofReal (C * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
            (originCube d 0) (1 / 16) (.finite 1) H.grad ^ 2) := by
  obtain ⟨C, hC, hread⟩ := exists_unit_fractional_readout_all d
  refine ⟨C, hC, ?_⟩
  intro H
  rw [unit_fractionalSeminormSq_eq H.toFun H.memL2.aestronglyMeasurable]
  exact hread H

end SubdiffusiveProcess.Static
