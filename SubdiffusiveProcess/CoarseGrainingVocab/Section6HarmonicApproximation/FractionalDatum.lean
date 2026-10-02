import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryDatum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6DerivedSupport
import Homogenization.Sobolev.Fractional.EuclideanWspLpMembership

/-!
# The frozen fractional datum as a Chapter-3 field

The v5 anchor stores the inhomogeneous source directly in Chapter 3's full
Euclidean `W^{s,2}` carrier, but its boundary gradient is split between the
`H¹` object and the frozen normalized fractional seminorm.  This file proves
that these two pieces reconstruct the same full carrier on a cube.

PROVENANCE: this is the normalization step used implicitly by
`Algsuperdiff/Section4/Provider/ExcessDecay/CoarseIndexBridges.lean`.  The
measurability half is delegated to CoarseGraining's
`memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem norm_cubeEuclideanWspKernel_two_eq_fractionalKernel
    (sOrder : FractionalOrder) (f : Vec d → Vec d)
    (z : Vec d × Vec d) :
    ‖cubeEuclideanWspKernel sOrder FiniteLpExponent.two f z‖ =
      fractionalKernel sOrder.1 f z := by
  rw [norm_cubeEuclideanWspKernel]
  norm_num [fractionalKernel, euclideanDist, div_eq_mul_inv]
  have hexp : (-((d : ℝ) * (1 / 2 : ℝ)) + -sOrder.1) =
      -(sOrder.1 + (d : ℝ) * (1 / 2 : ℝ)) := by ring
  rw [hexp]
  rw [Real.rpow_neg (euclideanNorm_nonneg _)]
  norm_num
  ac_rfl

private theorem gagliardoCubeMeasure_eq_smul_openProduct (Q : TriadicCube d) :
    Gagliardo.gagliardoCubeMeasure Q =
      (volume (openCubeSet Q))⁻¹ •
        ((volume.restrict (openCubeSet Q)).prod
          (volume.restrict (openCubeSet Q))) := by
  rw [Gagliardo.gagliardoCubeMeasure, normalizedCubeMeasure, cubeMeasure,
    Measure.prod_smul_left, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  have hvol : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    rw [← ENNReal.ofReal_toReal (volume_openCubeSet_lt_top Q).ne,
      volume_openCubeSet_toReal]
  rw [hvol]
  rw [ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]

private theorem volume_openCubeSet_ne_zero' (Q : TriadicCube d) :
    volume (openCubeSet Q) ≠ 0 := by
  intro hzero
  have hz := congrArg ENNReal.toReal hzero
  have hv : cubeVolume Q = 0 := by
    rw [volume_openCubeSet_toReal] at hz
    simpa using hz
  exact (cubeVolume_pos Q).ne' hv

private theorem rawFractionalENorm_ne_top_of_memFractionalOn
    (Q : TriadicCube d) (sOrder : FractionalOrder) (f : Vec d → Vec d)
    (h : SubdiffusiveProcess.CoarseGrainingVocab.MemFractionalOn
      (openCubeSet Q) sOrder.1 f) :
    eLpNorm (fractionalKernel sOrder.1 f) 2
        ((volume.restrict (openCubeSet Q)).prod
          (volume.restrict (openCubeSet Q))) ≠ ∞ := by
  intro htop
  apply h
  rw [fractionalSeminormOn, htop, ENNReal.mul_top]
  exact ne_of_gt (ENNReal.rpow_pos
    (ENNReal.div_pos (ENNReal.ofReal_ne_zero_iff.mpr sOrder.2.1)
      (volume_openCubeSet_lt_top Q).ne)
    (ENNReal.div_ne_top ENNReal.ofReal_ne_top (volume_openCubeSet_ne_zero' Q)))

/-- The `H¹` gradient's `L²` component and the frozen seminorm finiteness
assemble to the exact inhomogeneous Euclidean `W^{s,2}` predicate. -/
theorem memCubeEuclideanFullWsp_grad_of_memFractionalOn
    (Q : TriadicCube d) (sOrder : FractionalOrder)
    (h : H1Function (openCubeSet Q))
    (hfrac : SubdiffusiveProcess.CoarseGrainingVocab.MemFractionalOn
      (openCubeSet Q) sOrder.1 h.grad) :
    Ch03.ABK26.MemCubeEuclideanFullWsp
      Q sOrder FiniteLpExponent.two h.grad := by
  have hL2vec : MemVectorL2 (cubeSet Q) h.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using h.grad_memVectorL2
  have hLp : MemLp (fun x => HilbertVec.ofVec (h.grad x)) 2
      (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure]
    exact (memHilbertVectorL2_hilbertifyVecField hL2vec).smul_measure
      ENNReal.ofReal_ne_top
  have hraw := rawFractionalENorm_ne_top_of_memFractionalOn Q sOrder h.grad hfrac
  have hrawVec : eLpNorm (cubeEuclideanWspKernel sOrder FiniteLpExponent.two h.grad) 2
      ((volume.restrict (openCubeSet Q)).prod
        (volume.restrict (openCubeSet Q))) ≠ ∞ := by
    rw [← eLpNorm_norm]
    simp_rw [norm_cubeEuclideanWspKernel_two_eq_fractionalKernel]
    exact hraw
  have hsemi : cubeEuclideanWspESeminorm Q sOrder FiniteLpExponent.two h.grad < ∞ := by
    have hvol0 : volume (openCubeSet Q) ≠ 0 := volume_openCubeSet_ne_zero' Q
    rw [cubeEuclideanWspESeminorm, gagliardoCubeMeasure_eq_smul_openProduct,
      show FiniteLpExponent.two.exponent = (2 : ℝ≥0∞) by rfl,
      eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.inv_ne_top.mpr hvol0))
      (lt_top_iff_ne_top.mpr hrawVec)
  exact ⟨hLp, memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top hLp hsemi⟩

/-- On a cube, the frozen normalized fractional seminorm is exactly
`sqrt(s)` times Chapter 3's normalized Euclidean `W^{s,2}` seminorm. -/
theorem fractionalSeminormOn_openCubeSet_eq_sqrt_mul_cubeEuclideanWspESeminorm
    (Q : TriadicCube d) (sOrder : FractionalOrder) (f : Vec d → Vec d) :
    SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
        (openCubeSet Q) sOrder.1 f =
      (ENNReal.ofReal sOrder.1) ^ (1 / 2 : ℝ) *
        cubeEuclideanWspESeminorm Q sOrder FiniteLpExponent.two f := by
  rw [cubeEuclideanWspESeminorm, gagliardoCubeMeasure_eq_smul_openProduct,
    show FiniteLpExponent.two.exponent = (2 : ℝ≥0∞) by rfl,
    eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  rw [← eLpNorm_norm]
  simp_rw [norm_cubeEuclideanWspKernel_two_eq_fractionalKernel]
  unfold SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
  rw [ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num [smul_eq_mul]
  ac_rfl

/-- The real-valued form of the preceding normalization identity. -/
theorem cubeEuclideanWspESeminorm_toReal_eq_rpow_neg_half_mul_fractional
    (Q : TriadicCube d) (sOrder : FractionalOrder) (f : Vec d → Vec d) :
    (cubeEuclideanWspESeminorm Q sOrder FiniteLpExponent.two f).toReal =
      Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
        (SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
          (openCubeSet Q) sOrder.1 f).toReal := by
  have heq := fractionalSeminormOn_openCubeSet_eq_sqrt_mul_cubeEuclideanWspESeminorm
    Q sOrder f
  have hsqrt0 : (ENNReal.ofReal sOrder.1) ^ (1 / 2 : ℝ) ≠ 0 := by
    exact ne_of_gt (ENNReal.rpow_pos
      (ENNReal.ofReal_pos.mpr sOrder.2.1) ENNReal.ofReal_ne_top)
  have hsqrttop : (ENNReal.ofReal sOrder.1) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hsolve : cubeEuclideanWspESeminorm Q sOrder FiniteLpExponent.two f =
      ((ENNReal.ofReal sOrder.1) ^ (1 / 2 : ℝ))⁻¹ *
        SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
          (openCubeSet Q) sOrder.1 f := by
    rw [heq, ← mul_assoc, ENNReal.inv_mul_cancel hsqrt0 hsqrttop, one_mul]
  rw [hsolve, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal sOrder.2.1.le]
  rw [← Real.rpow_neg sOrder.2.1.le]
  congr 1

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
