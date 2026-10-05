module

public import Homogenization.Deterministic.WeakNormInterfaces.AECongruence
public import Homogenization.Book.Ch03.Definitions
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum

@[expose] public section

open MeasureTheory Homogenization
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.FractionalAECongruence

/-- The fractional seminorm depends only on the almost-everywhere class. -/
theorem fractionalSeminormOn_congr {d : ℕ} (U : Set (Vec d)) (s : ℝ)
    {f g : Vec d → Vec d} (hfg : f =ᵐ[volume.restrict U] g) :
    SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn U s f =
      SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn U s g := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
  congr 1
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by norm_num) (by norm_num),
    SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by norm_num) (by norm_num)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp hfg,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hfg] with xy hx hy
  simp only [Function.comp_apply] at hx hy
  simp only [SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel, hx, hy]

@[simp] theorem fractionalSeminormOn_zero {d : ℕ} (U : Set (Vec d)) (s : ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn U s (0 : Vec d → Vec d) = 0 := by
  have hk : SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s (0 : Vec d → Vec d) = 0 := by
    funext xy
    simp [SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel, euclideanNorm, vecNormSq, vecDot]
  rw [SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn, hk,
    SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded aestronglyMeasurable_zero, eLpNorm_zero, mul_zero]

/-- Positive vector partial norms are invariant under changes on a null set. -/
theorem positivePartial_congr {d : ℕ} (Q : TriadicCube d) (s : ℝ) (N : ℕ)
    {f g : Vec d → Vec d} (hfg : f =ᵐ[volume.restrict (cubeSet Q)] g) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N f =
      cubeBesovPositiveVectorPartialSeminormTwo Q s N g := by
  unfold cubeBesovPositiveVectorPartialSeminormTwo
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (fun t : ℝ => t ^ 2)
  unfold cubeBesovPositiveVectorDepthSeminorm
  apply congrArg (fun t : ℝ => (3 : ℝ) ^ (s * (j : ℝ)) * Real.sqrt t)
  unfold cubeBesovPositiveVectorDepthAverage descendantsAverage
  apply congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t)
  apply Finset.sum_congr rfl
  intro R hR
  have hRfg : f =ᵐ[volume.restrict (cubeSet R)] g :=
    hfg.filter_mono (ae_mono (Measure.restrict_mono_set volume
      (cubeSet_subset_of_mem_descendantsAtDepth hR)))
  have havg := cubeAverageVec_eq_of_ae_eq_on_cubeSet hRfg
  have hfl : cubeFluctuationVec R f =ᵐ[normalizedCubeMeasure R] cubeFluctuationVec R g := by
    apply Measure.ae_smul_measure
    filter_upwards [hRfg] with x hx
    simp only [cubeFluctuationVec, hx, havg]
  unfold cubeLpNorm
  rw [eLpNorm_congr_ae hfl]

/-- Full positive vector norms respect the same null-set equivalence. -/
theorem positiveNorm_congr {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    {f g : Vec d → Vec d} (hfg : f =ᵐ[volume.restrict (cubeSet Q)] g) :
    Book.Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q s f =
      Book.Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q s g := by
  unfold Book.Ch03.scaleNormalizedPositiveBesovVectorNormTwo
  rw [cubeAverageVec_eq_of_ae_eq_on_cubeSet hfg]
  apply congrArg (fun t : ℝ => Real.sqrt (vecNormSq (cubeAverageVec Q g)) + t)
  unfold Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
    cubeBesovPositiveVectorSeminormTwo
  simp_rw [positivePartial_congr Q s _ hfg]

/-- An almost-everywhere zero vector field has all required Besov regularity. -/
theorem regularity_of_ae_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    {f : Vec d → Vec d} (hf : f =ᵐ[volume.restrict (cubeSet Q)] 0) :
    Book.Ch03.ForceBesovRegularity Q s f := by
  constructor
  · exact (MemLp.zero (μ := normalizedCubeMeasure Q)).ae_eq (Measure.ae_smul_measure hf.symm _)
  · simp_rw [positivePartial_congr Q s _ hf]
    exact cubeBesovPositiveVectorPartialSeminormTwo_zero_bddAbove Q s

@[simp] theorem positiveNorm_zero {d : ℕ} (Q : TriadicCube d) (s : ℝ) :
    Book.Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q s (0 : Vec d → Vec d) = 0 := by
  unfold Book.Ch03.scaleNormalizedPositiveBesovVectorNormTwo
  rw [show cubeAverageVec Q (0 : Vec d → Vec d) = 0 from cubeAverageVec_const Q 0]
  simp [vecNormSq, vecDot]

end SubdiffusiveProcess.FractionalAECongruence
