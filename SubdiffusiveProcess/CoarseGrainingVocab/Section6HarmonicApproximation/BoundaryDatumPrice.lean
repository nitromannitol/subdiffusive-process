/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.DatumPricing
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalPoincare

/-!
# Pricing the full projected boundary datum

The Chapter-3 Dirichlet RHS uses a full positive Besov norm: the cube mean
plus the positive seminorm.  This file prices the mean by local Euclidean
`L²`, transports that `L²` to the ambient truncated window, and combines it
with `DatumPricing` for the seminorm.

PROVENANCE: this is the composition in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryDatumTransport.lean` and
`CoarseDatumPricing.lean`, with the GMC frozen fractional normalization.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The cube average after recentering is the volume average on the translated
open cube. -/
theorem cubeAverageVec_comp_add_eq_averageVecOn_translateSet
    (Q : TriadicCube d) (c : Vec d) (f : Vec d → Vec d) :
    cubeAverageVec Q (fun x => f (x + c)) =
      averageVecOn (translateSet c (openCubeSet Q)) f := by
  funext i
  unfold cubeAverageVec cubeAverage averageVecOn volumeAverage
  rw [volume_translateSet_eq, volume_openCubeSet_toReal]
  congr 1
  calc
    ∫ x in cubeSet Q, f (x + c) i ∂volume =
        ∫ x in openCubeSet Q, f (x + c) i ∂volume := by
      rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    _ = ∫ x in translateSet c (openCubeSet Q), f x i ∂volume :=
      setIntegral_comp_addRight_translateSet c (openCubeSet Q) (fun x => f x i)

/-- The full positive Besov norm of a recentered boundary field, priced by
the ambient mean, ambient fractional fluctuation, and the already-landed
positive-seminorm comparison. -/
theorem scaleNormalizedPositiveBesovVectorNormTwo_translate_le_window
    (Q : TriadicCube d) (c : Vec d) (U : Set (Vec d))
    (s : FractionalOrder) (D : ℝ) (f : Vec d → Vec d)
    (hfLocal : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two (fun x => f (x + c)))
    (hsub : translateSet c (openCubeSet Q) ⊆ U)
    (hUmeas : MeasurableSet U)
    (hU0 : 0 < volume U) (hUtop : volume U ≠ ∞)
    (hPpos : 0 < (volume (translateSet c (openCubeSet Q))).toReal)
    (hdiam : ∀ x ∈ U, ∀ y ∈ U, euclideanNorm (x - y) ≤ D)
    (hfU : MemLp (fun x => HilbertVec.ofVec (f x)) 2 (volume.restrict U))
    (hUfin : fractionalSeminormOn U s.1 f ≠ ∞) :
    scaleNormalizedPositiveBesovVectorNormTwo Q s.1 (fun x => f (x + c)) ≤
      Real.sqrt ((volume U).toReal /
          (volume (translateSet c (openCubeSet Q))).toReal) *
        (D ^ (s.1 + (d : ℝ) / 2) * s.1 ^ (-(1 / 2 : ℝ)) *
          (volume U).toReal ^ (-(1 / 2 : ℝ)) *
            (fractionalSeminormOn U s.1 f).toReal) +
      euclideanNorm (averageVecOn U f) +
      caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s.1) Q *
        (Real.rpow s.1 (-(1 / 2 : ℝ)) *
          (Real.sqrt ((volume U).toReal /
              (volume (translateSet c (openCubeSet Q))).toReal) *
            (fractionalSeminormOn U s.1 f).toReal)) := by
  let P := translateSet c (openCubeSet Q)
  have hUreal : 0 < (volume U).toReal := ENNReal.toReal_pos hU0.ne' hUtop
  have hP0 : volume P ≠ 0 := (ENNReal.toReal_ne_zero.mp hPpos.ne').1
  have hPtop : volume P ≠ ∞ := (ENNReal.toReal_ne_zero.mp hPpos.ne').2
  have hfP : MemLp (fun x => HilbertVec.ofVec (f x)) 2 (volume.restrict P) :=
    hfU.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hmeanLocal := euclideanNorm_averageVecOn_le_vectorNormalizedL2On hPpos hfP
  have hlocal := vectorNormalizedL2On_subwindow_le_mean_add_fractional
    hsub hUmeas hU0 hUtop hPpos s.2.1 hdiam hfU hUfin
  have hmean : Real.sqrt (vecNormSq
      (cubeAverageVec Q (fun x => f (x + c)))) ≤
      Real.sqrt ((volume U).toReal / (volume P).toReal) *
        (D ^ (s.1 + (d : ℝ) / 2) * s.1 ^ (-(1 / 2 : ℝ)) *
          (volume U).toReal ^ (-(1 / 2 : ℝ)) *
            (fractionalSeminormOn U s.1 f).toReal) +
        euclideanNorm (averageVecOn U f) := by
    rw [cubeAverageVec_comp_add_eq_averageVecOn_translateSet]
    change euclideanNorm (averageVecOn P f) ≤ _
    exact hmeanLocal.trans hlocal
  have hsemi := scaleNormalizedPositiveBesovVectorSeminormTwo_translate_le_window
    Q c U s f hfLocal hsub hP0 hPtop hU0.ne' hUtop hUfin
  unfold scaleNormalizedPositiveBesovVectorNormTwo
  exact add_le_add hmean hsemi

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
