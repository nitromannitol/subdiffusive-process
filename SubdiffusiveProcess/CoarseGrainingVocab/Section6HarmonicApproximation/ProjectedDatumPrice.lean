module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryDatumPrice

@[expose] public section

/-!
# Projected boundary-datum prices

This file exposes the two exact readouts needed after
`exists_projectedBoundaryCellEnergy`: the source sign disappears from the
positive Besov seminorm, and the stored Dirichlet boundary gradient is the
translated ambient gradient.

PROVENANCE: the sign argument is the private lemma
`cubeBesovPositiveVectorSeminormTwo_neg_of_memLp` in CoarseGraining's
`LocalCoarseGrainingOneCube.lean`; the boundary readout mirrors
`Algsuperdiff/Section4/Provider/ExcessDecay/CoarseDatumPricing.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The concrete positive `q=2` seminorm is insensitive to the sign of a
locally square-integrable vector field. -/
theorem scaleNormalizedPositiveBesovVectorSeminormTwo_neg_of_memLp
    (Q : TriadicCube d) (s : ℝ) (g : Vec d → Vec d)
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s (fun x => -g x) =
      scaleNormalizedPositiveBesovVectorSeminormTwo Q s g := by
  unfold scaleNormalizedPositiveBesovVectorSeminormTwo
  unfold cubeBesovPositiveVectorSeminormTwo
  have hpartial : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun x => -g x) =
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g := by
    intro N
    unfold cubeBesovPositiveVectorPartialSeminormTwo
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    unfold cubeBesovPositiveVectorDepthSeminorm
    apply congrArg (fun x : ℝ =>
      (Real.rpow (3 : ℝ) (s * (j : ℝ)) * Real.sqrt x) ^ 2)
    unfold cubeBesovPositiveVectorDepthAverage
    dsimp only [descendantsAverage]
    congr 1
    apply Finset.sum_congr rfl
    intro R hR
    have hRmem : MemLp g 2 (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic (E := Vec d) hR hg
    have hzero : MemLp (0 : Vec d → Vec d) 2
        (normalizedCubeMeasure R) := by simp
    have havg : cubeAverageVec R (fun x => -g x) = -cubeAverageVec R g := by
      have hzeroavg : cubeAverageVec R (0 : Vec d → Vec d) = 0 := by
        funext i
        simp [cubeAverageVec, cubeAverage]
      simpa [hzeroavg] using
        (cubeAverageVec_sub_memLp R (0 : Vec d → Vec d) g hzero hRmem)
    have hfluct : cubeFluctuationVec R (fun x => -g x) =
        fun x => -(cubeFluctuationVec R g x) := by
      funext x
      rw [cubeFluctuationVec_apply, cubeFluctuationVec_apply, havg]
      abel
    rw [hfluct]
    unfold cubeLpNorm
    change (eLpNorm (-(cubeFluctuationVec R g)) 2
      (normalizedCubeMeasure R)).toReal ^ 2 = _
    rw [eLpNorm_neg]
  simp_rw [hpartial]

/-- The projected source seminorm is priced by the unsigned ambient source
seminorm on the manuscript window. -/
theorem projectedForceSeminorm_le_window
    [NeZero d]
    (Q : TriadicCube d) (c : Vec d) (U : Set (Vec d))
    (s : FractionalOrder) (g g0 : Vec d → Vec d)
    (hgLocal : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two (fun x => g (x + c)))
    (hg0 : ∀ x, g0 x = g (x + c))
    (hsub : translateSet c (openCubeSet Q) ⊆ U)
    (hQ0 : volume (translateSet c (openCubeSet Q)) ≠ 0)
    (hQtop : volume (translateSet c (openCubeSet Q)) ≠ ∞)
    (hU0 : volume U ≠ 0) (hUtop : volume U ≠ ∞)
    (hUfin : fractionalSeminormOn U s.1 g ≠ ∞) :
    scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 (fun x => -g0 x) ≤
      caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s.1) Q *
        (Real.rpow s.1 (-(1 / 2 : ℝ)) *
          (Real.sqrt ((volume U).toReal /
              (volume (translateSet c (openCubeSet Q))).toReal) *
            (fractionalSeminormOn U s.1 g).toReal)) := by
  have hgeq : g0 = fun x => g (x + c) := funext hg0
  rw [hgeq,
    scaleNormalizedPositiveBesovVectorSeminormTwo_neg_of_memLp Q s.1
      (fun x => g (x + c))
      (Ch03.ABK26.MemCubeEuclideanFullWsp.memLpTwo (by norm_num) hgLocal)]
  exact scaleNormalizedPositiveBesovVectorSeminormTwo_translate_le_window
    Q c U s g hgLocal hsub hQ0 hQtop hU0 hUtop hUfin

/-- The projected boundary-gradient norm is exactly the translated ambient
gradient norm and hence obeys the full datum price on the manuscript window. -/
theorem projectedBoundaryNorm_le_window
    [NeZero d]
    (Q : TriadicCube d) (c : Vec d) (U : Set (Vec d))
    (s : FractionalOrder) (D : ℝ) (hgrad : Vec d → Vec d)
    (h0 : H1Function (openCubeSet Q))
    (A : CoeffFamily d) (g0 : Vec d → Vec d)
    (v : DirichletForcedCubeSolution Q A g0)
    (hv : v.boundaryData = h0)
    (hh0 : ∀ x, h0.grad x = hgrad (x + c))
    (hhLocal : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two (fun x => hgrad (x + c)))
    (hsub : translateSet c (openCubeSet Q) ⊆ U)
    (hUmeas : MeasurableSet U)
    (hU0 : 0 < volume U) (hUtop : volume U ≠ ∞)
    (hPpos : 0 < (volume (translateSet c (openCubeSet Q))).toReal)
    (hdiam : ∀ x ∈ U, ∀ y ∈ U, euclideanNorm (x - y) ≤ D)
    (hhU : MemLp (fun x => HilbertVec.ofVec (hgrad x)) 2
      (volume.restrict U))
    (hUfin : fractionalSeminormOn U s.1 hgrad ≠ ∞) :
    scaleNormalizedPositiveBesovVectorNormTwo Q s.1
        (dirichletBoundaryGradientField v) ≤
      Real.sqrt ((volume U).toReal /
          (volume (translateSet c (openCubeSet Q))).toReal) *
        (D ^ (s.1 + (d : ℝ) / 2) * s.1 ^ (-(1 / 2 : ℝ)) *
          (volume U).toReal ^ (-(1 / 2 : ℝ)) *
            (fractionalSeminormOn U s.1 hgrad).toReal) +
      euclideanNorm (averageVecOn U hgrad) +
      caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s.1) Q *
        (Real.rpow s.1 (-(1 / 2 : ℝ)) *
          (Real.sqrt ((volume U).toReal /
              (volume (translateSet c (openCubeSet Q))).toReal) *
            (fractionalSeminormOn U s.1 hgrad).toReal)) := by
  have heq : dirichletBoundaryGradientField v =
      fun x => hgrad (x + c) := by
    funext x
    rw [dirichletBoundaryGradientField, hv, hh0]
  rw [heq]
  exact scaleNormalizedPositiveBesovVectorNormTwo_translate_le_window
    Q c U s D hgrad hhLocal hsub hUmeas hU0 hUtop hPpos hdiam hhU hUfin

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
