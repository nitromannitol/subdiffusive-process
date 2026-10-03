module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BalancedFinalReadout

@[expose] public section

/-!
# Canonical-field final Dirichlet readout

The frozen theorem uses one pair of difference-field witnesses for both its
main and zero-source estimates.  This non-existential form keeps those
canonical witnesses visible across the two rows.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- Direct final readout for the canonical gradient and flux differences. -/
theorem cutoffDirichletCanonicalDifferenceFields_le_of_balancedPrebalance
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (s : FractionalOrder)
    (u v : H1Function (openCubeSet (originCube d 0)))
    (hzero : HasH10Difference (originCube d 0) u v)
    {U T D : ℝ} (hU : 0 ≤ U) (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hpre :
      paperNegativeFractionalDual (originCube d 0) s
            FiniteLpExponent.two
            (scaledCenteredCubePullbackEuclideanL2Field (N : ℤ)
              (centeredCubeScale (N : ℤ))
              (centeredCubeGradientDifferenceL2Field (N : ℤ)
                (centeredCubeRawDilation (N : ℤ) u)
                (centeredCubeRawDilation (N : ℤ) v))) +
          paperNegativeFractionalDual (originCube d 0) s
            FiniteLpExponent.two
            (scaledCenteredCubePullbackEuclideanL2Field (N : ℤ)
              (centeredCubeScale (N : ℤ) * (ahom M L)⁻¹)
              (centeredCubeFluxDifferenceL2Field (N : ℤ)
                ((aCutoffFamily M L omega).coeffOn
                  (originCube d (N : ℤ)))
                (ahom M L) (centeredCubeRawDilation (N : ℤ) u)
                (centeredCubeRawDilation (N : ℤ) v))) ≤
        ENNReal.ofReal (U * T * D)) :
    l2Size (originCube d 0) (fun x ↦ u.toFun x - v.toFun x) +
          ordinaryVectorHMinusOne (originCube d 0)
            (cutoffDirichletGradientDifference N u v) +
        ordinaryVectorHMinusOne (originCube d 0)
          (cutoffDirichletFluxDifference M L N omega u v) ≤
      ENNReal.ofReal (dirichletReadoutRandomFactor s d U * T) *
        ENNReal.ofReal D := by
  have hreadout := dirichletFinalReadout_le_paperNegativeFractionalDual_sum
    s u v (cutoffDirichletGradientDifference N u v)
    (cutoffDirichletFluxDifference M L N omega u v)
    (cutoffDirichletGradientDifference_toFun N u v) hzero
  rw [cutoffDirichletDifferenceFields_paperDual_sum_eq M L N omega s u v]
    at hreadout
  calc
    _ ≤ dirichletFinalReadoutConstant s d * ENNReal.ofReal (U * T * D) :=
      hreadout.trans (by gcongr)
    _ = ENNReal.ofReal
        ((dirichletFinalReadoutConstant s d).toReal * (U * T * D)) := by
      calc
        dirichletFinalReadoutConstant s d * ENNReal.ofReal (U * T * D) =
            ENNReal.ofReal (dirichletFinalReadoutConstant s d).toReal *
              ENNReal.ofReal (U * T * D) := by
                rw [ENNReal.ofReal_toReal
                  (dirichletFinalReadoutConstant_lt_top s d).ne]
        _ = _ := (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
    _ ≤ ENNReal.ofReal (dirichletReadoutRandomFactor s d U * T * D) := by
      apply ENNReal.ofReal_le_ofReal
      unfold dirichletReadoutRandomFactor
      have hTD : 0 ≤ T * D := mul_nonneg hT hD
      have hCU : (dirichletFinalReadoutConstant s d).toReal * U ≤
          1 + (dirichletFinalReadoutConstant s d).toReal * U := by linarith
      calc
        (dirichletFinalReadoutConstant s d).toReal * (U * T * D) =
            ((dirichletFinalReadoutConstant s d).toReal * U) * (T * D) := by ring
        _ ≤ (1 + (dirichletFinalReadoutConstant s d).toReal * U) *
            (T * D) := mul_le_mul_of_nonneg_right hCU hTD
        _ = (1 + (dirichletFinalReadoutConstant s d).toReal * U) * T * D := by ring
    _ = ENNReal.ofReal (dirichletReadoutRandomFactor s d U * T) *
          ENNReal.ofReal D := by
      rw [ENNReal.ofReal_mul]
      exact mul_nonneg
        (zero_le_one.trans (one_le_dirichletReadoutRandomFactor s d hU)) hT

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
