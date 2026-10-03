module

public import SubdiffusiveProcess.Paper.in_J

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_J_responseJ_split (d : ℕ) (hd : 2 ≤ d) :
    (∀ (U : Homogenization.Book.Ch02.Domain d)
      (a : Homogenization.Book.Ch02.CoeffOn U),
      Homogenization.Book.Ch02.CoeffOn.IsSymmetric a →
      ∀ p q : Homogenization.Vec d,
      Homogenization.Book.Ch02.responseJ U a p q =
        (1 / 2 : ℝ) * Homogenization.vecDot p
            (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) p) +
          (1 / 2 : ℝ) * Homogenization.vecDot q
            (Homogenization.matVecMul
              (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) q) -
          Homogenization.vecDot p q) := by
  intro U a ha p q
  rw [Homogenization.Book.Ch02.responseJ_eq_canonical_coarseMatrices_formula
      (Homogenization.Book.Ch02.canonicalResponseMatrixIdentities U a) p q,
    (Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U a ha).kappa_eq_zero]
  have hzero : Homogenization.matVecMul (0 : Homogenization.Mat d) p = 0 := by
    funext i
    simp [Homogenization.matVecMul]
  rw [hzero]
  simp

end Paper
