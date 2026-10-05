module

public import SubdiffusiveProcess.Paper.lem_as_coarse_deep_grid
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
open Homogenization.Book.Ch02
open Homogenization (vecDot matVecMul)

/-- A coordinate response bank bounds the primal coarse operator norm. -/
theorem aux_lem_as_coarse_shallow_grid_matrix_bank_b_norm {d : ℕ} [NeZero d]
    (Jc : in_J d) (U : Domain d) (a : CoeffOn U)
    (hs : CoeffOn.IsSymmetric a) (K : ℝ)
    (hbank : ∀ i : Fin d, responseJ U a (Pi.single i 1) 0 ≤ K) :
    matrixNorm (bCoarse U a) ≤ 2 * (d : ℝ) * K := by
  have ht := responseSymmetricDirichletNeumannTheory U a hs
  have hb : bCoarse U a = sigmaCoarse U a := ht.derived_matrices.2.2
  rw [hb]
  calc
    matrixNorm (sigmaCoarse U a) ≤ Matrix.trace (sigmaCoarse U a) :=
      matrixNorm_le_trace_of_posSemidef _ (hb ▸ bCoarse_posSemidef U a)
    _ = ∑ i : Fin d, 2 * responseJ U a (Pi.single i 1) 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have h := (aux_lem_as_coarse_deep_grid_J_slices Jc U a hs (Pi.single i 1)).1
      have hdiag : vecDot (Pi.single i (1 : ℝ))
          (matVecMul (sigmaCoarse U a) (Pi.single i 1)) = sigmaCoarse U a i i := by
        simp [vecDot, matVecMul, Pi.single_apply]
      rw [hdiag] at h
      simp only [Matrix.diag_apply]
      linarith
    _ ≤ ∑ _i : Fin d, 2 * K := Finset.sum_le_sum fun i _ => by
      exact mul_le_mul_of_nonneg_left (hbank i) (by norm_num)
    _ = 2 * (d : ℝ) * K := by simp; ring

/-- The dual coordinate response bank bounds the inverse Neumann matrix norm. -/
theorem aux_lem_as_coarse_shallow_grid_matrix_bank_star_norm {d : ℕ} [NeZero d]
    (Jc : in_J d) (U : Domain d) (a : CoeffOn U)
    (hs : CoeffOn.IsSymmetric a) (K : ℝ)
    (hbank : ∀ i : Fin d, responseJ U a 0 (Pi.single i 1) ≤ K) :
    matrixNorm (sigmaStarInvCoarse U a) ≤ 2 * (d : ℝ) * K := by
  calc
    matrixNorm (sigmaStarInvCoarse U a) ≤ Matrix.trace (sigmaStarInvCoarse U a) :=
      matrixNorm_le_trace_of_posSemidef _ (sigmaStarInvCoarse_posDef U a).posSemidef
    _ = ∑ i : Fin d, 2 * responseJ U a 0 (Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := (aux_lem_as_coarse_deep_grid_J_slices Jc U a hs (Pi.single i 1)).2
      have hdiag : vecDot (Pi.single i (1 : ℝ))
          (matVecMul (sigmaStarInvCoarse U a) (Pi.single i 1)) =
          sigmaStarInvCoarse U a i i := by
        simp [vecDot, matVecMul, Pi.single_apply]
      rw [hdiag] at h
      simp only [Matrix.diag_apply]
      linarith
    _ ≤ ∑ _i : Fin d, 2 * K := Finset.sum_le_sum fun i _ => by
      exact mul_le_mul_of_nonneg_left (hbank i) (by norm_num)
    _ = 2 * (d : ℝ) * K := by simp; ring

/-- Pure coordinate responses bound both coarse matrix norms on a triadic cell. -/
theorem lem_as_coarse_shallow_grid_matrix_bank {d : ℕ} [NeZero d]
    (Jc : in_J d) (Q : Homogenization.TriadicCube d) (A : TriadicCoeffFamily d)
    (hs : CoeffOn.IsSymmetric (A.coeffOn Q)) (Kb Ks : ℝ)
    (hb : ∀ i : Fin d,
      responseJ (cubeDomain Q) (A.coeffOn Q) (Pi.single i 1) 0 ≤ Kb)
    (hstar : ∀ i : Fin d,
      responseJ (cubeDomain Q) (A.coeffOn Q) 0 (Pi.single i 1) ≤ Ks) :
    coarseBMatrixNorm Q A + coarseSigmaStarInvMatrixNorm Q A ≤
      2 * (d : ℝ) * (Kb + Ks) := by
  have hB := aux_lem_as_coarse_shallow_grid_matrix_bank_b_norm Jc (cubeDomain Q)
    (A.coeffOn Q) hs Kb hb
  have hS := aux_lem_as_coarse_shallow_grid_matrix_bank_star_norm Jc (cubeDomain Q)
    (A.coeffOn Q) hs Ks hstar
  unfold coarseBMatrixNorm coarseSigmaStarInvMatrixNorm
  nlinarith

end SubdiffusiveProcess.Paper

