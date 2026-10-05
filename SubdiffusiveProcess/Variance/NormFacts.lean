module

public import SubdiffusiveProcess.Variance.MatrixChain

@[expose] public section

/-!
# Operator-norm facts for the variance algebra

`matrixNorm A = ‖Matrix.toEuclideanCLM A‖` is the operator norm of the paper's Section 1.5.
-/

open Homogenization Homogenization.Book.Ch02

namespace SubdiffusiveProcess.Variance

variable {d : ℕ}

theorem matrixNorm_sub_le (A B : Mat d) : matrixNorm (A - B) ≤ matrixNorm A + matrixNorm B := by
  unfold matrixNorm
  rw [map_sub]
  exact norm_sub_le _ _

theorem matrixNorm_add_le (A B : Mat d) : matrixNorm (A + B) ≤ matrixNorm A + matrixNorm B := by
  unfold matrixNorm
  rw [map_add]
  exact norm_add_le _ _

theorem abs_entry_le_matrixNorm (A : Mat d) (i j : Fin d) : |A i j| ≤ matrixNorm A := by
  classical
  have h := SubdiffusiveProcess.Lfgc.sqrt_vecNormSq_matVecMul_le A (Pi.single j 1)
  have h1 : vecNormSq (Pi.single j (1 : ℝ) : Vec d) = 1 := by
    simp [vecNormSq, vecDot, Pi.single_apply]
  rw [h1, Real.sqrt_one, mul_one] at h
  have h2 : (matVecMul A (Pi.single j 1) i) ^ 2 ≤ vecNormSq (matVecMul A (Pi.single j 1)) := by
    unfold vecNormSq vecDot
    have := Finset.single_le_sum (f := fun k => matVecMul A (Pi.single j 1) k *
      matVecMul A (Pi.single j 1) k) (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)
    simpa [sq] using this
  have h3 : |matVecMul A (Pi.single j 1) i| ≤ Real.sqrt (vecNormSq (matVecMul A (Pi.single j 1))) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h2
  have h4 : matVecMul A (Pi.single j 1) i = A i j := by
    simp [matVecMul, Pi.single_apply]
  rw [h4] at h3
  exact h3.trans h

/-- The operator norm of a positive semidefinite symmetric matrix with quadratic form bounded by
`c |v|²` is at most `c`. -/
theorem matrixNorm_le_of_quad_le_const [NeZero d] {A : Mat d} {c : ℝ} (hA : A.IsSymm)
    (hpos : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul A v))
    (hle : ∀ v : Vec d, vecDot v (matVecMul A v) ≤ c * vecNormSq v) : matrixNorm A ≤ c := by
  have hc : 0 ≤ c := by
    have h := hpos (Pi.single (0 : Fin d) 1)
    have h1 := hle (Pi.single (0 : Fin d) 1)
    have h2 : vecNormSq (Pi.single (0 : Fin d) (1 : ℝ) : Vec d) = 1 := by
      classical
      simp [vecNormSq, vecDot, Pi.single_apply]
    rw [h2] at h1
    linarith
  have h := SubdiffusiveProcess.Lfgc.matrixNorm_le_of_quad_le A (c • (1 : Mat d)) hA hpos
    (fun v => by
      rw [quad_smul]
      have : vecDot v (matVecMul (1 : Mat d) v) = vecNormSq v := by
        simp [vecDot, matVecMul, vecNormSq, Matrix.one_apply]
      rw [this]
      exact hle v)
  refine h.trans ?_
  unfold matrixNorm
  rw [map_smul, map_one]
  calc ‖c • (1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖
      ≤ ‖c‖ * ‖(1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ = c := by rw [mul_one, Real.norm_of_nonneg hc]

end SubdiffusiveProcess.Variance
