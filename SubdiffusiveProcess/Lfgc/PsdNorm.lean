module

public import Homogenization.Book.Ch02.MultiscaleEllipticity

@[expose] public section

/-!
# Operator norm of positive semidefinite matrices

For a symmetric positive semidefinite `A` whose quadratic form is bounded by that of a
symmetric `B`, the Euclidean operator norm (`Homogenization.Book.Ch02.matrixNorm`) satisfies
`‖A‖ ≤ ‖B‖`.  The proof is the Cauchy–Schwarz inequality for the semi-inner product
`(x, y) ↦ y · A x`.  The file also records `x · A x ≤ ‖A‖ |x|²`.
It proves nothing about coarse-grained matrices.
-/

open Homogenization Homogenization.Book.Ch02

namespace SubdiffusiveProcess.Lfgc
variable {d : ℕ}

/-- The Euclidean vector with the given coordinates. -/
noncomputable abbrev euc (v : Vec d) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v

theorem norm_euc (v : Vec d) : ‖euc v‖ = Real.sqrt (vecNormSq v) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  unfold vecNormSq vecDot
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.norm_eq_abs, sq_abs, pow_two]

theorem toEuclideanCLM_euc (A : Mat d) (v : Vec d) :
    Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A (euc v) = euc (matVecMul A v) := by
  ext i
  rfl

theorem vecNormSq_nonneg' (v : Vec d) : 0 ≤ vecNormSq v := by
  unfold vecNormSq vecDot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem sqrt_vecNormSq_matVecMul_le (A : Mat d) (v : Vec d) :
    Real.sqrt (vecNormSq (matVecMul A v)) ≤ matrixNorm A * Real.sqrt (vecNormSq v) := by
  have h := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A).le_opNorm (euc v)
  rw [toEuclideanCLM_euc, norm_euc, norm_euc] at h
  exact h

theorem vecNormSq_matVecMul_le (A : Mat d) (v : Vec d) :
    vecNormSq (matVecMul A v) ≤ matrixNorm A ^ 2 * vecNormSq v := by
  have h := sqrt_vecNormSq_matVecMul_le A v
  have hA : 0 ≤ matrixNorm A := norm_nonneg _
  have h2 := mul_self_le_mul_self (Real.sqrt_nonneg _) h
  rw [Real.mul_self_sqrt (vecNormSq_nonneg' _)] at h2
  calc vecNormSq (matVecMul A v) ≤ matrixNorm A * Real.sqrt (vecNormSq v) *
        (matrixNorm A * Real.sqrt (vecNormSq v)) := h2
    _ = matrixNorm A ^ 2 * (Real.sqrt (vecNormSq v) * Real.sqrt (vecNormSq v)) := by ring
    _ = matrixNorm A ^ 2 * vecNormSq v := by rw [Real.mul_self_sqrt (vecNormSq_nonneg' _)]

/-- `x · A x ≤ ‖A‖ |x|²`. -/
theorem quad_le_matrixNorm (A : Mat d) (v : Vec d) :
    vecDot v (matVecMul A v) ≤ matrixNorm A * vecNormSq v := by
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq v (matVecMul A v)
  have hA := vecNormSq_matVecMul_le A v
  have hv := vecNormSq_nonneg' v
  have hnA : 0 ≤ matrixNorm A := norm_nonneg _
  have h1 : vecDot v (matVecMul A v) ^ 2 ≤ (matrixNorm A * vecNormSq v) ^ 2 := by
    calc vecDot v (matVecMul A v) ^ 2 ≤ vecNormSq v * vecNormSq (matVecMul A v) := hcs
      _ ≤ vecNormSq v * (matrixNorm A ^ 2 * vecNormSq v) :=
          mul_le_mul_of_nonneg_left hA hv
      _ = (matrixNorm A * vecNormSq v) ^ 2 := by ring
  exact abs_le_of_sq_le_sq' h1 (mul_nonneg hnA hv) |>.2

theorem vecDot_add_smul_left (v w u : Vec d) (t : ℝ) :
    vecDot (v + t • w) u = vecDot v u + t * vecDot w u := by
  unfold vecDot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem matVecMul_add_smul (A : Mat d) (v w : Vec d) (t : ℝ) :
    matVecMul A (v + t • w) = matVecMul A v + t • matVecMul A w := by
  funext i
  unfold matVecMul
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem vecDot_comm' (v w : Vec d) : vecDot v w = vecDot w v := by
  unfold vecDot
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem vecDot_add_smul_right (v w u : Vec d) (t : ℝ) :
    vecDot u (v + t • w) = vecDot u v + t * vecDot u w := by
  rw [vecDot_comm' u, vecDot_add_smul_left, vecDot_comm' v, vecDot_comm' w]

theorem vecDot_matVecMul_symm (A : Mat d) (hA : A.IsSymm) (v w : Vec d) :
    vecDot v (matVecMul A w) = vecDot w (matVecMul A v) := by
  unfold vecDot matVecMul
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hij : A j i = A i j := by
    have := congrFun (congrFun hA i) j
    simpa [Matrix.transpose_apply] using this
  rw [hij]
  ring

/-- Cauchy–Schwarz for a symmetric positive semidefinite matrix. -/
theorem sq_bilin_le_quad_mul_quad (A : Mat d) (hA : A.IsSymm)
    (hpos : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul A v)) (v w : Vec d) :
    vecDot w (matVecMul A v) ^ 2 ≤
      vecDot v (matVecMul A v) * vecDot w (matVecMul A w) := by
  set a := vecDot w (matVecMul A w)
  set b := vecDot w (matVecMul A v)
  set c := vecDot v (matVecMul A v)
  have hq : ∀ t : ℝ, 0 ≤ a * (t * t) + (2 * b) * t + c := by
    intro t
    have h := hpos (v + t • w)
    rw [matVecMul_add_smul, vecDot_add_smul_left, vecDot_add_smul_right,
      vecDot_add_smul_right] at h
    have hs : vecDot v (matVecMul A w) = b := vecDot_matVecMul_symm A hA v w
    rw [hs] at h
    nlinarith [h]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith [hd]

/-- The operator norm is monotone on positive semidefinite symmetric matrices. -/
theorem matrixNorm_le_of_quad_le (A B : Mat d) (hA : A.IsSymm)
    (hpos : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul A v))
    (hAB : ∀ v : Vec d, vecDot v (matVecMul A v) ≤ vecDot v (matVecMul B v)) :
    matrixNorm A ≤ matrixNorm B := by
  unfold matrixNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  set v : Vec d := WithLp.ofLp x with hvdef
  have hx : x = euc v := rfl
  rw [hx, toEuclideanCLM_euc, norm_euc, norm_euc]
  set nB := ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) B‖
  have hnB : 0 ≤ nB := norm_nonneg _
  set w := matVecMul A v
  -- `|Av|^2 = w·Av`; Cauchy–Schwarz gives `|w|^4 ≤ (v·Av)(w·Aw)`.
  have hww : vecDot w (matVecMul A v) = vecNormSq w := rfl
  have hcs := sq_bilin_le_quad_mul_quad A hA hpos v w
  rw [hww] at hcs
  have h1 : vecDot v (matVecMul A v) ≤ nB * vecNormSq v :=
    (hAB v).trans (quad_le_matrixNorm B v)
  have h2 : vecDot w (matVecMul A w) ≤ nB * vecNormSq w :=
    (hAB w).trans (quad_le_matrixNorm B w)
  have hv0 := vecNormSq_nonneg' v
  have hw0 := vecNormSq_nonneg' w
  have hqv := hpos v
  have hqw := hpos w
  have hmain : vecNormSq w ≤ nB ^ 2 * vecNormSq v := by
    by_cases hw : vecNormSq w = 0
    · rw [hw]; positivity
    · have hwpos : 0 < vecNormSq w := lt_of_le_of_ne hw0 (Ne.symm hw)
      have h3 : vecNormSq w ^ 2 ≤ (nB * vecNormSq v) * (nB * vecNormSq w) :=
        hcs.trans (mul_le_mul h1 h2 hqw (mul_nonneg hnB hv0))
      have h4 : vecNormSq w * vecNormSq w ≤ (nB ^ 2 * vecNormSq v) * vecNormSq w := by
        nlinarith [h3]
      exact le_of_mul_le_mul_right h4 hwpos
  calc Real.sqrt (vecNormSq w) ≤ Real.sqrt (nB ^ 2 * vecNormSq v) := Real.sqrt_le_sqrt hmain
    _ = nB * Real.sqrt (vecNormSq v) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnB]

end SubdiffusiveProcess.Lfgc
