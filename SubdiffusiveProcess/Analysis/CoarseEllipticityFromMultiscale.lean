import Homogenization.Book.Ch02.MultiscaleEllipticity
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Localization
import Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import Mathlib.Tactic

open Homogenization Homogenization.Book.Ch02

namespace SubdiffusiveProcess




/-- The geometric discount exponent `c = (1 - 3^{-sq})^{2/q}` is nonnegative. -/
theorem aux_sigmaCoarse_trace_c_nonneg (s q : ℝ) (hs : 0 < s) (hq : 1 ≤ q) :
    0 ≤ ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) := by
  have hdisc : 0 ≤ 1 - (3 : ℝ) ^ (-s * q) := by
    have h1 : (3 : ℝ) ^ (-s * q) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · norm_num
      · nlinarith
    linarith
  exact Real.rpow_nonneg hdisc _

/-- The geometric discount exponent `c = (1 - 3^{-sq})^{2/q}` is at most `1`. -/
theorem aux_sigmaCoarse_trace_c_le_one (s q : ℝ) (hs : 0 < s) (hq : 1 ≤ q) :
    ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ≤ 1 := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hdisc_nonneg : 0 ≤ 1 - (3 : ℝ) ^ (-s * q) := by
    have h1 : (3 : ℝ) ^ (-s * q) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · norm_num
      · nlinarith
    linarith
  have hdisc_le_one : 1 - (3 : ℝ) ^ (-s * q) ≤ 1 := by
    have h3pos : 0 < (3 : ℝ) ^ (-s * q) := Real.rpow_pos_of_pos (by norm_num) _
    linarith
  calc ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ≤ (1 : ℝ) ^ (2 / q) := by
        apply Real.rpow_le_rpow hdisc_nonneg hdisc_le_one
        positivity
    _ = 1 := Real.one_rpow _

/-- Diagonal entries of a matrix as a quadratic form against a standard basis vector. -/
theorem aux_sigmaCoarse_trace_vecDot_single_matVecMul {d : ℕ} (A : Mat d) (i : Fin d) :
    vecDot (Pi.single i (1 : ℝ)) (matVecMul A (Pi.single i (1 : ℝ))) = A i i := by
  simp [vecDot, matVecMul, Finset.sum_ite_eq', Pi.single_apply]

/-- Standard basis vectors have unit squared norm. -/
theorem aux_sigmaCoarse_trace_vecNormSq_single {d : ℕ} (i : Fin d) :
    vecNormSq (Pi.single i (1 : ℝ) : Vec d) = 1 := by
  simp [vecNormSq, vecDot, Pi.single_apply, Finset.sum_ite_eq']

/-- The trace of a positive semidefinite matrix is controlled by its dimension times its
operator norm. -/
theorem aux_sigmaCoarse_trace_trace_le_dim_mul_matrixNorm {d : ℕ} [NeZero d] {A : Mat d}
    (hA : A.PosSemidef) :
    Matrix.trace A ≤ (d : ℝ) * matrixNorm A := by
  have hdiag : ∀ i : Fin d, A i i ≤ matrixOperatorNorm A := by
    intro i
    have h := vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef hA
      (Pi.single i (1 : ℝ))
    rw [aux_sigmaCoarse_trace_vecDot_single_matVecMul, aux_sigmaCoarse_trace_vecNormSq_single] at h
    simpa using h
  calc Matrix.trace A = ∑ i, A i i := rfl
    _ ≤ ∑ _i : Fin d, matrixOperatorNorm A := Finset.sum_le_sum fun i _ => hdiag i
    _ = (d : ℝ) * matrixOperatorNorm A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
    _ = (d : ℝ) * matrixNorm A := by rw [matrixNorm_eq_matrixOperatorNorm]

/-- Symmetric coefficient data forces the derived matrix `b` to coincide with `sigma`. -/
theorem aux_sigmaCoarse_trace_bCoarse_eq_sigmaCoarse {d : ℕ} (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (hsym : CoeffOn.IsSymmetric (a.coeffOn Q)) :
    Book.Ch02.bCoarse (cubeDomain Q) (a.coeffOn Q) =
      Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q) :=
  (responseSymmetricDirichletNeumannTheory (cubeDomain Q) (a.coeffOn Q) hsym).derived_matrices.2.2

/-- Under a symmetric coefficient, `sigmaCoarse` is positive semidefinite. -/
theorem aux_sigmaCoarse_trace_sigmaCoarse_posSemidef {d : ℕ} (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (hsym : CoeffOn.IsSymmetric (a.coeffOn Q)) :
    (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)).PosSemidef := by
  rw [← aux_sigmaCoarse_trace_bCoarse_eq_sigmaCoarse Q a hsym]
  exact bCoarse_posSemidef (cubeDomain Q) (a.coeffOn Q)

/-- Under a symmetric coefficient, `‖sigmaCoarse(Q)‖` is controlled by the finite-exponent upper
multiscale ellipticity `Λ_{s,q}(Q)`. -/
theorem aux_sigmaCoarse_trace_sigmaNorm_le_Lambda {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (hsym : CoeffOn.IsSymmetric (a.coeffOn Q)) (s q : ℝ)
    (hs : 0 < s) (hq : 1 ≤ q) :
    matrixNorm (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) ≤ LambdaSqFinite Q s q a := by
  have hcb : coarseBMatrixNorm Q a = matrixNorm (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) := by
    show matrixNorm (Book.Ch02.bCoarse (cubeDomain Q) (a.coeffOn Q)) =
      matrixNorm (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q))
    rw [aux_sigmaCoarse_trace_bCoarse_eq_sigmaCoarse Q a hsym]
  rw [← hcb]
  exact oneCube_b_le_LambdaSq_finite Q a hs hq

/-- Under a symmetric coefficient, `trace(sigmaCoarse(Q))` is controlled by `d` times the
finite-exponent upper multiscale ellipticity `Λ_{s,q}(Q)`. -/
theorem aux_sigmaCoarse_trace_trace_le_dim_mul_Lambda {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (hsym : CoeffOn.IsSymmetric (a.coeffOn Q)) (s q : ℝ)
    (hs : 0 < s) (hq : 1 ≤ q) :
    Matrix.trace (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) ≤
      (d : ℝ) * LambdaSqFinite Q s q a := by
  have h1 := aux_sigmaCoarse_trace_trace_le_dim_mul_matrixNorm
    (aux_sigmaCoarse_trace_sigmaCoarse_posSemidef Q a hsym)
  have h2 := aux_sigmaCoarse_trace_sigmaNorm_le_Lambda Q a hsym s q hs hq
  have hdpos : (0 : ℝ) ≤ (d : ℝ) := by positivity
  calc Matrix.trace (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) ≤
        (d : ℝ) * matrixNorm (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) := h1
    _ ≤ (d : ℝ) * LambdaSqFinite Q s q a := mul_le_mul_of_nonneg_left h2 hdpos

/-- The Euclidean quadratic form of `sigmaStar` is bounded below by `|x|² / ‖sigmaStar⁻¹‖`. -/
theorem aux_sigmaCoarse_trace_sigmaStar_quad_lb {d : ℕ} (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (x : Vec d) :
    vecNormSq x ≤ coarseSigmaStarInvMatrixNorm Q a *
      vecDot x (matVecMul (Book.Ch02.sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x) := by
  have h := vecNormSq_le_matrixOperatorNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    (A := Book.Ch02.sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q))
    (B := Book.Ch02.sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q))
    (sigmaStarInvCoarse_posDef (cubeDomain Q) (a.coeffOn Q)).posSemidef
    (fun ξ => by
      have heq := sigmaStarInvCoarse_mul_sigmaStarCoarse
        (isUnit_det_sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q))
        (U := cubeDomain Q) (a := a.coeffOn Q)
      show (Book.Ch02.sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q)).mulVec
          ((Book.Ch02.sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)).mulVec ξ) = ξ
      rw [Matrix.mulVec_mulVec, heq, Matrix.one_mulVec])
    x
  show vecNormSq x ≤ coarseSigmaStarInvMatrixNorm Q a *
      vecDot x (matVecMul (Book.Ch02.sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x)
  exact h

/-- Löwner order `sigmaStar ≤ sigma`, unwound to the quadratic form (unconditional). -/
theorem aux_sigmaCoarse_trace_sigmaStar_quad_le_sigma_quad {d : ℕ} (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (x : Vec d) :
    vecDot x (matVecMul (Book.Ch02.sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x) ≤
      vecDot x (matVecMul (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) x) := by
  have h := (sigmaStarCoarse_le_sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) x
  linarith

/-- The finite-exponent lower multiscale ellipticity `λ_{s,q}(Q)` times `|x|²` is controlled by
the quadratic form of `sigmaCoarse(Q)` (unconditional, no symmetry needed). -/
theorem aux_sigmaCoarse_trace_lam_mul_normSq_le_quad {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (s q : ℝ) (hs : 0 < s) (hq : 1 ≤ q) (x : Vec d) :
    lambdaSqFinite Q s q a * vecNormSq x ≤
      vecDot x (matVecMul (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) x) := by
  have hNpos : 0 < coarseSigmaStarInvMatrixNorm Q a := coarseSigmaStarInvMatrixNorm_pos Q a
  have hlampos : 0 < lambdaSqFinite Q s q a := lambdaSq_finite_pos Q a hs hq
  have hlamleNinv : lambdaSqFinite Q s q a ≤ (coarseSigmaStarInvMatrixNorm Q a)⁻¹ :=
    lambdaSq_finite_le_oneCube Q a hs hq
  have hquad := aux_sigmaCoarse_trace_sigmaStar_quad_lb Q a x
  have hYnonneg : 0 ≤ vecDot x (matVecMul (Book.Ch02.sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x) := by
    have h := (sigmaStarCoarse_posDef (cubeDomain Q) (a.coeffOn Q)).posSemidef.dotProduct_mulVec_nonneg x
    show (0:ℝ) ≤ vecDot x (matVecMul (Book.Ch02.sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x)
    exact h
  have hYleZ := aux_sigmaCoarse_trace_sigmaStar_quad_le_sigma_quad Q a x
  have hlamN : lambdaSqFinite Q s q a * coarseSigmaStarInvMatrixNorm Q a ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_right hlamleNinv hNpos.le
    rwa [inv_mul_cancel₀ hNpos.ne'] at h1
  calc lambdaSqFinite Q s q a * vecNormSq x
      ≤ lambdaSqFinite Q s q a * (coarseSigmaStarInvMatrixNorm Q a *
          vecDot x (matVecMul (Book.Ch02.sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x)) :=
        mul_le_mul_of_nonneg_left hquad hlampos.le
    _ = (lambdaSqFinite Q s q a * coarseSigmaStarInvMatrixNorm Q a) *
          vecDot x (matVecMul (Book.Ch02.sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x) := by ring
    _ ≤ 1 * vecDot x (matVecMul (Book.Ch02.sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x) :=
        mul_le_mul_of_nonneg_right hlamN hYnonneg
    _ = vecDot x (matVecMul (Book.Ch02.sigmaStarCoarse (cubeDomain Q) (a.coeffOn Q)) x) := one_mul _
    _ ≤ vecDot x (matVecMul (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) x) := hYleZ

/-- The multiplicative core inequality: `c² λ T |x|² ≤ Λ d Z`, with no division. -/
theorem aux_sigmaCoarse_trace_star {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (hsym : CoeffOn.IsSymmetric (a.coeffOn Q)) (s q : ℝ)
    (hs : 0 < s) (hq : 1 ≤ q) (x : Vec d) :
    ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * lambdaSqFinite Q s q a *
        Matrix.trace (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) * vecNormSq x ≤
      LambdaSqFinite Q s q a * (d : ℝ) *
        vecDot x (matVecMul (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) x) := by
  have hc_nonneg := aux_sigmaCoarse_trace_c_nonneg s q hs hq
  have hc_le_one := aux_sigmaCoarse_trace_c_le_one s q hs hq
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    exact_mod_cast this
  have hLampos : 0 < LambdaSqFinite Q s q a := LambdaSq_finite_pos Q a hs hq
  have hlampos : 0 < lambdaSqFinite Q s q a := lambdaSq_finite_pos Q a hs hq
  have hXnonneg : 0 ≤ vecNormSq x := vecNormSq_nonneg x
  have hTleDLam := aux_sigmaCoarse_trace_trace_le_dim_mul_Lambda Q a hsym s q hs hq
  have hlamXleZ := aux_sigmaCoarse_trace_lam_mul_normSq_le_quad Q a s q hs hq x
  have hc2lam_nonneg : 0 ≤ ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * lambdaSqFinite Q s q a :=
    mul_nonneg (sq_nonneg _) hlampos.le
  have hLamd_nonneg : 0 ≤ LambdaSqFinite Q s q a * (d : ℝ) := mul_nonneg hLampos.le hdpos.le
  have hCT : ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * lambdaSqFinite Q s q a *
      Matrix.trace (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) ≤
      (d : ℝ) * lambdaSqFinite Q s q a * LambdaSqFinite Q s q a := by
    calc ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * lambdaSqFinite Q s q a *
          Matrix.trace (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q))
        ≤ ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * lambdaSqFinite Q s q a *
            ((d : ℝ) * LambdaSqFinite Q s q a) :=
          mul_le_mul_of_nonneg_left hTleDLam hc2lam_nonneg
      _ = (d : ℝ) * (((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * lambdaSqFinite Q s q a *
            LambdaSqFinite Q s q a) := by ring
      _ ≤ (d : ℝ) * (lambdaSqFinite Q s q a * LambdaSqFinite Q s q a) := by
          have hc2_le_one : ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 ≤ 1 :=
            pow_le_one₀ hc_nonneg hc_le_one
          have hstep : ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * lambdaSqFinite Q s q a *
              LambdaSqFinite Q s q a ≤ lambdaSqFinite Q s q a * LambdaSqFinite Q s q a := by
            have hprod := mul_le_mul_of_nonneg_right hc2_le_one
              (mul_nonneg hlampos.le hLampos.le)
            calc ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * lambdaSqFinite Q s q a *
                  LambdaSqFinite Q s q a
                = ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 *
                    (lambdaSqFinite Q s q a * LambdaSqFinite Q s q a) := by ring
              _ ≤ 1 * (lambdaSqFinite Q s q a * LambdaSqFinite Q s q a) := hprod
              _ = lambdaSqFinite Q s q a * LambdaSqFinite Q s q a := one_mul _
          exact mul_le_mul_of_nonneg_left hstep hdpos.le
      _ = (d : ℝ) * lambdaSqFinite Q s q a * LambdaSqFinite Q s q a := by ring
  calc ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * lambdaSqFinite Q s q a *
        Matrix.trace (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) * vecNormSq x
      ≤ ((d : ℝ) * lambdaSqFinite Q s q a * LambdaSqFinite Q s q a) * vecNormSq x :=
        mul_le_mul_of_nonneg_right hCT hXnonneg
    _ = LambdaSqFinite Q s q a * (d : ℝ) * (lambdaSqFinite Q s q a * vecNormSq x) := by ring
    _ ≤ LambdaSqFinite Q s q a * (d : ℝ) *
          vecDot x (matVecMul (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) x) :=
        mul_le_mul_of_nonneg_left hlamXleZ hLamd_nonneg

/-- **Coarse-grained ellipticity from multiscale ellipticity.**
A symmetric chart's coarse matrix `σ(Q)` is `c₀`-elliptic relative to its trace, with `c₀`
controlled by the ratio of the finite-exponent multiscale ellipticities `λ_{s,q}(Q)/Λ_{s,q}(Q)`. -/
theorem sigmaCoarse_trace_ellipticity_of_multiscale {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    (hsym : CoeffOn.IsSymmetric (a.coeffOn Q)) (s q : ℝ) (hs : 0 < s) (hq : 1 ≤ q)
    (x : Fin d → ℝ) :
    ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * (lambdaSqFinite Q s q a / LambdaSqFinite Q s q a) /
        (d : ℝ) * Matrix.trace (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) * (x ⬝ᵥ x) ≤
      x ⬝ᵥ (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)).mulVec x := by
  have hLampos : 0 < LambdaSqFinite Q s q a := LambdaSq_finite_pos Q a hs hq
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    exact_mod_cast this
  have hStar := aux_sigmaCoarse_trace_star Q a hsym s q hs hq x
  have hgoaleq :
      ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * (lambdaSqFinite Q s q a / LambdaSqFinite Q s q a) /
          (d : ℝ) * Matrix.trace (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) * vecNormSq x =
      (((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * lambdaSqFinite Q s q a *
          Matrix.trace (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) * vecNormSq x) /
        (LambdaSqFinite Q s q a * (d : ℝ)) := by
    field_simp
  show ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * (lambdaSqFinite Q s q a / LambdaSqFinite Q s q a) /
        (d : ℝ) * Matrix.trace (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) * vecNormSq x ≤
      vecDot x (matVecMul (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) x)
  rw [hgoaleq, div_le_iff₀ (mul_pos hLampos hdpos)]
  calc ((1 - (3 : ℝ) ^ (-s * q)) ^ (2 / q)) ^ 2 * lambdaSqFinite Q s q a *
        Matrix.trace (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) * vecNormSq x
      ≤ LambdaSqFinite Q s q a * (d : ℝ) *
          vecDot x (matVecMul (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) x) := hStar
    _ = vecDot x (matVecMul (Book.Ch02.sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) x) *
          (LambdaSqFinite Q s q a * (d : ℝ)) := by ring

end SubdiffusiveProcess
