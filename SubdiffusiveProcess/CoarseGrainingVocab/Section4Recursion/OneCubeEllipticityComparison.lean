module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ScalarErrorComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.LowerEllipticityComparison
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorControl

@[expose] public section

/-!
# Provider: the upper half of `l.mathcal.E.to.Lambdas` at `q = 2`

This file proves a local version of the second inequality in the display
`e.bound.Lambdas.by.Es`
of ABK26 in the case `q = 2`:

> `max{σ₀^{-1} Λ_{s,2}(□_m;a), σ₀ λ_{s,2}^{-1}(□_m;a)}
>  ≤ 1 + 2 𝓔_{s,∞,2}(□_m;a,σ₀)² + 2^{1/2} 𝓔_{s,∞,2}(□_m;a,σ₀)`.

The lower half is `ToLambdas.lean`; the two halves are assembled here in
`bound_max_weightedEllipticity_by_homogenizationErrorOnCube_infinity_two`.

## Proof route

The printed proof runs through the operator inequalities
`e.xminusonetimesxminusonesquared.sstar` and
`e.xminusonetimesxminusonesquared.b`, reads off the eigenvalue function
`f(x) = x^{-1}(x-1)^2` on an eigenvector of `σ₀ σ_*^{-1}(U;a)`, and optimizes in
`ε`.  Here the same estimate is obtained without any spectral decomposition:

* both printed operator inequalities are equivalent, on each vector `u`, to the
  single scalar statement `f(P) ≤ P + R - 2` and `f(R) ≤ P + R - 2` for the two
  normalized quadratic forms `P = σ⁻¹ u·b(U;a)u` and `R = σ u·σ_*^{-1}(U;a)u`,
  which by `invMulSubOneSq_le_add_sub_two` only needs `1 ≤ P * R`;
* `1 ≤ P * R` is Cauchy--Schwarz for the positive definite form `σ_*(U;a)`
  together with `σ_*(U;a) ≤ b(U;a)` in the Löwner order;
* `P + R - 2 ≤ 2 max_{|e|=1} J` is the first inequality of the printed
  `e.J.by.f`, obtained here from the reflection identity of `ToLambdas.lean` at
  the half-probe `(u, 0)`;
* the Euclidean operator norms `|b|` and `|σ_*^{-1}|` are recovered from the
  quadratic forms because both matrices are positive semidefinite.

## Main results

* `vecDot_bCoarse_add_vecDot_sigmaStarInvCoarse_sub_two_le`
  (the first inequality of `e.J.by.f`, in quadratic-form shape)
* `inv_mul_coarseBMatrixNorm_le_one_add_add_sqrt` and
  `mul_coarseSigmaStarInvMatrixNorm_le_one_add_add_sqrt`
  (the sharp one-cube upper bounds)
* `inv_mul_LambdaSq_le` and `mul_lambdaSq_inv_le` (aggregated `ε`-forms)
* `max_weightedEllipticity_le_one_add_two_mul_sq_add_sqrt_two_mul`
  (the second inequality of `e.bound.Lambdas.by.Es` at `q = 2`)

## References

* ABK26.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison

open Homogenization

/-! ## Quadratic forms and the Euclidean operator norm -/

/-- A quadratic form bounded on the unit sphere is bounded everywhere, by
homogeneity. -/
theorem vecDot_matVecMul_le_mul_vecNormSq {d : ℕ} {A : Mat d} {c : ℝ}
    (h : ∀ u : Vec d, vecNormSq u = 1 → vecDot u (matVecMul A u) ≤ c)
    (x : Vec d) :
    vecDot x (matVecMul A x) ≤ c * vecNormSq x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [vecNormSq, vecDot, matVecMul]
  · have hpos : 0 < vecNormSq x :=
      lt_of_le_of_ne (vecNormSq_nonneg x) fun h0 => hx (vecNormSq_eq_zero h0.symm)
    obtain ⟨t, htpos, hts⟩ : ∃ t : ℝ, 0 < t ∧ t ^ 2 = vecNormSq x :=
      ⟨Real.sqrt (vecNormSq x), Real.sqrt_pos.2 hpos,
        Real.sq_sqrt (vecNormSq_nonneg x)⟩
    have hu : vecNormSq (t⁻¹ • x) = 1 := by
      rw [vecNormSq_smul, ← hts]
      field_simp
    have hq := h _ hu
    rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right] at hq
    calc
      vecDot x (matVecMul A x)
          = t ^ 2 * (t⁻¹ * (t⁻¹ * vecDot x (matVecMul A x))) := by
            field_simp
      _ ≤ t ^ 2 * c := mul_le_mul_of_nonneg_left hq (sq_nonneg t)
      _ = c * vecNormSq x := by rw [hts]; ring

/-- For a positive semidefinite matrix, a bound for the quadratic form on the
unit sphere bounds the Euclidean operator norm. -/
theorem matrixNorm_le_of_forall_unit {d : ℕ} [NeZero d] {A : Mat d}
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ u : Vec d, vecNormSq u = 1 → vecDot u (matVecMul A u) ≤ c) :
    Book.Ch02.matrixNorm A ≤ c := by
  have hquad : ∀ x : Vec d,
      vecDot x (matVecMul (c • (1 : Mat d)) x) = c * vecNormSq x := by
    intro x
    have hone : matVecMul (1 : Mat d) x = x := by
      funext i
      simp [matVecMul, Matrix.one_apply]
    rw [smul_matVecMul, vecDot_smul_right, hone]
    rfl
  have hloew : MatLoewnerLE A (c • (1 : Mat d)) := by
    intro x
    have hx := vecDot_matVecMul_le_mul_vecNormSq h x
    rw [hquad x]
    linarith
  have hsymm : (c • (1 : Mat d)).IsSymm := by
    simp [Matrix.IsSymm]
  have hpsd : (c • (1 : Mat d)).PosSemidef :=
    Book.Ch02.posSemidef_of_matLoewnerLE_of_posSemidef_of_isSymm hA hsymm hloew
  calc
    Book.Ch02.matrixNorm A ≤ Book.Ch02.matrixNorm (c • (1 : Mat d)) :=
      Book.Ch02.matrixNorm_le_of_matLoewnerLE_of_posSemidef hA hpsd hloew
    _ = c := by
      rw [Book.Ch02.matrixNorm_eq_matrixOperatorNorm,
        Book.Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hc]

/-! ## The product of the two coarse quadratic forms -/

/-- Cauchy--Schwarz for the positive definite form `σ_*(U;a)`, combined with the
Löwner bound `σ_*(U;a) ≤ b(U;a)`: the quadratic forms of `b(U;a)` and
`σ_*^{-1}(U;a)` have product at least `|u|⁴`.

This is the vector-level content of the two printed operator inequalities
`e.xminusonetimesxminusonesquared.sstar` and
`e.xminusonetimesxminusonesquared.b` (ABK26). -/
theorem sq_vecNormSq_le_vecDot_bCoarse_mul_vecDot_sigmaStarInvCoarse {d : ℕ}
    (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) (u : Vec d) :
    vecNormSq u ^ 2 ≤
      vecDot u (matVecMul (Book.Ch02.bCoarse U a) u) *
        vecDot u (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) u) := by
  have hdet : IsUnit (Book.Ch02.sigmaStarInvCoarse U a).det :=
    Book.Ch02.isUnit_det_sigmaStarInvCoarse U a
  have hstar_nonneg : ∀ ξ : Vec d,
      0 ≤ vecDot ξ (matVecMul (Book.Ch02.sigmaStarCoarse U a) ξ) := by
    intro ξ
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      (Book.Ch02.sigmaStarCoarse_posDef U a).posSemidef.dotProduct_mulVec_nonneg ξ
  have hinv : matVecMul (Book.Ch02.sigmaStarCoarse U a)
      (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) u) = u := by
    rw [matVecMul_mul, Book.Ch02.sigmaStarCoarse_mul_sigmaStarInvCoarse hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hCS := Homogenization.sq_vecDot_matVecMul_le_of_isSymm_of_nonneg
    (Book.Ch02.sigmaStarCoarse_isSymm U a) hstar_nonneg u
    (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) u)
  rw [hinv] at hCS
  rw [vecDot_comm (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) u) u] at hCS
  have hLoew : vecDot u (matVecMul (Book.Ch02.sigmaStarCoarse U a) u) ≤
      vecDot u (matVecMul (Book.Ch02.bCoarse U a) u) := by
    have h1 := Book.Ch02.sigmaStarCoarse_le_sigmaCoarse U a u
    have h2 := Book.Ch02.sigmaCoarse_le_bCoarse U a u
    linarith
  have hs_nonneg : 0 ≤ vecDot u (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) u) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      (Book.Ch02.sigmaStarInvCoarse_posDef U a).posSemidef.dotProduct_mulVec_nonneg u
  calc
    vecNormSq u ^ 2 = vecDot u u ^ 2 := rfl
    _ ≤ vecDot u (matVecMul (Book.Ch02.sigmaStarCoarse U a) u) *
          vecDot u (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) u) := hCS
    _ ≤ vecDot u (matVecMul (Book.Ch02.bCoarse U a) u) *
          vecDot u (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) u) :=
        mul_le_mul_of_nonneg_right hLoew hs_nonneg

/-! ## The first inequality of `e.J.by.f` -/

/-- The normalized block-response value set of a scalar comparator is bounded
above, by the one-cube estimate of `ToLambdas.lean`. -/
theorem normalizedBlockResponseValueSet_scalarMatrix_bddAbove {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) {σ : ℝ}
    (hσ : 0 < σ) :
    BddAbove
      (Book.Ch02.normalizedBlockResponseValueSet Q F (scalarMatrix (d := d) σ)) := by
  refine ⟨σ⁻¹ * Book.Ch02.coarseBMatrixNorm Q F +
    σ * Book.Ch02.coarseSigmaStarInvMatrixNorm Q F - 2, ?_⟩
  rintro y ⟨e, he, rfl⟩
  have hnorm :
      vecNormSq (fun i => e (Sum.inl i)) + vecNormSq (fun i => e (Sum.inr i)) = 1 := by
    rw [← fullBlockVecNormSq_eq_add]
    exact he
  rw [ofFullBlockVec_constantFullBlockMatrixInvSqrt_scalarMatrix hσ,
    ofFullBlockVec_constantFullBlockMatrixSqrt_scalarMatrix hσ]
  exact doubledResponseJ_scalarNormalized_le (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
    hσ _ _ hnorm

/-- The first inequality of the printed `e.J.by.f` (ABK26) in quadratic-form
shape: on a unit vector, the `σ`-weighted sum of the two coarse quadratic forms
minus `2` is at most twice the normalized block-response maximum.

The proof evaluates the reflection identity of `ToLambdas.lean` at the
half-probe `(u, 0)`, whose reflection is itself. -/
theorem vecDot_bCoarse_add_vecDot_sigmaStarInvCoarse_sub_two_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ)
    (u : Vec d) (hu : vecNormSq u = 1) :
    σ⁻¹ * vecDot u
          (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u) +
        σ * vecDot u
          (matVecMul (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
            (F.coeffOn Q)) u) - 2 ≤
      2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) := by
  have hcpos : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ
  have hc : Real.sqrt σ ≠ 0 := ne_of_gt hcpos
  have hcc : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt hσ.le
  have hcinv : (Real.sqrt σ)⁻¹ * (Real.sqrt σ)⁻¹ = σ⁻¹ := by rw [← mul_inv, hcc]
  have hzero : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
  have hkey := doubledResponseJ_scaledNormalizers_add_reflect_eq
    (Book.Ch02.cubeDomain Q) (F.coeffOn Q) hc u 0
  rw [hcc, hcinv, hu, hzero, vecDot_zero_left, vecDot_zero_left] at hkey
  simp only [neg_zero] at hkey
  have hmem : Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
      ((Real.sqrt σ)⁻¹ • u, Real.sqrt σ • (0 : Vec d))
      (Real.sqrt σ • u, (Real.sqrt σ)⁻¹ • (0 : Vec d)) ∈
      Book.Ch02.normalizedBlockResponseValueSet Q F (scalarMatrix (d := d) σ) := by
    refine ⟨Sum.elim u 0, ?_, ?_⟩
    · rw [fullBlockVecNormSq_eq_add]
      show vecNormSq u + vecNormSq (0 : Vec d) = 1
      rw [hzero, add_zero]
      exact hu
    · rw [ofFullBlockVec_constantFullBlockMatrixInvSqrt_scalarMatrix hσ,
        ofFullBlockVec_constantFullBlockMatrixSqrt_scalarMatrix hσ]
      rfl
  have hle : Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
      ((Real.sqrt σ)⁻¹ • u, Real.sqrt σ • (0 : Vec d))
      (Real.sqrt σ • u, (Real.sqrt σ)⁻¹ • (0 : Vec d)) ≤
      Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) :=
    le_csSup (normalizedBlockResponseValueSet_scalarMatrix_bddAbove Q F hσ) hmem
  linarith

/-! ## The sharp one-cube upper bounds -/

/-- The two normalized quadratic forms at a unit vector are each at most
`1 + D + D^{1/2}`, where `D` is twice the normalized block-response maximum. -/
private theorem unit_quadraticForms_le {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) (u : Vec d)
    (hu : vecNormSq u = 1) :
    σ⁻¹ * vecDot u
        (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u) ≤
      1 + 2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) +
        Real.sqrt
          (2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ)) ∧
      σ * vecDot u
        (matVecMul (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
          (F.coeffOn Q)) u) ≤
      1 + 2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) +
        Real.sqrt
          (2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ)) := by
  have hune : u ≠ 0 := by
    intro h0
    rw [h0] at hu
    simp [vecNormSq, vecDot] at hu
  have hbpos : 0 < vecDot u
      (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      (Book.Ch02.bCoarse_posDef (Book.Ch02.cubeDomain Q)
        (F.coeffOn Q)).dotProduct_mulVec_pos hune
  have hspos : 0 < vecDot u
      (matVecMul (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
        (F.coeffOn Q)) u) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      (Book.Ch02.sigmaStarInvCoarse_posDef (Book.Ch02.cubeDomain Q)
        (F.coeffOn Q)).dotProduct_mulVec_pos hune
  have hPpos : 0 < σ⁻¹ * vecDot u
      (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u) :=
    mul_pos (inv_pos.2 hσ) hbpos
  have hRpos : 0 < σ * vecDot u
      (matVecMul (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
        (F.coeffOn Q)) u) := mul_pos hσ hspos
  have hprod : 1 ≤ (σ⁻¹ * vecDot u
        (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u)) *
      (σ * vecDot u
        (matVecMul (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
          (F.coeffOn Q)) u)) := by
    have hCS := sq_vecNormSq_le_vecDot_bCoarse_mul_vecDot_sigmaStarInvCoarse
      (Book.Ch02.cubeDomain Q) (F.coeffOn Q) u
    rw [hu] at hCS
    have hmul : (σ⁻¹ * vecDot u
          (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u)) *
        (σ * vecDot u
          (matVecMul (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
            (F.coeffOn Q)) u)) =
        vecDot u (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q)
            (F.coeffOn Q)) u) *
          vecDot u (matVecMul (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
            (F.coeffOn Q)) u) := by
      field_simp
    rw [hmul]
    simpa using hCS
  have hsum := vecDot_bCoarse_add_vecDot_sigmaStarInvCoarse_sub_two_le Q F hσ u hu
  have hD : 0 ≤ 2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) := by
    have := Book.Ch02.normalizedBlockResponseMax_nonneg Q F (scalarMatrix (d := d) σ)
    linarith
  constructor
  · have hf := (invMulSubOneSq_le_add_sub_two hPpos hprod).trans hsum
    have := sub_one_le_add_sqrt_of_invMulSubOneSq_le hPpos hD hf
    linarith
  · have hprod' : 1 ≤ (σ * vecDot u
          (matVecMul (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
            (F.coeffOn Q)) u)) *
        (σ⁻¹ * vecDot u
          (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u)) := by
      rw [mul_comm]
      exact hprod
    have hsum' : (σ * vecDot u
          (matVecMul (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
            (F.coeffOn Q)) u)) +
        (σ⁻¹ * vecDot u
          (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u)) -
          2 ≤
        2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) := by
      linarith
    have hf := (invMulSubOneSq_le_add_sub_two hRpos hprod').trans hsum'
    have := sub_one_le_add_sqrt_of_invMulSubOneSq_le hRpos hD hf
    linarith

/-- The sharp one-cube upper bound for `σ^{-1} |b(Q;a)|`. -/
theorem inv_mul_coarseBMatrixNorm_le_one_add_add_sqrt {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    σ⁻¹ * Book.Ch02.coarseBMatrixNorm Q F ≤
      1 + 2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) +
        Real.sqrt
          (2 * Book.Ch02.normalizedBlockResponseMax Q F
            (scalarMatrix (d := d) σ)) := by
  have hD : 0 ≤ 2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) := by
    have := Book.Ch02.normalizedBlockResponseMax_nonneg Q F (scalarMatrix (d := d) σ)
    linarith
  have hC : 0 ≤ 1 + 2 * Book.Ch02.normalizedBlockResponseMax Q F
      (scalarMatrix (d := d) σ) +
      Real.sqrt (2 * Book.Ch02.normalizedBlockResponseMax Q F
        (scalarMatrix (d := d) σ)) := by
    have := Real.sqrt_nonneg
      (2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ))
    linarith
  have hnorm : Book.Ch02.matrixNorm
      (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) ≤
      σ * (1 + 2 * Book.Ch02.normalizedBlockResponseMax Q F
          (scalarMatrix (d := d) σ) +
        Real.sqrt (2 * Book.Ch02.normalizedBlockResponseMax Q F
          (scalarMatrix (d := d) σ))) := by
    refine matrixNorm_le_of_forall_unit
      (Book.Ch02.bCoarse_posDef (Book.Ch02.cubeDomain Q) (F.coeffOn Q)).posSemidef
      (mul_nonneg hσ.le hC) ?_
    intro u hu
    have hunit := (unit_quadraticForms_le Q F hσ u hu).1
    have hmul := mul_le_mul_of_nonneg_left hunit hσ.le
    rw [← mul_assoc, mul_inv_cancel₀ hσ.ne', one_mul] at hmul
    exact hmul
  have hb : Book.Ch02.coarseBMatrixNorm Q F =
      Book.Ch02.matrixNorm (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) :=
    rfl
  rw [hb]
  calc
    σ⁻¹ * Book.Ch02.matrixNorm
        (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q))
        ≤ σ⁻¹ * (σ * (1 + 2 * Book.Ch02.normalizedBlockResponseMax Q F
              (scalarMatrix (d := d) σ) +
            Real.sqrt (2 * Book.Ch02.normalizedBlockResponseMax Q F
              (scalarMatrix (d := d) σ)))) :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.2 hσ.le)
    _ = 1 + 2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) +
          Real.sqrt (2 * Book.Ch02.normalizedBlockResponseMax Q F
            (scalarMatrix (d := d) σ)) := by
        field_simp

/-- The sharp one-cube upper bound for `σ |σ_*^{-1}(Q;a)|`. -/
theorem mul_coarseSigmaStarInvMatrixNorm_le_one_add_add_sqrt {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    σ * Book.Ch02.coarseSigmaStarInvMatrixNorm Q F ≤
      1 + 2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) +
        Real.sqrt
          (2 * Book.Ch02.normalizedBlockResponseMax Q F
            (scalarMatrix (d := d) σ)) := by
  have hD : 0 ≤ 2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) := by
    have := Book.Ch02.normalizedBlockResponseMax_nonneg Q F (scalarMatrix (d := d) σ)
    linarith
  have hC : 0 ≤ 1 + 2 * Book.Ch02.normalizedBlockResponseMax Q F
      (scalarMatrix (d := d) σ) +
      Real.sqrt (2 * Book.Ch02.normalizedBlockResponseMax Q F
        (scalarMatrix (d := d) σ)) := by
    have := Real.sqrt_nonneg
      (2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ))
    linarith
  have hnorm : Book.Ch02.matrixNorm
      (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) ≤
      σ⁻¹ * (1 + 2 * Book.Ch02.normalizedBlockResponseMax Q F
          (scalarMatrix (d := d) σ) +
        Real.sqrt (2 * Book.Ch02.normalizedBlockResponseMax Q F
          (scalarMatrix (d := d) σ))) := by
    refine matrixNorm_le_of_forall_unit
      (Book.Ch02.sigmaStarInvCoarse_posDef (Book.Ch02.cubeDomain Q)
        (F.coeffOn Q)).posSemidef (mul_nonneg (inv_nonneg.2 hσ.le) hC) ?_
    intro u hu
    have hunit := (unit_quadraticForms_le Q F hσ u hu).2
    have hmul := mul_le_mul_of_nonneg_left hunit (inv_nonneg.2 hσ.le)
    rw [← mul_assoc, inv_mul_cancel₀ hσ.ne', one_mul] at hmul
    exact hmul
  have hs : Book.Ch02.coarseSigmaStarInvMatrixNorm Q F =
      Book.Ch02.matrixNorm
        (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) :=
    rfl
  rw [hs]
  calc
    σ * Book.Ch02.matrixNorm
        (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q))
        ≤ σ * (σ⁻¹ * (1 + 2 * Book.Ch02.normalizedBlockResponseMax Q F
              (scalarMatrix (d := d) σ) +
            Real.sqrt (2 * Book.Ch02.normalizedBlockResponseMax Q F
              (scalarMatrix (d := d) σ)))) :=
        mul_le_mul_of_nonneg_left hnorm hσ.le
    _ = 1 + 2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) +
          Real.sqrt (2 * Book.Ch02.normalizedBlockResponseMax Q F
            (scalarMatrix (d := d) σ)) := by
        field_simp

/-! ## Descendant-scale square-root bounds -/

/-- The upper one-cube estimate, maximized over a descendant scale and put in
the square-root form needed by the paper's `q = 1` aggregation. -/
theorem sqrt_inv_mul_maxDescendantBMatrixNormAtScale_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (F : Book.Ch02.TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    Real.sqrt (σ⁻¹ * Book.Ch02.maxDescendantBMatrixNormAtScale Q k F) ≤
      1 + Real.sqrt (2 * Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        Q k F (scalarMatrix (d := d) σ)) := by
  let D := Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
    Q k F (scalarMatrix (d := d) σ)
  let C := 1 + 2 * D + Real.sqrt (2 * D)
  have hD : 0 ≤ D :=
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk F _
  have hne := descendantsAtScale_nonempty Q hk
  have hpoint : ∀ R ∈ descendantsAtScale Q k,
      Book.Ch02.coarseBMatrixNorm R F ≤ σ * C := by
    intro R hR
    have hRone := inv_mul_coarseBMatrixNorm_le_one_add_add_sqrt R F hσ
    have hMle :=
      Book.Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        F (scalarMatrix (d := d) σ) hR
    have hroot : Real.sqrt (2 * Book.Ch02.normalizedBlockResponseMax R F
        (scalarMatrix (d := d) σ)) ≤ Real.sqrt (2 * D) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left hMle (by norm_num)
    have hRle : σ⁻¹ * Book.Ch02.coarseBMatrixNorm R F ≤ C := by
      dsimp [C, D]
      linarith
    exact (inv_mul_le_iff₀ hσ).mp hRle
  have hmax : Book.Ch02.maxDescendantBMatrixNormAtScale Q k F ≤ σ * C := by
    simpa [Book.Ch02.maxDescendantBMatrixNormAtScale] using
      Book.Ch02.finsetSupReal_le (descendantsAtScale Q k) hne hpoint
  have hbase : σ⁻¹ * Book.Ch02.maxDescendantBMatrixNormAtScale Q k F ≤ C := by
    calc
      σ⁻¹ * Book.Ch02.maxDescendantBMatrixNormAtScale Q k F ≤ σ⁻¹ * (σ * C) :=
        mul_le_mul_of_nonneg_left hmax (inv_nonneg.2 hσ.le)
      _ = C := by field_simp
  have hx : 0 ≤ σ⁻¹ * Book.Ch02.maxDescendantBMatrixNormAtScale Q k F :=
    mul_nonneg (inv_nonneg.2 hσ.le)
      (Book.Ch02.maxDescendantBMatrixNormAtScale_nonneg Q hk F)
  have hsqrtSq := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD)
  have hxSq := Real.sq_sqrt hx
  have hsqrt0 := Real.sqrt_nonneg (2 * D)
  have hx0 := Real.sqrt_nonneg
    (σ⁻¹ * Book.Ch02.maxDescendantBMatrixNormAtScale Q k F)
  dsimp [C] at hbase
  dsimp [D] at hD hsqrtSq hsqrt0 ⊢
  nlinarith

/-- The lower-inverse twin of
`sqrt_inv_mul_maxDescendantBMatrixNormAtScale_le`. -/
theorem sqrt_mul_maxDescendantSigmaStarInvMatrixNormAtScale_le {d : ℕ}
    [NeZero d] (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (F : Book.Ch02.TriadicCoeffFamily d) {σ : ℝ} (hσ : 0 < σ) :
    Real.sqrt (σ * Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F) ≤
      1 + Real.sqrt (2 * Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        Q k F (scalarMatrix (d := d) σ)) := by
  let D := Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
    Q k F (scalarMatrix (d := d) σ)
  let C := 1 + 2 * D + Real.sqrt (2 * D)
  have hD : 0 ≤ D :=
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk F _
  have hne := descendantsAtScale_nonempty Q hk
  have hpoint : ∀ R ∈ descendantsAtScale Q k,
      Book.Ch02.coarseSigmaStarInvMatrixNorm R F ≤ σ⁻¹ * C := by
    intro R hR
    have hRone := mul_coarseSigmaStarInvMatrixNorm_le_one_add_add_sqrt R F hσ
    have hMle :=
      Book.Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        F (scalarMatrix (d := d) σ) hR
    have hroot : Real.sqrt (2 * Book.Ch02.normalizedBlockResponseMax R F
        (scalarMatrix (d := d) σ)) ≤ Real.sqrt (2 * D) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left hMle (by norm_num)
    have hRle : σ * Book.Ch02.coarseSigmaStarInvMatrixNorm R F ≤ C := by
      dsimp [C, D]
      linarith
    exact (le_inv_mul_iff₀ hσ).mpr hRle
  have hmax : Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F ≤
      σ⁻¹ * C := by
    simpa [Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale] using
      Book.Ch02.finsetSupReal_le (descendantsAtScale Q k) hne hpoint
  have hbase : σ * Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F ≤ C := by
    calc
      σ * Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F ≤
          σ * (σ⁻¹ * C) := mul_le_mul_of_nonneg_left hmax hσ.le
      _ = C := by field_simp
  have hx : 0 ≤ σ * Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F :=
    mul_nonneg hσ.le
      (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hk F)
  have hsqrtSq := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD)
  have hxSq := Real.sq_sqrt hx
  have hsqrt0 := Real.sqrt_nonneg (2 * D)
  have hx0 := Real.sqrt_nonneg
    (σ * Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F)
  dsimp [C] at hbase
  dsimp [D] at hD hsqrtSq hsqrt0 ⊢
  nlinarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison
