module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumannDefinitions
public import Homogenization.Book.Ch02.Theorems.MatrixPositivity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

@[expose] public section

/-!
# Sharp comparison of the response with normalized coarse matrices

This is the deterministic comparison in `l.sharp.compare.J`.  The reference
matrix is genuinely matrix-valued and positive definite.

The proof-route decomposition follows
`Algsuperdiff/Section3/Provider/Homogenization/RelativeComparatorProbe.lean`:
first rewrite the response by completed squares, then compare the positive
summands, and finally convert the resulting quadratic bounds to matrix norms.
Unlike that scalar-isotropic doubled-block analogue, the argument below keeps
an arbitrary SPD reference matrix throughout.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization Homogenization.Book
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-- Symmetric positive square root of a real matrix. -/
noncomputable def matrixSqrt {d : ℕ} (A : Mat d) : Mat d :=
  CFC.sqrt A

/-- First positive summand in the normalized completed-square formula. -/
noncomputable def sharpPrimalGapMatrix {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (b : Mat d) : Mat d :=
  (1 / 2 : ℝ) •
    (matrixInvSqrt b * (aMatrix U a - aStarMatrix U a) * matrixInvSqrt b)

/-- Second positive summand in the normalized completed-square formula. -/
noncomputable def sharpPrimalMismatchMatrix {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (b : Mat d) : Mat d :=
  let D := (1 : Mat d) - matrixInvSqrt b * aStarMatrix U a * matrixInvSqrt b
  (1 / 2 : ℝ) •
    (D * (matrixSqrt b * (aStarMatrix U a)⁻¹ * matrixSqrt b) * D)

/-- Square-root mismatch in the first displayed comparison of
`l.sharp.compare.J`. -/
noncomputable def sharpPrimalMismatchRoot {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (b : Mat d) : Mat d :=
  matrixInvSqrt b * matrixSqrt (aStarMatrix U a) -
    matrixSqrt b * matrixInvSqrt (aStarMatrix U a)

/-- First positive summand in the inverse completed-square formula. -/
noncomputable def sharpDualGapMatrix {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (b : Mat d) : Mat d :=
  (1 / 2 : ℝ) •
    (matrixSqrt b * ((aStarMatrix U a)⁻¹ - (aMatrix U a)⁻¹) * matrixSqrt b)

/-- Second positive summand in the inverse completed-square formula. -/
noncomputable def sharpDualMismatchMatrix {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (b : Mat d) : Mat d :=
  let D := (1 : Mat d) - matrixSqrt b * (aMatrix U a)⁻¹ * matrixSqrt b
  (1 / 2 : ℝ) •
    (D * (matrixInvSqrt b * aMatrix U a * matrixInvSqrt b) * D)

/-- Square-root mismatch in the second displayed comparison of
`l.sharp.compare.J`. -/
noncomputable def sharpDualMismatchRoot {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (b : Mat d) : Mat d :=
  matrixSqrt b * matrixInvSqrt (aMatrix U a) -
    matrixInvSqrt b * matrixSqrt (aMatrix U a)

/-- Sum of the two positive matrices in the inverse completed-square formula. -/
noncomputable def sharpDualResponseMatrix {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (b : Mat d) : Mat d :=
  sharpDualGapMatrix U a b + sharpDualMismatchMatrix U a b

/-- Matrix whose unit quadratic forms are the paper's normalized response probes. -/
noncomputable def sharpResponseMatrix {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (b : Mat d) : Mat d :=
  sharpPrimalGapMatrix U a b + sharpPrimalMismatchMatrix U a b

/-- The response maximum in matrix form.  `sharpResponse_quadratic` identifies
its unit quadratic forms with `J(U,b⁻¹ᐟ²e,b¹ᐟ²e;a)`. -/
noncomputable def sharpResponseMax {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (b : Mat d) : ℝ :=
  Ch02.matrixOperatorNorm (sharpResponseMatrix U a b)

/-- Unit-sphere values of the normalized response probe. -/
noncomputable def sharpResponseValueSet {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (b : Mat d) : Set ℝ :=
  {y | ∃ e : Vec d, vecNormSq e = 1 ∧
    y = J U a (matVecMul (matrixInvSqrt b) e) (matVecMul (matrixSqrt b) e)}

/-- The paper's `max_{|e|=1}` read as the supremum of its unit-sphere
response values.  Attainment is not needed by any consumer. -/
noncomputable def sharpResponseSup {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (b : Mat d) : ℝ :=
  sSup (sharpResponseValueSet U a b)

private theorem matrixOperatorNorm_add_comparison_of_posSemidef {d : ℕ}
    {M N : Mat d} (hM : M.PosSemidef) (hN : N.PosSemidef) :
    Ch02.matrixOperatorNorm (M + N) ≤
        Ch02.matrixOperatorNorm M + Ch02.matrixOperatorNorm N ∧
      Ch02.matrixOperatorNorm M + Ch02.matrixOperatorNorm N ≤
        2 * Ch02.matrixOperatorNorm (M + N) := by
  rw [Ch02.matrixOperatorNorm_eq_l2_opNorm,
    Ch02.matrixOperatorNorm_eq_l2_opNorm,
    Ch02.matrixOperatorNorm_eq_l2_opNorm]
  constructor
  · exact norm_add_le M N
  · have hMle : ‖M‖ ≤ ‖M + N‖ := by
      exact Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef
        hM (hM.add hN) (by
          intro x
          have := hN.dotProduct_mulVec_nonneg x
          rw [add_matVecMul, vecDot_add_right]
          have hq : 0 ≤ vecDot x (matVecMul N x) := by
            simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using this
          linarith)
    have hNle : ‖N‖ ≤ ‖M + N‖ := by
      exact Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef
        hN (hM.add hN) (by
          intro x
          have := hM.dotProduct_mulVec_nonneg x
          rw [add_matVecMul, vecDot_add_right]
          have hq : 0 ≤ vecDot x (matVecMul M x) := by
            simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using this
          linarith)
    linarith

private theorem matrixOperatorNorm_right_le_add_of_posSemidef {d : ℕ}
    {M N : Mat d} (hM : M.PosSemidef) (hN : N.PosSemidef) :
    Ch02.matrixOperatorNorm N ≤ Ch02.matrixOperatorNorm (M + N) := by
  apply Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef hN (hM.add hN)
  intro x
  have hq : 0 ≤ vecDot x (matVecMul M x) := by
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
      hM.dotProduct_mulVec_nonneg x
  rw [add_matVecMul, vecDot_add_right]
  linarith

private theorem matrixOperatorNorm_left_le_add_of_posSemidef {d : ℕ}
    {M N : Mat d} (hM : M.PosSemidef) (hN : N.PosSemidef) :
    Ch02.matrixOperatorNorm M ≤ Ch02.matrixOperatorNorm (M + N) := by
  simpa [add_comm] using matrixOperatorNorm_right_le_add_of_posSemidef hN hM

private theorem matrixSqrt_posSemidef {d : ℕ} (A : Mat d) :
    (matrixSqrt A).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact CFC.sqrt_nonneg A

private theorem matrixSqrt_isSymm {d : ℕ} (A : Mat d) :
    (matrixSqrt A).IsSymm := by
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using
    (matrixSqrt_posSemidef A).isHermitian

private theorem matrixInvSqrt_isSymm {d : ℕ} (A : Mat d) :
    (matrixInvSqrt A).IsSymm := by
  exact isSymm_nonsingInv (matrixSqrt_isSymm A)

private theorem matrixSqrt_mul_self {d : ℕ} {A : Mat d}
    (hA : A.PosSemidef) : matrixSqrt A * matrixSqrt A = A := by
  simpa [matrixSqrt, pow_two] using
    CFC.sq_sqrt A (by
      rw [Matrix.nonneg_iff_posSemidef]
      exact hA)

private theorem matrixSqrt_isUnit {d : ℕ} {A : Mat d}
    (hA : A.PosDef) : IsUnit (matrixSqrt A) := by
  exact (CFC.isUnit_sqrt_iff A (by
    rw [Matrix.nonneg_iff_posSemidef]
    exact hA.posSemidef)).2 hA.isUnit

private theorem matrixInvSqrt_mul_matrixSqrt {d : ℕ} {A : Mat d}
    (hA : A.PosDef) : matrixInvSqrt A * matrixSqrt A = 1 := by
  exact Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (matrixSqrt_isUnit hA))

private theorem matrixSqrt_mul_matrixInvSqrt {d : ℕ} {A : Mat d}
    (hA : A.PosDef) : matrixSqrt A * matrixInvSqrt A = 1 := by
  exact Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (matrixSqrt_isUnit hA))

private theorem matrixInvSqrt_mul_self {d : ℕ} {A : Mat d}
    (hA : A.PosDef) : matrixInvSqrt A * matrixInvSqrt A = A⁻¹ := by
  have hTQ := matrixSqrt_mul_matrixInvSqrt hA
  have hQT := matrixInvSqrt_mul_matrixSqrt hA
  have hTT := matrixSqrt_mul_self hA.posSemidef
  apply hA.isUnit.mul_left_cancel
  rw [Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)]
  nth_rewrite 1 [← hTT]
  calc
    matrixSqrt A * matrixSqrt A *
        (matrixInvSqrt A * matrixInvSqrt A) =
      matrixSqrt A *
        ((matrixSqrt A * matrixInvSqrt A) * matrixInvSqrt A) := by
          simp [Matrix.mul_assoc]
    _ = 1 := by rw [hTQ, one_mul, hTQ]

private theorem matrix_nonsing_inv_anti {d : ℕ} {A B : Mat d}
    (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  letI : Invertible A := hA.isUnit.invertible
  letI : Invertible B := hB.isUnit.invertible
  have hgap : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hblock :
      (Matrix.fromBlocks B (1 : Mat d)
        (Matrix.conjTranspose (1 : Mat d)) A⁻¹).PosSemidef := by
    rw [Matrix.PosDef.fromBlocks₂₂ (A := B) (B := (1 : Mat d)) hA.inv]
    simpa using hgap
  have hinvgap :=
    (Matrix.PosDef.fromBlocks₁₁ (B := (1 : Mat d)) (D := A⁻¹) hB).mp hblock
  rw [Matrix.le_iff]
  simpa using hinvgap

private theorem aMatrix_posDef {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (ha : a.IsSymmetric) :
    (aMatrix U a).PosDef := by
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U a ha
  have hsigma : (Ch02.sigmaCoarse U a).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · simpa [Matrix.IsHermitian, Matrix.IsSymm] using
        Ch02.sigmaCoarse_isSymm U a
    · intro p hp
      have hstar := (Ch02.sigmaStarCoarse_posDef U a).dotProduct_mulVec_pos hp
      have hle := hTheory.dirichlet_neumann_bracketing.2.1 p
      have hstar' : 0 < (1 / 2 : ℝ) *
          vecDot p (matVecMul (Ch02.sigmaStarCoarse U a) p) := by
        have : 0 < vecDot p
            (matVecMul (Ch02.sigmaStarCoarse U a) p) := by
          simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hstar
        nlinarith
      have := hstar'.trans_le hle
      simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using (show
        0 < vecDot p (matVecMul (Ch02.sigmaCoarse U a) p) by
          nlinarith)
  change (Ch02.aCoarse U a).PosDef
  rw [hTheory.derived_matrices.1]
  exact hsigma

private theorem aStarMatrix_posDef {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (ha : a.IsSymmetric) :
    (aStarMatrix U a).PosDef := by
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U a ha
  change (Ch02.aStarCoarse U a).PosDef
  rw [hTheory.derived_matrices.2.1]
  exact Ch02.sigmaStarCoarse_posDef U a

private theorem vecDot_congruence {d : ℕ} (L A : Mat d)
    (hL : L.IsSymm) (x : Vec d) :
    vecDot x (matVecMul (L * A * L) x) =
      vecDot (matVecMul L x) (matVecMul A (matVecMul L x)) := by
  rw [← matVecMul_mul, ← matVecMul_mul]
  rw [vecDot_matVecMul_comm_of_isSymm hL]
  exact vecDot_comm _ _

private theorem vecDot_congruence_transpose {d : ℕ} (L A : Mat d)
    (x : Vec d) :
    vecDot x (matVecMul (Matrix.transpose L * A * L) x) =
      vecDot (matVecMul L x) (matVecMul A (matVecMul L x)) := by
  rw [← matVecMul_mul, ← matVecMul_mul]
  change dotProduct x
    (Matrix.mulVec (Matrix.transpose L) (Matrix.mulVec A (Matrix.mulVec L x))) = _
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_transpose]
  rfl

private theorem aStarMatrix_inv_eq_sigmaStarInvCoarse {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric) :
    (aStarMatrix U a)⁻¹ = Ch02.sigmaStarInvCoarse U a := by
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U a ha
  rw [show aStarMatrix U a = Ch02.sigmaStarCoarse U a from
    hTheory.derived_matrices.2.1]
  unfold Ch02.sigmaStarCoarse
  exact Matrix.nonsing_inv_nonsing_inv _
    (Ch02.isUnit_det_sigmaStarInvCoarse U a)

private theorem sharpPrimalGapMatrix_posSemidef {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) : (sharpPrimalGapMatrix U a b).PosSemidef := by
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U a ha
  have hgapSymm : (aMatrix U a - aStarMatrix U a).IsSymm := by
    change (Ch02.aCoarse U a - Ch02.aStarCoarse U a).IsSymm
    rw [hTheory.derived_matrices.1, hTheory.derived_matrices.2.1]
    exact (Ch02.sigmaCoarse_isSymm U a).sub (Ch02.sigmaStarCoarse_isSymm U a)
  have hgap : (aMatrix U a - aStarMatrix U a).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (by simpa [Matrix.IsHermitian, Matrix.IsSymm] using hgapSymm) ?_
    intro x
    have hx := hTheory.dirichlet_neumann_bracketing.2.1 x
    change 0 ≤ vecDot x (matVecMul (aMatrix U a - aStarMatrix U a) x)
    change 0 ≤ vecDot x
      (matVecMul (Ch02.aCoarse U a - Ch02.aStarCoarse U a) x)
    rw [hTheory.derived_matrices.1, hTheory.derived_matrices.2.1]
    rw [sub_matVecMul]
    rw [show vecDot x
          (matVecMul (Ch02.sigmaCoarse U a) x -
            matVecMul (Ch02.sigmaStarCoarse U a) x) =
        vecDot x (matVecMul (Ch02.sigmaCoarse U a) x) -
          vecDot x (matVecMul (Ch02.sigmaStarCoarse U a) x) by
      simp [vecDot, mul_sub, Finset.sum_sub_distrib]]
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using (show
      0 ≤ vecDot x (matVecMul (Ch02.sigmaCoarse U a) x) -
        vecDot x (matVecMul (Ch02.sigmaStarCoarse U a) x) by
          linarith)
  unfold sharpPrimalGapMatrix
  have hcong := hgap.conjTranspose_mul_mul_same (matrixInvSqrt b)
  have hSsymm := matrixInvSqrt_isSymm b
  have hcong' :
      (matrixInvSqrt b * (aMatrix U a - aStarMatrix U a) *
        matrixInvSqrt b).PosSemidef := by
    have hSstar : Matrix.conjTranspose (matrixInvSqrt b) = matrixInvSqrt b := by
      exact Matrix.isHermitian_iff_isSymm.mpr hSsymm
    rw [hSstar] at hcong
    exact hcong
  exact hcong'.smul (by norm_num)

private theorem inverse_coarse_gap_posSemidef {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric) :
    ((aStarMatrix U a)⁻¹ - (aMatrix U a)⁻¹).PosSemidef := by
  have hA : (aMatrix U a).PosDef := aMatrix_posDef U a ha
  have hAst : (aStarMatrix U a).PosDef := aStarMatrix_posDef U a ha
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U a ha
  have hgap : (aMatrix U a - aStarMatrix U a).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · have hAsymm : (aMatrix U a).IsSymm := by
        simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA.posSemidef.isHermitian
      have hAstsymm : (aStarMatrix U a).IsSymm := by
        simpa [Matrix.IsHermitian, Matrix.IsSymm] using hAst.posSemidef.isHermitian
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hAsymm.sub hAstsymm
    · intro x
      have hx := hTheory.dirichlet_neumann_bracketing.2.1 x
      rw [← hTheory.derived_matrices.1,
        ← hTheory.derived_matrices.2.1] at hx
      change 0 ≤ vecDot x
        (matVecMul (aMatrix U a - aStarMatrix U a) x)
      rw [sub_matVecMul]
      rw [show vecDot x
          (matVecMul (aMatrix U a) x - matVecMul (aStarMatrix U a) x) =
        vecDot x (matVecMul (aMatrix U a) x) -
          vecDot x (matVecMul (aStarMatrix U a) x) by
            simp [vecDot, mul_sub, Finset.sum_sub_distrib]]
      linarith
  have hle : aStarMatrix U a ≤ aMatrix U a := by
    rw [Matrix.le_iff]
    exact hgap
  have hinv' : (aMatrix U a)⁻¹ ≤ (aStarMatrix U a)⁻¹ :=
    matrix_nonsing_inv_anti hAst hA hle
  rw [← Matrix.nonneg_iff_posSemidef]
  exact sub_nonneg.mpr hinv'

private theorem sharpDualGapMatrix_posSemidef {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) : (sharpDualGapMatrix U a b).PosSemidef := by
  have hgap := inverse_coarse_gap_posSemidef U a ha
  have hc := hgap.conjTranspose_mul_mul_same (matrixSqrt b)
  have hRstar : Matrix.conjTranspose (matrixSqrt b) = matrixSqrt b := by
    exact Matrix.isHermitian_iff_isSymm.mpr (matrixSqrt_isSymm b)
  rw [hRstar] at hc
  exact hc.smul (by norm_num)

private theorem sharpDualMismatchMatrix_posSemidef {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) : (sharpDualMismatchMatrix U a b).PosSemidef := by
  let D := (1 : Mat d) - matrixSqrt b * (aMatrix U a)⁻¹ * matrixSqrt b
  let C := matrixInvSqrt b * aMatrix U a * matrixInvSqrt b
  have hA : (aMatrix U a).PosDef := aMatrix_posDef U a ha
  have hC : C.PosSemidef := by
    have hc := hA.posSemidef.conjTranspose_mul_mul_same (matrixInvSqrt b)
    have hSstar : Matrix.conjTranspose (matrixInvSqrt b) = matrixInvSqrt b := by
      exact Matrix.isHermitian_iff_isSymm.mpr (matrixInvSqrt_isSymm b)
    rw [hSstar] at hc
    exact hc
  have hDsymm : D.IsSymm := by
    have hR := matrixSqrt_isSymm b
    have hAinv : ((aMatrix U a)⁻¹).IsSymm := by
      exact isSymm_nonsingInv (by
        simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA.posSemidef.isHermitian)
    dsimp [D]
    rw [Matrix.IsSymm]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      hR, hAinv]
    simp [Matrix.mul_assoc]
  have hc := hC.conjTranspose_mul_mul_same D
  have hDstar : Matrix.conjTranspose D = D := by
    exact Matrix.isHermitian_iff_isSymm.mpr hDsymm
  rw [hDstar] at hc
  exact hc.smul (by norm_num)

private theorem sharpDualResponseMatrix_eq_sharpResponseMatrix {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    sharpDualResponseMatrix U a b = sharpResponseMatrix U a b := by
  let R := matrixSqrt b
  let S := matrixInvSqrt b
  let A := aMatrix U a
  let Astar := aStarMatrix U a
  let P := S * Astar * S
  let C := R * Astar⁻¹ * R
  let Q := R * A⁻¹ * R
  let E := S * A * S
  have hA : A.PosDef := aMatrix_posDef U a ha
  have hAstar : Astar.PosDef := aStarMatrix_posDef U a ha
  have hRS : R * S = 1 := matrixSqrt_mul_matrixInvSqrt hb
  have hSR : S * R = 1 := matrixInvSqrt_mul_matrixSqrt hb
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hAinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hSSinv : Astar * Astar⁻¹ = 1 := Matrix.mul_nonsing_inv Astar
    ((Matrix.isUnit_iff_isUnit_det Astar).mp hAstar.isUnit)
  have hSinvS : Astar⁻¹ * Astar = 1 := Matrix.nonsing_inv_mul Astar
    ((Matrix.isUnit_iff_isUnit_det Astar).mp hAstar.isUnit)
  have hSR' (Z : Mat d) : S * (R * Z) = Z := by
    rw [← Matrix.mul_assoc, hSR, one_mul]
  have hRS' (Z : Mat d) : R * (S * Z) = Z := by
    rw [← Matrix.mul_assoc, hRS, one_mul]
  have hAAinv' (Z : Mat d) : A * (A⁻¹ * Z) = Z := by
    rw [← Matrix.mul_assoc, hAAinv, one_mul]
  have hAinvA' (Z : Mat d) : A⁻¹ * (A * Z) = Z := by
    rw [← Matrix.mul_assoc, hAinvA, one_mul]
  have hSSinv' (Z : Mat d) : Astar * (Astar⁻¹ * Z) = Z := by
    rw [← Matrix.mul_assoc, hSSinv, one_mul]
  have hSinvS' (Z : Mat d) : Astar⁻¹ * (Astar * Z) = Z := by
    rw [← Matrix.mul_assoc, hSinvS, one_mul]
  have hPC : P * C = 1 := by
    dsimp [P, C]
    simp only [Matrix.mul_assoc]
    rw [hSR', hSSinv', hSR]
  have hCP : C * P = 1 := by
    dsimp [P, C]
    simp only [Matrix.mul_assoc]
    rw [hRS', hSinvS', hRS]
  have hQE : Q * E = 1 := by
    dsimp [Q, E]
    simp only [Matrix.mul_assoc]
    rw [hRS', hAinvA', hRS]
  have hEQ : E * Q = 1 := by
    dsimp [Q, E]
    simp only [Matrix.mul_assoc]
    rw [hSR', hAAinv', hSR]
  have hprimal :
      S * (A - Astar) * S + (1 - P) * C * (1 - P) =
        E + C - 1 - 1 := by
    have hgap : S * (A - Astar) * S = E - P := by
      dsimp [E, P]
      noncomm_ring
    rw [hgap]
    noncomm_ring [hPC, hCP]
  have hdual :
      R * (Astar⁻¹ - A⁻¹) * R + (1 - Q) * E * (1 - Q) =
        E + C - 1 - 1 := by
    have hgap : R * (Astar⁻¹ - A⁻¹) * R = C - Q := by
      dsimp [C, Q]
      noncomm_ring
    rw [hgap]
    noncomm_ring [hQE, hEQ]
  change
    (1 / 2 : ℝ) • (R * (Astar⁻¹ - A⁻¹) * R) +
        (1 / 2 : ℝ) • ((1 - Q) * E * (1 - Q)) =
      (1 / 2 : ℝ) • (S * (A - Astar) * S) +
        (1 / 2 : ℝ) • ((1 - P) * C * (1 - P))
  rw [← smul_add, ← smul_add, hdual, hprimal]

private theorem sharpDualMismatchMatrix_eq_root_mul_transpose {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    sharpDualMismatchMatrix U a b =
      (1 / 2 : ℝ) •
        (sharpDualMismatchRoot U a b *
          Matrix.transpose (sharpDualMismatchRoot U a b)) := by
  let R := matrixSqrt b
  let S := matrixInvSqrt b
  let A := aMatrix U a
  let T := matrixSqrt A
  let Q := matrixInvSqrt A
  let D := (1 : Mat d) - R * A⁻¹ * R
  let C := S * A * S
  let X := R * Q - S * T
  have hA : A.PosDef := aMatrix_posDef U a ha
  have hRS : R * S = 1 := matrixSqrt_mul_matrixInvSqrt hb
  have hSR : S * R = 1 := matrixInvSqrt_mul_matrixSqrt hb
  have hTQ : T * Q = 1 := matrixSqrt_mul_matrixInvSqrt hA
  have hQT : Q * T = 1 := matrixInvSqrt_mul_matrixSqrt hA
  have hTT : T * T = A := matrixSqrt_mul_self hA.posSemidef
  have hQQ : Q * Q = A⁻¹ := matrixInvSqrt_mul_self hA
  have hXt : Matrix.transpose X = Q * R - T * S := by
    have hR := matrixSqrt_isSymm b
    have hS := matrixInvSqrt_isSymm b
    have hT := matrixSqrt_isSymm A
    have hQ := matrixInvSqrt_isSymm A
    dsimp [X]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      hR, hQ, hS, hT]
  let P := R * A⁻¹ * R
  have hSR' (Z : Mat d) : S * (R * Z) = Z := by
    rw [← Matrix.mul_assoc, hSR, one_mul]
  have hRS' (Z : Mat d) : R * (S * Z) = Z := by
    rw [← Matrix.mul_assoc, hRS, one_mul]
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hAinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hAAinv' (Z : Mat d) : A * (A⁻¹ * Z) = Z := by
    rw [← Matrix.mul_assoc, hAAinv, one_mul]
  have hAinvA' (Z : Mat d) : A⁻¹ * (A * Z) = Z := by
    rw [← Matrix.mul_assoc, hAinvA, one_mul]
  have hPC : P * C = 1 := by
    dsimp [P, C]
    simp only [Matrix.mul_assoc]
    rw [hRS', hAinvA', hRS]
  have hCP : C * P = 1 := by
    dsimp [P, C]
    simp only [Matrix.mul_assoc]
    rw [hSR', hAAinv', hSR]
  have hTQ' (Z : Mat d) : T * (Q * Z) = Z := by
    rw [← Matrix.mul_assoc, hTQ, one_mul]
  have hQT' (Z : Mat d) : Q * (T * Z) = Z := by
    rw [← Matrix.mul_assoc, hQT, one_mul]
  have hTT' (Z : Mat d) : T * (T * Z) = A * Z := by
    rw [← Matrix.mul_assoc, hTT]
  have hQQ' (Z : Mat d) : Q * (Q * Z) = A⁻¹ * Z := by
    rw [← Matrix.mul_assoc, hQQ]
  change (1 / 2 : ℝ) • (D * C * D) =
    (1 / 2 : ℝ) • (X * Matrix.transpose X)
  congr 1
  rw [hXt]
  have hleft : D * C * D = C - 1 - 1 + P := by
    have hDP : D = 1 - P := by rfl
    rw [hDP]
    calc
      (1 - P) * C * (1 - P) = C - C * P - P * C + P * C * P := by
        noncomm_ring
      _ = C - 1 - 1 + P := by rw [hCP, hPC, one_mul]
  have hright : X * (Q * R - T * S) = P - 1 - 1 + C := by
    dsimp [X]
    calc
      (R * Q - S * T) * (Q * R - T * S) =
          R * (Q * (Q * R)) - S * (T * (Q * R)) -
            R * (Q * (T * S)) + S * (T * (T * S)) := by
        noncomm_ring
      _ = P - 1 - 1 + C := by
        rw [hQQ', hTQ', hQT', hTT']
        dsimp [P, C]
        rw [hSR, hRS]
        simp only [Matrix.mul_assoc]
  rw [hleft, hright]
  abel

private theorem sharpDualMismatchMatrix_norm {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    Ch02.matrixOperatorNorm (sharpDualMismatchMatrix U a b) =
      (1 / 2 : ℝ) *
        Ch02.matrixOperatorNorm (sharpDualMismatchRoot U a b) ^ 2 := by
  rw [sharpDualMismatchMatrix_eq_root_mul_transpose U a ha b hb]
  simp only [Ch02.matrixOperatorNorm_eq_l2_opNorm, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  let X := sharpDualMismatchRoot U a b
  have hstar : Matrix.conjTranspose X = Matrix.transpose X := by
    ext i j
    simp [Matrix.conjTranspose]
  have hcstar := Matrix.l2_opNorm_conjTranspose_mul_self (Matrix.conjTranspose X)
  rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at hcstar
  rw [← hstar, hcstar]
  ring

private theorem sharpDualMismatchMatrix_norm_raw {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (b : Mat d) :
    Ch02.matrixOperatorNorm (sharpDualMismatchMatrix U a b) =
      (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
        (((1 : Mat d) - matrixSqrt b * (aMatrix U a)⁻¹ * matrixSqrt b) *
          (matrixInvSqrt b * aMatrix U a * matrixInvSqrt b) *
          ((1 : Mat d) - matrixSqrt b * (aMatrix U a)⁻¹ * matrixSqrt b)) := by
  unfold sharpDualMismatchMatrix
  simp only [Ch02.matrixOperatorNorm_eq_l2_opNorm, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

private theorem sharpDualGapMatrix_norm {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (b : Mat d) :
    Ch02.matrixOperatorNorm (sharpDualGapMatrix U a b) =
      (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
        (matrixSqrt b * ((aStarMatrix U a)⁻¹ - (aMatrix U a)⁻¹) * matrixSqrt b) := by
  unfold sharpDualGapMatrix
  simp only [Ch02.matrixOperatorNorm_eq_l2_opNorm, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

private theorem matrix_deviation_sq_le_of_inverse_mismatch {d : ℕ} [NeZero d]
    {C P : Mat d} (hC : C.PosDef)
    (hCP : C * P = 1) (hPC : P * C = 1) {H : ℝ} (hH : 0 ≤ H)
    (hMismatch :
      (1 / 2 : ℝ) * Ch02.matrixOperatorNorm ((1 - P) * C * (1 - P)) ≤ H) :
    Ch02.matrixOperatorNorm (C - 1) ^ 2 ≤ 4 * H * (1 + H) := by
  let Y := C - (1 : Mat d)
  let K := (1 - P) * C * (1 - P)
  let K' := (1 - C) * P * (1 - C)
  have hK : K = K' := by
    dsimp [K, K']
    noncomm_ring [hCP, hPC]
  have hYY : Y * Y = K' * C := by
    dsimp [Y, K']
    noncomm_ring [hCP, hPC]
  have hYsymm : Y.IsSymm := by
    have hCsymm : C.IsSymm := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hC.posSemidef.isHermitian
    exact hCsymm.sub Matrix.isSymm_one
  have hYstar : Matrix.conjTranspose Y = Y := by
    exact Matrix.isHermitian_iff_isSymm.mpr hYsymm
  have hYsqNorm : Ch02.matrixOperatorNorm (Y * Y) =
      Ch02.matrixOperatorNorm Y ^ 2 := by
    have hcstar := Matrix.l2_opNorm_conjTranspose_mul_self Y
    rw [hYstar] at hcstar
    simpa [Ch02.matrixOperatorNorm_eq_l2_opNorm, pow_two] using hcstar
  have hKnorm : Ch02.matrixOperatorNorm K ≤ 2 * H := by
    nlinarith
  have hCnorm : Ch02.matrixOperatorNorm C ≤
      Ch02.matrixOperatorNorm Y + 1 := by
    have hdecomp : C = Y + 1 := by simp [Y]
    rw [hdecomp, Ch02.matrixOperatorNorm_eq_l2_opNorm]
    calc
      ‖Y + (1 : Mat d)‖ ≤ ‖Y‖ + ‖(1 : Mat d)‖ := norm_add_le _ _
      _ = Ch02.matrixOperatorNorm Y + 1 := by
        rw [← Ch02.matrixOperatorNorm_eq_l2_opNorm,
          ← Ch02.matrixOperatorNorm_eq_l2_opNorm,
          Ch02.matrixOperatorNorm_one]
  have hmul : Ch02.matrixOperatorNorm (Y * Y) ≤
      Ch02.matrixOperatorNorm K * Ch02.matrixOperatorNorm C := by
    rw [hYY, ← hK]
    exact Ch02.matrixOperatorNorm_mul_le K C
  have hbound : Ch02.matrixOperatorNorm Y ^ 2 ≤
      (2 * H) * (Ch02.matrixOperatorNorm Y + 1) := by
    rw [← hYsqNorm]
    exact hmul.trans (mul_le_mul hKnorm hCnorm
      (Ch02.matrixOperatorNorm_nonneg C)
      (mul_nonneg (by norm_num) hH))
  have hYnonneg := Ch02.matrixOperatorNorm_nonneg Y
  change Ch02.matrixOperatorNorm Y ^ 2 ≤ 4 * H * (1 + H)
  nlinarith [sq_nonneg (Ch02.matrixOperatorNorm Y - 2 * H)]

private theorem sharpPrimalMismatchMatrix_posSemidef {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) :
    (sharpPrimalMismatchMatrix U a b).PosSemidef := by
  let D := (1 : Mat d) - matrixInvSqrt b * aStarMatrix U a * matrixInvSqrt b
  let C := matrixSqrt b * (aStarMatrix U a)⁻¹ * matrixSqrt b
  have hStar : (aStarMatrix U a).PosDef := aStarMatrix_posDef U a ha
  have hStarInv : ((aStarMatrix U a)⁻¹).PosSemidef :=
    ((Matrix.posDef_inv_iff (M := aStarMatrix U a)).2 hStar).posSemidef
  have hC : C.PosSemidef := by
    have hc := hStarInv.conjTranspose_mul_mul_same (matrixSqrt b)
    have hRstar : Matrix.conjTranspose (matrixSqrt b) = matrixSqrt b := by
      exact Matrix.isHermitian_iff_isSymm.mpr (matrixSqrt_isSymm b)
    rw [hRstar] at hc
    exact hc
  have hDsymm : D.IsSymm := by
    have hS := matrixInvSqrt_isSymm b
    have hAst : (aStarMatrix U a).IsSymm := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hStar.posSemidef.isHermitian
    dsimp [D]
    rw [Matrix.IsSymm]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      hS, hAst]
    simp [Matrix.mul_assoc]
  have hcong := hC.conjTranspose_mul_mul_same D
  have hDCD : (D * C * D).PosSemidef := by
    have hDstar : Matrix.conjTranspose D = D := by
      exact Matrix.isHermitian_iff_isSymm.mpr hDsymm
    rw [hDstar] at hcong
    exact hcong
  simpa [sharpPrimalMismatchMatrix, D, C] using hDCD.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

private theorem sharpPrimalMismatchMatrix_eq_root_mul_transpose {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    sharpPrimalMismatchMatrix U a b =
      (1 / 2 : ℝ) •
        (sharpPrimalMismatchRoot U a b *
          Matrix.transpose (sharpPrimalMismatchRoot U a b)) := by
  let R := matrixSqrt b
  let S := matrixInvSqrt b
  let Astar := aStarMatrix U a
  let T := matrixSqrt Astar
  let Q := matrixInvSqrt Astar
  let D := (1 : Mat d) - S * Astar * S
  let C := R * Astar⁻¹ * R
  let X := S * T - R * Q
  have hAstar : Astar.PosDef := aStarMatrix_posDef U a ha
  have hRS : R * S = 1 := matrixSqrt_mul_matrixInvSqrt hb
  have hSR : S * R = 1 := matrixInvSqrt_mul_matrixSqrt hb
  have hTQ : T * Q = 1 := matrixSqrt_mul_matrixInvSqrt hAstar
  have hQT : Q * T = 1 := matrixInvSqrt_mul_matrixSqrt hAstar
  have hTT : T * T = Astar := matrixSqrt_mul_self hAstar.posSemidef
  have hQQ : Q * Q = Astar⁻¹ := matrixInvSqrt_mul_self hAstar
  have hXt : Matrix.transpose X = T * S - Q * R := by
    have hR := matrixSqrt_isSymm b
    have hS := matrixInvSqrt_isSymm b
    have hT := matrixSqrt_isSymm Astar
    have hQ := matrixInvSqrt_isSymm Astar
    dsimp [X]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      hS, hT, hR, hQ]
  let P := S * Astar * S
  have hSR' (Z : Mat d) : S * (R * Z) = Z := by
    rw [← Matrix.mul_assoc, hSR, one_mul]
  have hRS' (Z : Mat d) : R * (S * Z) = Z := by
    rw [← Matrix.mul_assoc, hRS, one_mul]
  have hAAinv : Astar * Astar⁻¹ = 1 :=
    Matrix.mul_nonsing_inv Astar
      ((Matrix.isUnit_iff_isUnit_det Astar).mp hAstar.isUnit)
  have hAinvA : Astar⁻¹ * Astar = 1 :=
    Matrix.nonsing_inv_mul Astar
      ((Matrix.isUnit_iff_isUnit_det Astar).mp hAstar.isUnit)
  have hAAinv' (Z : Mat d) : Astar * (Astar⁻¹ * Z) = Z := by
    rw [← Matrix.mul_assoc, hAAinv, one_mul]
  have hAinvA' (Z : Mat d) : Astar⁻¹ * (Astar * Z) = Z := by
    rw [← Matrix.mul_assoc, hAinvA, one_mul]
  have hPC : P * C = 1 := by
    dsimp [P, C]
    simp only [Matrix.mul_assoc]
    rw [hSR', hAAinv', hSR]
  have hCP : C * P = 1 := by
    dsimp [P, C]
    simp only [Matrix.mul_assoc]
    rw [hRS', hAinvA', hRS]
  have hTQ' (Z : Mat d) : T * (Q * Z) = Z := by
    rw [← Matrix.mul_assoc, hTQ, one_mul]
  have hQT' (Z : Mat d) : Q * (T * Z) = Z := by
    rw [← Matrix.mul_assoc, hQT, one_mul]
  have hTT' (Z : Mat d) : T * (T * Z) = Astar * Z := by
    rw [← Matrix.mul_assoc, hTT]
  have hQQ' (Z : Mat d) : Q * (Q * Z) = Astar⁻¹ * Z := by
    rw [← Matrix.mul_assoc, hQQ]
  change (1 / 2 : ℝ) • (D * C * D) =
    (1 / 2 : ℝ) • (X * Matrix.transpose X)
  congr 1
  rw [hXt]
  have hleft : D * C * D = C - 1 - 1 + P := by
    have hDP : D = 1 - P := by rfl
    rw [hDP]
    calc
      (1 - P) * C * (1 - P) = C - C * P - P * C + P * C * P := by
        noncomm_ring
      _ = C - 1 - 1 + P := by rw [hCP, hPC, one_mul]
  have hright : X * (T * S - Q * R) = P - 1 - 1 + C := by
    dsimp [X]
    calc
      (S * T - R * Q) * (T * S - Q * R) =
          S * (T * (T * S)) - R * (Q * (T * S)) -
            S * (T * (Q * R)) + R * (Q * (Q * R)) := by
        noncomm_ring
      _ = P - 1 - 1 + C := by
        rw [hTT', hQT', hTQ', hQQ']
        dsimp [P, C]
        rw [hRS, hSR]
        simp only [Matrix.mul_assoc]
  rw [hleft, hright]
  abel

private theorem sharpPrimalMismatchMatrix_norm {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    Ch02.matrixOperatorNorm (sharpPrimalMismatchMatrix U a b) =
      (1 / 2 : ℝ) *
        Ch02.matrixOperatorNorm (sharpPrimalMismatchRoot U a b) ^ 2 := by
  rw [sharpPrimalMismatchMatrix_eq_root_mul_transpose U a ha b hb]
  simp only [Ch02.matrixOperatorNorm_eq_l2_opNorm, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  let X := sharpPrimalMismatchRoot U a b
  have hstar : Matrix.conjTranspose X = Matrix.transpose X := by
    ext i j
    simp [Matrix.conjTranspose]
  have hcstar := Matrix.l2_opNorm_conjTranspose_mul_self (Matrix.conjTranspose X)
  rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at hcstar
  rw [← hstar]
  rw [hcstar]
  ring

private theorem sharpPrimalMismatchMatrix_norm_raw {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (b : Mat d) :
    Ch02.matrixOperatorNorm (sharpPrimalMismatchMatrix U a b) =
      (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
        (((1 : Mat d) - matrixInvSqrt b * aStarMatrix U a * matrixInvSqrt b) *
          (matrixSqrt b * (aStarMatrix U a)⁻¹ * matrixSqrt b) *
          ((1 : Mat d) - matrixInvSqrt b * aStarMatrix U a * matrixInvSqrt b)) := by
  unfold sharpPrimalMismatchMatrix
  simp only [Ch02.matrixOperatorNorm_eq_l2_opNorm, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

private theorem sharpPrimalGapMatrix_norm {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (b : Mat d) :
    Ch02.matrixOperatorNorm (sharpPrimalGapMatrix U a b) =
      (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
        (matrixInvSqrt b * (aMatrix U a - aStarMatrix U a) * matrixInvSqrt b) := by
  unfold sharpPrimalGapMatrix
  simp only [Ch02.matrixOperatorNorm_eq_l2_opNorm, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- The normalized response matrix is positive semidefinite. -/
theorem sharpResponseMatrix_posSemidef {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (ha : a.IsSymmetric) (b : Mat d) :
    (sharpResponseMatrix U a b).PosSemidef := by
  exact (sharpPrimalGapMatrix_posSemidef U a ha b).add
    (sharpPrimalMismatchMatrix_posSemidef U a ha b)

/-- The norm of the normalized response matrix is nonnegative. -/
theorem sharpResponseMax_nonneg {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (b : Mat d) : 0 ≤ sharpResponseMax U a b :=
  Ch02.matrixOperatorNorm_nonneg _

/-- Completed-square identification of the normalized response quadratic
form.  This is the matrix version of `e.J.half.half.identity`. -/
theorem sharpResponse_quadratic {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (ha : a.IsSymmetric) (b : Mat d) (hb : b.PosDef)
    (e : Vec d) :
    J U a (matVecMul (matrixInvSqrt b) e) (matVecMul (matrixSqrt b) e) =
      vecDot e (matVecMul (sharpResponseMatrix U a b) e) := by
  let R := matrixSqrt b
  let S := matrixInvSqrt b
  let A := aMatrix U a
  let Astar := aStarMatrix U a
  let D := (1 : Mat d) - S * Astar * S
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U a ha
  have hRS : R * S = 1 := matrixSqrt_mul_matrixInvSqrt hb
  have hR : R.IsSymm := matrixSqrt_isSymm b
  have hD : D.IsSymm := by
    have hS : S.IsSymm := matrixInvSqrt_isSymm b
    have hAst : Astar.IsSymm := by
      have hp := aStarMatrix_posDef U a ha
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hp.posSemidef.isHermitian
    dsimp [D]
    rw [Matrix.IsSymm]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      hS, hAst]
    simp [Matrix.mul_assoc]
  have hres :
      matVecMul R e - matVecMul Astar (matVecMul S e) =
        matVecMul (R * D) e := by
    have hRSA : R * (S * Astar * S) = Astar * S := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc R S (Astar * S), hRS, one_mul]
    have hm : R - Astar * S = R * D := by
      dsimp [D]
      rw [mul_sub, mul_one, hRSA]
    calc
      matVecMul R e - matVecMul Astar (matVecMul S e) =
          matVecMul (R - Astar * S) e := by
        rw [sub_matVecMul, matVecMul_mul]
      _ = matVecMul (R * D) e := by rw [hm]
  have hquadMismatch :
      vecDot
          (matVecMul R e - matVecMul Astar (matVecMul S e))
          (matVecMul (Astar⁻¹)
            (matVecMul R e - matVecMul Astar (matVecMul S e))) =
        vecDot e (matVecMul (D * (R * Astar⁻¹ * R) * D) e) := by
    rw [hres]
    have ht : Matrix.transpose (R * D) = D * R := by
      rw [Matrix.transpose_mul, hD, hR]
    rw [← vecDot_congruence_transpose (R * D) Astar⁻¹ e, ht]
    simp [Matrix.mul_assoc]
  have hraw := hTheory.response_completed_square_eq
    (matVecMul S e) (matVecMul R e)
  rw [← hTheory.derived_matrices.1, ← hTheory.derived_matrices.2.1,
    ← aStarMatrix_inv_eq_sigmaStarInvCoarse U a ha] at hraw
  rw [hquadMismatch] at hraw
  have hquadGap :
      vecDot (matVecMul S e)
          (matVecMul (A - Astar) (matVecMul S e)) =
        vecDot e (matVecMul (S * (A - Astar) * S) e) := by
    exact (vecDot_congruence S (A - Astar) (matrixInvSqrt_isSymm b) e).symm
  rw [hquadGap] at hraw
  change Ch02.responseJ U a (matVecMul S e) (matVecMul R e) = _
  rw [hraw]
  simp only [sharpResponseMatrix, sharpPrimalGapMatrix,
    sharpPrimalMismatchMatrix, D, R, S, A, Astar]
  rw [add_matVecMul, vecDot_add_right, smul_matVecMul, smul_matVecMul,
    vecDot_smul_right, vecDot_smul_right]

private theorem sharpResponseValueSet_nonempty {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (b : Mat d) :
    (sharpResponseValueSet U a b).Nonempty := by
  let e : Vec d := Pi.single default 1
  refine ⟨J U a (matVecMul (matrixInvSqrt b) e)
    (matVecMul (matrixSqrt b) e), e, ?_, rfl⟩
  simp only [e, vecNormSq, vecDot]
  rw [Finset.sum_eq_single default]
  · simp
  · intro i _ hi
    have hi0 : i ≠ (0 : Fin d) := by simpa using hi
    simp [hi0]
  · simp

private theorem sharpResponseValueSet_bddAbove {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    BddAbove (sharpResponseValueSet U a b) := by
  refine ⟨sharpResponseMax U a b, ?_⟩
  intro y hy
  rcases hy with ⟨e, he, rfl⟩
  rw [sharpResponse_quadratic U a ha b hb e]
  have h := Ch02.vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef
    (sharpResponseMatrix_posSemidef U a ha b) e
  simpa [sharpResponseMax, he] using h

private theorem sharpResponseSup_nonneg {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    0 ≤ sharpResponseSup U a b := by
  let e : Vec d := Pi.single default 1
  have he : vecNormSq e = 1 := by
    simp only [e, vecNormSq, vecDot]
    rw [Finset.sum_eq_single default]
    · simp
    · intro i _ hi
      have hi0 : i ≠ (0 : Fin d) := by simpa using hi
      simp [hi0]
    · simp
  have hmem :
      J U a (matVecMul (matrixInvSqrt b) e) (matVecMul (matrixSqrt b) e) ∈
        sharpResponseValueSet U a b := ⟨e, he, rfl⟩
  exact (Ch02.responseJ_nonneg U a _ _).trans
    (le_csSup (sharpResponseValueSet_bddAbove U a ha b hb) hmem)

private theorem vecDot_matVecMul_smul_vector {d : ℕ} (A : Mat d)
    (c : ℝ) (x : Vec d) :
    vecDot (c • x) (matVecMul A (c • x)) =
      c ^ 2 * vecDot x (matVecMul A x) := by
  have hm : matVecMul A (c • x) = c • matVecMul A x := by
    exact Matrix.mulVec_smul A c x
  rw [hm, vecDot_smul_left, vecDot_smul_right]
  ring

/-- The supremum over unit normalized probes is exactly the operator norm of
the positive response matrix.  Thus `sharpResponseMax` is the paper's
`max_{|e|=1}` (with `max` interpreted harmlessly as `sup`). -/
theorem sharpResponseSup_eq_max {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    sharpResponseSup U a b = sharpResponseMax U a b := by
  have hne := sharpResponseValueSet_nonempty U a b
  have hbdd := sharpResponseValueSet_bddAbove U a ha b hb
  have hsup_le : sharpResponseSup U a b ≤ sharpResponseMax U a b := by
    apply csSup_le hne
    intro y hy
    rcases hy with ⟨e, he, rfl⟩
    rw [sharpResponse_quadratic U a ha b hb e]
    have h := Ch02.vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef
      (sharpResponseMatrix_posSemidef U a ha b) e
    simpa [sharpResponseMax, he] using h
  have hc : 0 ≤ sharpResponseSup U a b :=
    sharpResponseSup_nonneg U a ha b hb
  have hM := sharpResponseMatrix_posSemidef U a ha b
  have hB :
      (sharpResponseSup U a b • (1 : Mat d)).PosSemidef :=
    Matrix.PosSemidef.one.smul hc
  have hLoewner : MatLoewnerLE (sharpResponseMatrix U a b)
      (sharpResponseSup U a b • (1 : Mat d)) := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp [vecDot, matVecMul]
    · have hxnorm : 0 < vecNormSq x := by
        exact lt_of_le_of_ne (vecNormSq_nonneg x)
          (by simpa [vecNormSq_eq_zero_iff, eq_comm] using hx)
      let t := Real.sqrt (vecNormSq x)
      let e : Vec d := t⁻¹ • x
      have ht : 0 < t := Real.sqrt_pos.2 hxnorm
      have htsq : t ^ 2 = vecNormSq x := Real.sq_sqrt hxnorm.le
      have he : vecNormSq e = 1 := by
        dsimp [e]
        rw [vecNormSq_smul]
        field_simp [ht.ne']
        nlinarith
      have hmem :
          J U a (matVecMul (matrixInvSqrt b) e)
              (matVecMul (matrixSqrt b) e) ∈
            sharpResponseValueSet U a b := ⟨e, he, rfl⟩
      have hunit := le_csSup hbdd hmem
      rw [sharpResponse_quadratic U a ha b hb e] at hunit
      change vecDot e (matVecMul (sharpResponseMatrix U a b) e) ≤
        sharpResponseSup U a b at hunit
      have hte : t • e = x := by
        ext i
        simp [e, ht.ne']
      have hscale :
          vecDot x (matVecMul (sharpResponseMatrix U a b) x) =
            t ^ 2 * vecDot e (matVecMul (sharpResponseMatrix U a b) e) := by
        conv_lhs => rw [← hte]
        exact vecDot_matVecMul_smul_vector _ t e
      have hqx :
          vecDot x (matVecMul (sharpResponseMatrix U a b) x) ≤
            sharpResponseSup U a b * vecNormSq x := by
        rw [hscale, ← htsq]
        calc
          t ^ 2 * vecDot e (matVecMul (sharpResponseMatrix U a b) e) ≤
              t ^ 2 * sharpResponseSup U a b :=
            mul_le_mul_of_nonneg_left hunit (sq_nonneg t)
          _ = sharpResponseSup U a b * t ^ 2 := by ring
      rw [smul_matVecMul, vecDot_smul_right]
      have hone : matVecMul (1 : Mat d) x = x := by
        funext i
        simp [matVecMul, Matrix.one_apply]
      rw [hone]
      change vecDot x (matVecMul (sharpResponseMatrix U a b) x) ≤
        sharpResponseSup U a b * vecDot x x at hqx
      nlinarith
  have hop := Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef
    hM hB hLoewner
  have hmax_le : sharpResponseMax U a b ≤ sharpResponseSup U a b := by
    simpa [sharpResponseMax,
      Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hc] using hop
  exact le_antisymm hsup_le hmax_le

/-- The first completed-square comparison, before rewriting the mismatch
summand as the square of a square-root difference. -/
theorem sharpCompareJ_primal_positive_summands {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) :
    sharpResponseMax U a b ≤
        Ch02.matrixOperatorNorm (sharpPrimalGapMatrix U a b) +
          Ch02.matrixOperatorNorm (sharpPrimalMismatchMatrix U a b) ∧
      Ch02.matrixOperatorNorm (sharpPrimalGapMatrix U a b) +
          Ch02.matrixOperatorNorm (sharpPrimalMismatchMatrix U a b) ≤
        2 * sharpResponseMax U a b := by
  simpa [sharpResponseMax, sharpResponseMatrix] using
    matrixOperatorNorm_add_comparison_of_posSemidef
      (sharpPrimalGapMatrix_posSemidef U a ha b)
      (sharpPrimalMismatchMatrix_posSemidef U a ha b)

/-- First source-exact two-sided comparison in `l.sharp.compare.J`. -/
theorem sharpCompareJ_primal {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    sharpResponseSup U a b ≤
        (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (matrixInvSqrt b * (aMatrix U a - aStarMatrix U a) * matrixInvSqrt b) +
        (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (sharpPrimalMismatchRoot U a b) ^ 2 ∧
      (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (matrixInvSqrt b * (aMatrix U a - aStarMatrix U a) * matrixInvSqrt b) +
        (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (sharpPrimalMismatchRoot U a b) ^ 2 ≤
        2 * sharpResponseSup U a b := by
  have h := sharpCompareJ_primal_positive_summands U a ha b
  rw [← sharpResponseSup_eq_max U a ha b hb,
    sharpPrimalGapMatrix_norm U a b,
    sharpPrimalMismatchMatrix_norm U a ha b hb] at h
  exact h

private theorem sharpCompareJ_dual_positive_summands {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    sharpResponseMax U a b ≤
        Ch02.matrixOperatorNorm (sharpDualGapMatrix U a b) +
          Ch02.matrixOperatorNorm (sharpDualMismatchMatrix U a b) ∧
      Ch02.matrixOperatorNorm (sharpDualGapMatrix U a b) +
          Ch02.matrixOperatorNorm (sharpDualMismatchMatrix U a b) ≤
        2 * sharpResponseMax U a b := by
  have h := matrixOperatorNorm_add_comparison_of_posSemidef
    (sharpDualGapMatrix_posSemidef U a ha b)
    (sharpDualMismatchMatrix_posSemidef U a ha b)
  rw [show sharpDualGapMatrix U a b + sharpDualMismatchMatrix U a b =
      sharpResponseMatrix U a b by
    exact sharpDualResponseMatrix_eq_sharpResponseMatrix U a ha b hb] at h
  simpa [sharpResponseMax] using h

/-- Second source-exact two-sided comparison in `l.sharp.compare.J`. -/
theorem sharpCompareJ_dual {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    sharpResponseSup U a b ≤
        (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (matrixSqrt b * ((aMatrix U a)⁻¹ - (aStarMatrix U a)⁻¹) * matrixSqrt b) +
        (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (sharpDualMismatchRoot U a b) ^ 2 ∧
      (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (matrixSqrt b * ((aMatrix U a)⁻¹ - (aStarMatrix U a)⁻¹) * matrixSqrt b) +
        (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (sharpDualMismatchRoot U a b) ^ 2 ≤
        2 * sharpResponseSup U a b := by
  have h := sharpCompareJ_dual_positive_summands U a ha b hb
  rw [← sharpResponseSup_eq_max U a ha b hb,
    sharpDualGapMatrix_norm U a b,
    sharpDualMismatchMatrix_norm U a ha b hb] at h
  have hgapNorm : Ch02.matrixOperatorNorm
        (matrixSqrt b * ((aStarMatrix U a)⁻¹ - (aMatrix U a)⁻¹) * matrixSqrt b) =
      Ch02.matrixOperatorNorm
        (matrixSqrt b * ((aMatrix U a)⁻¹ - (aStarMatrix U a)⁻¹) * matrixSqrt b) := by
    rw [Ch02.matrixOperatorNorm_eq_l2_opNorm,
      Ch02.matrixOperatorNorm_eq_l2_opNorm]
    have heq :
        matrixSqrt b * ((aStarMatrix U a)⁻¹ - (aMatrix U a)⁻¹) * matrixSqrt b =
          -(matrixSqrt b * ((aMatrix U a)⁻¹ - (aStarMatrix U a)⁻¹) * matrixSqrt b) := by
      noncomm_ring
    rw [heq, norm_neg]
  rw [hgapNorm] at h
  exact h

/-- The three normalized coarse-matrix deviations in the concluding display
of `l.sharp.compare.J`, with the explicit admissible universal constant `10`. -/
theorem sharpCompareJ_matrix_deviations {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    Ch02.matrixOperatorNorm
        (matrixInvSqrt b * (aMatrix U a - aStarMatrix U a) * matrixInvSqrt b) +
      Ch02.matrixOperatorNorm
          (matrixSqrt b * (aStarMatrix U a)⁻¹ * matrixSqrt b - 1) ^ 2 +
      Ch02.matrixOperatorNorm
          (matrixInvSqrt b * aMatrix U a * matrixInvSqrt b - 1) ^ 2 ≤
        10 * sharpResponseSup U a b * (1 + sharpResponseSup U a b) := by
  let H := sharpResponseSup U a b
  let R := matrixSqrt b
  let S := matrixInvSqrt b
  let A := aMatrix U a
  let Astar := aStarMatrix U a
  let P := S * Astar * S
  let C := R * Astar⁻¹ * R
  let Q := R * A⁻¹ * R
  let E := S * A * S
  have hH : 0 ≤ H := sharpResponseSup_nonneg U a ha b hb
  have hA : A.PosDef := aMatrix_posDef U a ha
  have hAstar : Astar.PosDef := aStarMatrix_posDef U a ha
  have hGapPos := sharpPrimalGapMatrix_posSemidef U a ha b
  have hMisPos := sharpPrimalMismatchMatrix_posSemidef U a ha b
  have hDualGapPos := sharpDualGapMatrix_posSemidef U a ha b
  have hDualMisPos := sharpDualMismatchMatrix_posSemidef U a ha b
  have hGapLe : Ch02.matrixOperatorNorm (sharpPrimalGapMatrix U a b) ≤ H := by
    calc
      Ch02.matrixOperatorNorm (sharpPrimalGapMatrix U a b) ≤
          Ch02.matrixOperatorNorm (sharpResponseMatrix U a b) := by
        simpa [sharpResponseMatrix] using
          matrixOperatorNorm_left_le_add_of_posSemidef hGapPos hMisPos
      _ = H := by
        rw [← sharpResponseMax, ← sharpResponseSup_eq_max U a ha b hb]
  have hMisLe : Ch02.matrixOperatorNorm (sharpPrimalMismatchMatrix U a b) ≤ H := by
    calc
      Ch02.matrixOperatorNorm (sharpPrimalMismatchMatrix U a b) ≤
          Ch02.matrixOperatorNorm (sharpResponseMatrix U a b) := by
        simpa [sharpResponseMatrix] using
          matrixOperatorNorm_right_le_add_of_posSemidef hGapPos hMisPos
      _ = H := by
        rw [← sharpResponseMax, ← sharpResponseSup_eq_max U a ha b hb]
  have hDualMisLe : Ch02.matrixOperatorNorm (sharpDualMismatchMatrix U a b) ≤ H := by
    calc
      Ch02.matrixOperatorNorm (sharpDualMismatchMatrix U a b) ≤
          Ch02.matrixOperatorNorm (sharpDualResponseMatrix U a b) := by
        simpa [sharpDualResponseMatrix] using
          matrixOperatorNorm_right_le_add_of_posSemidef hDualGapPos hDualMisPos
      _ = Ch02.matrixOperatorNorm (sharpResponseMatrix U a b) := by
        rw [sharpDualResponseMatrix_eq_sharpResponseMatrix U a ha b hb]
      _ = H := by
        rw [← sharpResponseMax, ← sharpResponseSup_eq_max U a ha b hb]
  have hGap : Ch02.matrixOperatorNorm (S * (A - Astar) * S) ≤ 2 * H := by
    rw [sharpPrimalGapMatrix_norm U a b] at hGapLe
    change (1 / 2 : ℝ) * Ch02.matrixOperatorNorm (S * (A - Astar) * S) ≤ H at hGapLe
    linarith
  have hRS : R * S = 1 := matrixSqrt_mul_matrixInvSqrt hb
  have hSR : S * R = 1 := matrixInvSqrt_mul_matrixSqrt hb
  have hSSinv : Astar * Astar⁻¹ = 1 := Matrix.mul_nonsing_inv Astar
    ((Matrix.isUnit_iff_isUnit_det Astar).mp hAstar.isUnit)
  have hSinvS : Astar⁻¹ * Astar = 1 := Matrix.nonsing_inv_mul Astar
    ((Matrix.isUnit_iff_isUnit_det Astar).mp hAstar.isUnit)
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hAinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hSR' (Z : Mat d) : S * (R * Z) = Z := by
    rw [← Matrix.mul_assoc, hSR, one_mul]
  have hRS' (Z : Mat d) : R * (S * Z) = Z := by
    rw [← Matrix.mul_assoc, hRS, one_mul]
  have hSSinv' (Z : Mat d) : Astar * (Astar⁻¹ * Z) = Z := by
    rw [← Matrix.mul_assoc, hSSinv, one_mul]
  have hSinvS' (Z : Mat d) : Astar⁻¹ * (Astar * Z) = Z := by
    rw [← Matrix.mul_assoc, hSinvS, one_mul]
  have hAAinv' (Z : Mat d) : A * (A⁻¹ * Z) = Z := by
    rw [← Matrix.mul_assoc, hAAinv, one_mul]
  have hAinvA' (Z : Mat d) : A⁻¹ * (A * Z) = Z := by
    rw [← Matrix.mul_assoc, hAinvA, one_mul]
  have hPC : P * C = 1 := by
    dsimp [P, C]
    simp only [Matrix.mul_assoc]
    rw [hSR', hSSinv', hSR]
  have hCP : C * P = 1 := by
    dsimp [P, C]
    simp only [Matrix.mul_assoc]
    rw [hRS', hSinvS', hRS]
  have hQE : Q * E = 1 := by
    dsimp [Q, E]
    simp only [Matrix.mul_assoc]
    rw [hRS', hAinvA', hRS]
  have hEQ : E * Q = 1 := by
    dsimp [Q, E]
    simp only [Matrix.mul_assoc]
    rw [hSR', hAAinv', hSR]
  have hCpos : C.PosDef := by
    have hc := hAstar.inv.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit (matrixSqrt_isUnit hb))
    have hRstar : Matrix.conjTranspose R = R := by
      exact Matrix.isHermitian_iff_isSymm.mpr (matrixSqrt_isSymm b)
    rw [hRstar] at hc
    exact hc
  have hSunit : IsUnit S := by
    exact (Matrix.isUnit_nonsing_inv_iff).2 (matrixSqrt_isUnit hb)
  have hEpos : E.PosDef := by
    have he := hA.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hSunit)
    have hSstar : Matrix.conjTranspose S = S := by
      exact Matrix.isHermitian_iff_isSymm.mpr (matrixInvSqrt_isSymm b)
    rw [hSstar] at he
    exact he
  have hMisRaw :
      (1 / 2 : ℝ) * Ch02.matrixOperatorNorm ((1 - P) * C * (1 - P)) ≤ H := by
    rw [sharpPrimalMismatchMatrix_norm_raw U a b] at hMisLe
    exact hMisLe
  have hDualMisRaw :
      (1 / 2 : ℝ) * Ch02.matrixOperatorNorm ((1 - Q) * E * (1 - Q)) ≤ H := by
    rw [sharpDualMismatchMatrix_norm_raw U a b] at hDualMisLe
    exact hDualMisLe
  have hCdev : Ch02.matrixOperatorNorm (C - 1) ^ 2 ≤ 4 * H * (1 + H) :=
    matrix_deviation_sq_le_of_inverse_mismatch hCpos hCP hPC hH hMisRaw
  have hEdev : Ch02.matrixOperatorNorm (E - 1) ^ 2 ≤ 4 * H * (1 + H) :=
    matrix_deviation_sq_le_of_inverse_mismatch hEpos hEQ hQE hH hDualMisRaw
  change Ch02.matrixOperatorNorm (S * (A - Astar) * S) +
      Ch02.matrixOperatorNorm (C - 1) ^ 2 +
      Ch02.matrixOperatorNorm (E - 1) ^ 2 ≤ 10 * H * (1 + H)
  nlinarith [mul_nonneg hH (by linarith : 0 ≤ 1 + H)]

end

end SubdiffusiveProcess.CoarseGrainingVocab
