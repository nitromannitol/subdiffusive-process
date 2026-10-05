module

public import SubdiffusiveProcess.CoarseGrainingVocab.SharpCompareJ

@[expose] public section

/-!
Convex-domain version of `l.sharp.compare.J` (the part of the lemma that the `Ch02` coarse-graining layer proves):
`U` is a nonempty bounded open convex set (`Ch02.Domain`), `a` a.e. symmetric uniformly elliptic on `U`.
`sharpResponseSup U a b = max_{|e| = 1} J(U, b^{-1/2} e, b^{1/2} e; a)` (the supremum over the unit sphere; attained, see
`sharpResponseSup_eq_max`), `aMatrix`/`aStarMatrix` are `a(U)`/`a_*(U)`.  The universal constant of the last display is `10`.
-/

open Homogenization hiding Vec Mat
open Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped Matrix.Norms.L2Operator MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem l_sharp_compare_J_convex {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (ha : a.IsSymmetric)
    (b : Mat d) (hb : b.PosDef) :
    (sharpResponseSup U a b ≤
        (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (matrixInvSqrt b * (aMatrix U a - aStarMatrix U a) * matrixInvSqrt b) +
        (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (matrixInvSqrt b * matrixSqrt (aStarMatrix U a) -
            matrixSqrt b * matrixInvSqrt (aStarMatrix U a)) ^ 2 ∧
      (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (matrixInvSqrt b * (aMatrix U a - aStarMatrix U a) * matrixInvSqrt b) +
        (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (matrixInvSqrt b * matrixSqrt (aStarMatrix U a) -
            matrixSqrt b * matrixInvSqrt (aStarMatrix U a)) ^ 2 ≤
        2 * sharpResponseSup U a b) ∧
    (sharpResponseSup U a b ≤
        (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (matrixSqrt b * ((aMatrix U a)⁻¹ - (aStarMatrix U a)⁻¹) * matrixSqrt b) +
        (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (matrixSqrt b * matrixInvSqrt (aMatrix U a) -
            matrixInvSqrt b * matrixSqrt (aMatrix U a)) ^ 2 ∧
      (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (matrixSqrt b * ((aMatrix U a)⁻¹ - (aStarMatrix U a)⁻¹) * matrixSqrt b) +
        (1 / 2 : ℝ) * Ch02.matrixOperatorNorm
          (matrixSqrt b * matrixInvSqrt (aMatrix U a) -
            matrixInvSqrt b * matrixSqrt (aMatrix U a)) ^ 2 ≤
        2 * sharpResponseSup U a b) ∧
    Ch02.matrixOperatorNorm
        (matrixInvSqrt b * (aMatrix U a - aStarMatrix U a) * matrixInvSqrt b) +
      Ch02.matrixOperatorNorm
          (matrixSqrt b * (aStarMatrix U a)⁻¹ * matrixSqrt b - 1) ^ 2 +
      Ch02.matrixOperatorNorm
          (matrixInvSqrt b * aMatrix U a * matrixInvSqrt b - 1) ^ 2 ≤
        10 * sharpResponseSup U a b * (1 + sharpResponseSup U a b) :=
  ⟨sharpCompareJ_primal U a ha b hb, sharpCompareJ_dual U a ha b hb,
    sharpCompareJ_matrix_deviations U a ha b hb⟩

end SubdiffusiveProcess.Paper
