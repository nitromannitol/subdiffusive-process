module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.Arithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.Carrier

@[expose] public section

/-!
# Pointwise consequences of small contrast

The source informally replaces `||a-Id|| <= delta` by `Id <= a`.  The latter
does not follow.  The correct consequence is coercivity at `1-delta`; combined
with `delta < 1/2`, it gives the same factor `2` in the harmonic-comparison
estimate printed in the proof.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

open Homogenization
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

private theorem matVecMul_sub_one (A : Mat d) (v : Vec d) :
    matVecMul (A - 1) v = matVecMul A v - v := by
  classical
  funext i
  simp only [matVecMul, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  simp [Matrix.one_apply]
  rfl

private theorem vecDot_self_eq_vecNormSq (v : Vec d) :
    vecDot v v = vecNormSq v := rfl

/-- Operator-norm closeness controls the perturbative quadratic form. -/
theorem abs_vecDot_coefficient_sub_identity_le {A : Mat d} {delta : ℝ}
    (hA : matrixOperatorNorm (A - 1) ≤ delta) (v : Vec d) :
    |vecDot v (matVecMul (A - 1) v)| ≤ delta * vecNormSq v := by
  exact (abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq (A - 1) v).trans
    (mul_le_mul_of_nonneg_right hA (vecNormSq_nonneg v))

/-- The honest lower ellipticity bound supplied by small contrast. -/
theorem one_sub_mul_vecNormSq_le_vecDot_coefficient {A : Mat d} {delta : ℝ}
    (hA : matrixOperatorNorm (A - 1) ≤ delta) (v : Vec d) :
    (1 - delta) * vecNormSq v ≤ vecDot v (matVecMul A v) := by
  have hdev := abs_vecDot_coefficient_sub_identity_le hA v
  have hlow : -delta * vecNormSq v ≤ vecDot v (matVecMul (A - 1) v) := by
    simpa only [neg_mul] using neg_le_of_abs_le hdev
  have hsplit : vecDot v (matVecMul A v) =
      vecNormSq v + vecDot v (matVecMul (A - 1) v) := by
    have hv : matVecMul A v = v + matVecMul (A - 1) v := by
      rw [matVecMul_sub_one]
      abel
    rw [hv, vecDot_add_right, vecDot_self_eq_vecNormSq]
  rw [hsplit]
  linarith

/-- The corresponding upper quadratic-form estimate. -/
theorem vecDot_coefficient_le_one_add_mul_vecNormSq {A : Mat d} {delta : ℝ}
    (hA : matrixOperatorNorm (A - 1) ≤ delta) (v : Vec d) :
    vecDot v (matVecMul A v) ≤ (1 + delta) * vecNormSq v := by
  have hdev := abs_vecDot_coefficient_sub_identity_le hA v
  have hupp : vecDot v (matVecMul (A - 1) v) ≤ delta * vecNormSq v :=
    le_trans (le_abs_self _) hdev
  have hsplit : vecDot v (matVecMul A v) =
      vecNormSq v + vecDot v (matVecMul (A - 1) v) := by
    have hv : matVecMul A v = v + matVecMul (A - 1) v := by
      rw [matVecMul_sub_one]
      abel
    rw [hv, vecDot_add_right, vecDot_self_eq_vecNormSq]
  rw [hsplit]
  linarith

/-- The printed smallness assumption supplies the honest half-coercivity used
in the corrected energy test. -/
theorem half_mul_vecNormSq_le_vecDot_coefficient_of_smallContrast
    {A : Mat d} {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hA : matrixOperatorNorm (A - 1) ≤ smallContrastThreshold d alpha)
    (v : Vec d) :
    (1 / 2 : ℝ) * vecNormSq v ≤ vecDot v (matVecMul A v) := by
  have hbase := one_sub_mul_vecNormSq_le_vecDot_coefficient hA v
  have hsmall := smallContrastThreshold_lt_half d halpha0 halpha1
  have hnorm := vecNormSq_nonneg v
  calc
    (1 / 2 : ℝ) * vecNormSq v ≤
        (1 - smallContrastThreshold d alpha) * vecNormSq v := by
      gcongr
      linarith
    _ ≤ vecDot v (matVecMul A v) := hbase

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
