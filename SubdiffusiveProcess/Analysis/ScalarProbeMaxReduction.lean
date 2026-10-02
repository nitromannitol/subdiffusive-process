import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
import SubdiffusiveProcess.Analysis.LipschitzLpCompact




open MeasureTheory Homogenization Set
open TopologicalSpace Homogenization.Book.Ch02
open scoped ENNReal NNReal Matrix

noncomputable section
namespace SubdiffusiveProcess

/-- The deterministic reference matrix whose operator norm is `paperScalarProbeMax` at
`alpha = 1`: half the sum of the Dirichlet and Neumann coarse matrices, minus the identity. -/
def probeMaxReduction_R {d : ℕ} (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    Mat d :=
  (1 / 2 : ℝ) • Book.Ch02.sigmaCoarse U a + (1 / 2 : ℝ) • Book.Ch02.sigmaStarInvCoarse U a -
    (1 : Mat d)

private theorem probeMaxReduction_vecDot_sub_right {d : ℕ} (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  simp only [vecDot, Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]

theorem probeMaxReduction_R_quad {d : ℕ} (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (hsym : Book.Ch02.CoeffOn.IsSymmetric a) (x : Vec d) :
    vecDot x (matVecMul (probeMaxReduction_R U a) x) = responseJ U a x x := by
  have hthy := responseSymmetricDirichletNeumannTheory U a hsym
  have hsplit := hthy.response_dirichlet_neumann_split x x
  have hd1 := hthy.dirichlet_value_by_sigma x
  have hn1 := hthy.neumann_value_by_sigmaStarInv x
  have hone : matVecMul (1 : Mat d) x = x := by
    show (1 : Mat d) *ᵥ x = x
    exact Matrix.one_mulVec x
  have hexpand : matVecMul (probeMaxReduction_R U a) x =
      (1 / 2 : ℝ) • matVecMul (Book.Ch02.sigmaCoarse U a) x +
        (1 / 2 : ℝ) • matVecMul (Book.Ch02.sigmaStarInvCoarse U a) x - x := by
    unfold probeMaxReduction_R
    rw [sub_matVecMul, add_matVecMul, smul_matVecMul, smul_matVecMul, hone]
  rw [hexpand, probeMaxReduction_vecDot_sub_right, vecDot_add_right,
    vecDot_smul_right, vecDot_smul_right, hsplit, hd1, hn1]

theorem probeMaxReduction_R_posSemidef {d : ℕ} (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (hsym : Book.Ch02.CoeffOn.IsSymmetric a) :
    (probeMaxReduction_R U a).PosSemidef := by
  have hSymmR : (probeMaxReduction_R U a).IsSymm := by
    have h1 : (Book.Ch02.sigmaCoarse U a).IsSymm := sigmaCoarse_isSymm U a
    have h2 : (Book.Ch02.sigmaStarInvCoarse U a).IsSymm := sigmaStarInvCoarse_isSymm U a
    have h3 : (1 : Mat d).IsSymm := Matrix.isSymm_one
    unfold probeMaxReduction_R
    exact ((h1.smul (1 / 2 : ℝ)).add (h2.smul (1 / 2 : ℝ))).sub h3
  have hzero : (0 : Mat d).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · simp [Matrix.IsHermitian]
    · intro x; simp
  have hLoewner : MatLoewnerLE 0 (probeMaxReduction_R U a) := by
    intro x
    have hq := probeMaxReduction_R_quad U a hsym x
    have hnn : 0 ≤ responseJ U a x x :=
      responseJ_nonneg U a x x
    have hzero_mv : matVecMul (0 : Mat d) x = 0 := by
      show (0 : Mat d) *ᵥ x = 0
      simp
    rw [hzero_mv, vecDot_zero_right, hq]
    linarith
  exact posSemidef_of_matLoewnerLE_of_posSemidef_of_isSymm
    hzero hSymmR hLoewner

theorem probeMaxReduction_R_hquad {d : ℕ} (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (hsym : Book.Ch02.CoeffOn.IsSymmetric a) (e : Vec d) :
    SubdiffusiveProcess.CoarseGrainingVocab.J U a ((Real.sqrt 1)⁻¹ • e) (Real.sqrt 1 • e) =
      vecDot e (matVecMul (probeMaxReduction_R U a) e) := by
  rw [Real.sqrt_one, inv_one, one_smul]
  exact (probeMaxReduction_R_quad U a hsym e).symm

/-- `paperScalarProbeMax` at `alpha = 1`, reduced to the operator norm of `probeMaxReduction_R`,
at a GENERAL cube `Q` (not just the origin cube). -/
theorem probeMaxReduction_eq {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    (hsym : Book.Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax Q a 1 =
      ENNReal.ofReal
        (matrixOperatorNorm (probeMaxReduction_R (cubeDomain Q) (a.coeffOn Q))) := by
  show SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMaxOn (cubeDomain Q) (a.coeffOn Q) 1 = _
  exact SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMaxOn_eq_ofReal_matrixOperatorNorm
    (cubeDomain Q) (a.coeffOn Q) 1 (probeMaxReduction_R (cubeDomain Q) (a.coeffOn Q))
    (probeMaxReduction_R_posSemidef (cubeDomain Q) (a.coeffOn Q) hsym)
    (probeMaxReduction_R_hquad (cubeDomain Q) (a.coeffOn Q) hsym)

theorem probeMaxReduction_toReal {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    (hsym : Book.Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) :
    (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax Q a 1).toReal =
      matrixOperatorNorm (probeMaxReduction_R (cubeDomain Q) (a.coeffOn Q)) := by
  rw [probeMaxReduction_eq Q a hsym]
  exact ENNReal.toReal_ofReal (matrixOperatorNorm_nonneg _)

/-- The scalar function combining the sigma/sigmaStarInv/identity entries (flattened over
`Fin d × Fin d × Fin 3`, third coordinate `0`/`1`/`2` selecting sigma/sigmaStarInv/identity) into
`probeMaxReduction_R`'s `matrixNorm`. -/
def probeMaxReduction_g (d : ℕ) : (Fin d × Fin d × Fin 3 → ℝ) → ℝ :=
  fun entries => matrixNorm (fun i j =>
    (1 / 2 : ℝ) * (entries (i, j, 0) + entries (i, j, 1)) - entries (i, j, 2))

theorem probeMaxReduction_g0 (d : ℕ) [NeZero d] :
    probeMaxReduction_g d 0 = 0 := by
  have hz : (fun i j : Fin d => (1 / 2 : ℝ) *
      ((0 : Fin d × Fin d × Fin 3 → ℝ) (i, j, 0) + (0 : Fin d × Fin d × Fin 3 → ℝ) (i, j, 1)) -
        (0 : Fin d × Fin d × Fin 3 → ℝ) (i, j, 2)) = (0 : Matrix (Fin d) (Fin d) ℝ) := by
    funext i j
    simp
  unfold probeMaxReduction_g
  rw [hz]
  unfold matrixNorm
  simp

theorem probeMaxReduction_glip (d : ℕ) :
    ∀ u v : Fin d × Fin d × Fin 3 → ℝ,
      |probeMaxReduction_g d u - probeMaxReduction_g d v| ≤
        (Fintype.card (Fin d) : ℝ) * ∑ p, |u p - v p| := by
  intro u v
  unfold probeMaxReduction_g
  have hstep := matrixNorm_lipschitz
    (fun i j => (1 / 2 : ℝ) * (u (i, j, 0) + u (i, j, 1)) - u (i, j, 2))
    (fun i j => (1 / 2 : ℝ) * (v (i, j, 0) + v (i, j, 1)) - v (i, j, 2))
  refine hstep.trans ?_
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hbound : ∀ i j : Fin d,
      |((1 / 2 : ℝ) * (u (i, j, 0) + u (i, j, 1)) - u (i, j, 2)) -
        ((1 / 2 : ℝ) * (v (i, j, 0) + v (i, j, 1)) - v (i, j, 2))| ≤
      |u (i, j, 0) - v (i, j, 0)| + |u (i, j, 1) - v (i, j, 1)| + |u (i, j, 2) - v (i, j, 2)| := by
    intro i j
    have heq : ((1 / 2 : ℝ) * (u (i, j, 0) + u (i, j, 1)) - u (i, j, 2)) -
        ((1 / 2 : ℝ) * (v (i, j, 0) + v (i, j, 1)) - v (i, j, 2)) =
        (1 / 2 : ℝ) * (u (i, j, 0) - v (i, j, 0)) +
          ((1 / 2 : ℝ) * (u (i, j, 1) - v (i, j, 1)) + -(u (i, j, 2) - v (i, j, 2))) := by
      ring
    rw [heq]
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [neg_abs_le (u (i, j, 0) - v (i, j, 0)), neg_abs_le (u (i, j, 1) - v (i, j, 1)),
        le_abs_self (u (i, j, 2) - v (i, j, 2)), abs_nonneg (u (i, j, 0) - v (i, j, 0)),
        abs_nonneg (u (i, j, 1) - v (i, j, 1))]
    · linarith [le_abs_self (u (i, j, 0) - v (i, j, 0)), le_abs_self (u (i, j, 1) - v (i, j, 1)),
        neg_abs_le (u (i, j, 2) - v (i, j, 2)), abs_nonneg (u (i, j, 0) - v (i, j, 0)),
        abs_nonneg (u (i, j, 1) - v (i, j, 1))]
  refine (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hbound i j))).trans ?_
  have hsplit : ∀ i j : Fin d,
      |u (i, j, 0) - v (i, j, 0)| + |u (i, j, 1) - v (i, j, 1)| + |u (i, j, 2) - v (i, j, 2)| =
        ∑ k : Fin 3, |u (i, j, k) - v (i, j, k)| := by
    intro i j
    rw [Fin.sum_univ_three]
  simp_rw [hsplit]
  have hflat : (∑ p : Fin d × Fin d × Fin 3, |u p - v p|) =
      ∑ i, ∑ j, ∑ k, |u (i, j, k) - v (i, j, k)| := by
    rw [Fintype.sum_prod_type]
    congr 1
    funext i
    rw [Fintype.sum_prod_type]
  rw [hflat]

end SubdiffusiveProcess
