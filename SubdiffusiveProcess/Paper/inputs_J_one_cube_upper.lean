module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CarrierComparison

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_inputs_J_one_cube_upper_probe (d : ℕ) [NeZero d]
    (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hSymm : Homogenization.Book.Ch02.CoeffOn.IsSymmetric (F.coeffOn Q))
    {σ : ℝ} (hσ : 0 < σ) (e : Homogenization.Vec d)
    (he : Homogenization.vecNormSq e = 1) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe Q F σ e ≤
      (σ⁻¹ * Homogenization.Book.Ch02.coarseBMatrixNorm Q F +
       σ * Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q F) / 2 := by
  let U := Homogenization.Book.Ch02.cubeDomain Q
  let a := F.coeffOn Q
  let p := (Real.sqrt σ)⁻¹ • e
  let q := Real.sqrt σ • e
  have hTheory := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory
    U a hSymm
  have hCanonical := Homogenization.Book.Ch02.canonicalResponseMatrixIdentities U a
  have hFormula := Homogenization.Book.Ch02.responseJ_eq_canonical_coarseMatrices_formula
    hCanonical p q
  have hSqrt : Real.sqrt σ ≠ 0 := (Real.sqrt_pos.2 hσ).ne'
  have hNormP : Homogenization.vecNormSq p = σ⁻¹ := by
    simp [p, Homogenization.vecNormSq_smul, he, Real.sq_sqrt hσ.le]
  have hNormQ : Homogenization.vecNormSq q = σ := by
    simp [q, Homogenization.vecNormSq_smul, he, Real.sq_sqrt hσ.le]
  have hCross : Homogenization.vecDot p q = 1 := by
    dsimp [p, q]
    rw [Homogenization.vecDot_smul_left, Homogenization.vecDot_smul_right]
    have he' : Homogenization.vecDot e e = 1 := by
      simpa [Homogenization.vecNormSq] using he
    rw [he']
    field_simp
  have hResponse : Homogenization.Book.Ch02.responseJ U a p q =
      (1 / 2 : ℝ) * Homogenization.vecDot p
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) p) +
        (1 / 2 : ℝ) * Homogenization.vecDot q
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) q) -
        Homogenization.vecDot p q := by
    have hmul : Homogenization.matVecMul (0 : Homogenization.Mat d) p = 0 :=
      Homogenization.zero_matVecMul p
    rw [hFormula, hTheory.kappa_eq_zero, hmul]
    simp
  have hBNorm : Homogenization.Book.Ch02.matrixOperatorNorm
      (Homogenization.Book.Ch02.sigmaCoarse U a) =
        Homogenization.Book.Ch02.coarseBMatrixNorm Q F := by
    calc
      Homogenization.Book.Ch02.matrixOperatorNorm
          (Homogenization.Book.Ch02.sigmaCoarse U a) =
          Homogenization.Book.Ch02.matrixNorm
            (Homogenization.Book.Ch02.sigmaCoarse U a) :=
        (Homogenization.Book.Ch02.matrixNorm_eq_matrixOperatorNorm _).symm
      _ = Homogenization.Book.Ch02.matrixNorm
            (Homogenization.Book.Ch02.bCoarse U a) :=
        congrArg Homogenization.Book.Ch02.matrixNorm hTheory.derived_matrices.2.2.symm
      _ = Homogenization.Book.Ch02.coarseBMatrixNorm Q F := rfl
  have hInvNorm : Homogenization.Book.Ch02.matrixOperatorNorm
      (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) =
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q F := by
    calc
      Homogenization.Book.Ch02.matrixOperatorNorm
          (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) =
          Homogenization.Book.Ch02.matrixNorm
            (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) :=
        (Homogenization.Book.Ch02.matrixNorm_eq_matrixOperatorNorm _).symm
      _ = Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q F := rfl
  have hQuadP : Homogenization.vecDot p
      (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) p) ≤
        Homogenization.Book.Ch02.matrixOperatorNorm
            (Homogenization.Book.Ch02.sigmaCoarse U a) *
          Homogenization.vecNormSq p :=
    (le_abs_self _).trans
      (Homogenization.Book.Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
        _ _)
  have hQuadQ : Homogenization.vecDot q
      (Homogenization.matVecMul
        (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) q) ≤
        Homogenization.Book.Ch02.matrixOperatorNorm
            (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) *
          Homogenization.vecNormSq q :=
    (le_abs_self _).trans
      (Homogenization.Book.Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
        _ _)
  have hQuadP' : Homogenization.vecDot p
      (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) p) ≤
        Homogenization.Book.Ch02.coarseBMatrixNorm Q F * σ⁻¹ := by
    rw [hNormP, hBNorm] at hQuadP
    exact hQuadP
  have hQuadQ' : Homogenization.vecDot q
      (Homogenization.matVecMul
        (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) q) ≤
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q F * σ := by
    rw [hNormQ, hInvNorm] at hQuadQ
    exact hQuadQ
  change Homogenization.Book.Ch02.responseJ U a p q ≤ _
  rw [hResponse, hCross]
  nlinarith [hQuadP', hQuadQ']

theorem inputs_J_one_cube_upper (d : ℕ) [NeZero d] (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hSymm : Homogenization.Book.Ch02.CoeffOn.IsSymmetric (F.coeffOn Q))
    {σ : ℝ} (hσ : 0 < σ) :
    (Homogenization.Book.Ch02.normalizedBlockResponseMax Q F (Homogenization.scalarMatrix σ) ≤
      (σ⁻¹ * Homogenization.Book.Ch02.coarseBMatrixNorm Q F +
       σ * Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q F) / 2) := by
  have hBNonneg : 0 ≤ Homogenization.Book.Ch02.coarseBMatrixNorm Q F := by
    change 0 ≤ Homogenization.Book.Ch02.matrixNorm
      (Homogenization.Book.Ch02.bCoarse
        (Homogenization.Book.Ch02.cubeDomain Q) (F.coeffOn Q))
    exact Homogenization.Book.Ch02.matrixNorm_nonneg _
  have hInvNonneg : 0 ≤ Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q F := by
    change 0 ≤ Homogenization.Book.Ch02.matrixNorm
      (Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain Q) (F.coeffOn Q))
    exact Homogenization.Book.Ch02.matrixNorm_nonneg _
  have hBoundNonneg : 0 ≤
      (σ⁻¹ * Homogenization.Book.Ch02.coarseBMatrixNorm Q F +
       σ * Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q F) / 2 := by
    apply div_nonneg
    · exact add_nonneg
        (mul_nonneg (inv_nonneg.mpr hσ.le) hBNonneg)
        (mul_nonneg hσ.le hInvNonneg)
    · norm_num
  have hPaper : SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax Q F σ ≤
      ENNReal.ofReal
        ((σ⁻¹ * Homogenization.Book.Ch02.coarseBMatrixNorm Q F +
         σ * Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q F) / 2) := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax
    refine iSup_le ?_
    intro e
    exact ENNReal.ofReal_le_ofReal
      (aux_inputs_J_one_cube_upper_probe d Q F hSymm hσ e.1 e.2)
  have hCarrier :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.paperScalarProbeMax_eq_ofReal_normalizedBlockResponseMax
      Q F hSymm hσ
  have hReal : ENNReal.ofReal
      (Homogenization.Book.Ch02.normalizedBlockResponseMax Q F
        (Homogenization.scalarMatrix σ)) ≤
        ENNReal.ofReal
          ((σ⁻¹ * Homogenization.Book.Ch02.coarseBMatrixNorm Q F +
           σ * Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q F) / 2) := by
    rw [← hCarrier]
    exact hPaper
  exact (ENNReal.ofReal_le_ofReal_iff hBoundNonneg).mp hReal

end Paper

