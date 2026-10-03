module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.CoarseGrainingVocab.SharpCompareJ

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff MatrixOrder Matrix.Norms.L2Operator
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_inputs_J_deviation_by_J_scalar_roots {d : ℕ}
    (a0 : ℝ) (ha0 : 0 < a0) :
    SubdiffusiveProcess.CoarseGrainingVocab.matrixSqrt (a0 • (1 : Homogenization.Mat d)) =
        Real.sqrt a0 • (1 : Homogenization.Mat d) ∧
      SubdiffusiveProcess.CoarseGrainingVocab.matrixInvSqrt (a0 • (1 : Homogenization.Mat d)) =
        (Real.sqrt a0)⁻¹ • (1 : Homogenization.Mat d) := by
  have hsqrt : SubdiffusiveProcess.CoarseGrainingVocab.matrixSqrt
      (a0 • (1 : Homogenization.Mat d)) =
      Real.sqrt a0 • (1 : Homogenization.Mat d) := by
    have hsqr : Real.sqrt a0 * Real.sqrt a0 = a0 := by
      rw [← sq]
      exact Real.sq_sqrt ha0.le
    apply CFC.sqrt_unique
    · calc
        (Real.sqrt a0 • (1 : Homogenization.Mat d)) *
            (Real.sqrt a0 • (1 : Homogenization.Mat d)) =
          Real.sqrt a0 • (Real.sqrt a0 • (1 : Homogenization.Mat d)) := by
            rw [smul_mul_assoc, Matrix.one_mul]
        _ = (Real.sqrt a0 * Real.sqrt a0) • (1 : Homogenization.Mat d) := by
          rw [← smul_smul]
        _ = a0 • (1 : Homogenization.Mat d) := by rw [hsqr]
    · rw [Matrix.nonneg_iff_posSemidef]
      exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (Real.sqrt_nonneg a0)
  have hsqrt_ne : Real.sqrt a0 ≠ 0 := (Real.sqrt_pos.2 ha0).ne'
  have hinv : SubdiffusiveProcess.CoarseGrainingVocab.matrixInvSqrt
      (a0 • (1 : Homogenization.Mat d)) =
      (Real.sqrt a0)⁻¹ • (1 : Homogenization.Mat d) := by
    change (SubdiffusiveProcess.CoarseGrainingVocab.matrixSqrt
      (a0 • (1 : Homogenization.Mat d)))⁻¹ = _
    rw [hsqrt]
    letI : Invertible (Real.sqrt a0) := invertibleOfNonzero hsqrt_ne
    rw [Matrix.inv_smul (A := (1 : Homogenization.Mat d)) (Real.sqrt a0) (by simp)]
    simp
  exact ⟨hsqrt, hinv⟩

theorem inputs_J_deviation_by_J (d : ℕ) (hd : 2 ≤ d) :
    (∃ C : ℝ, 0 < C ∧
      ∀ (U : Homogenization.Book.Ch02.Domain d)
        (a : Homogenization.Book.Ch02.CoeffOn U),
        Homogenization.Book.Ch02.CoeffOn.IsSymmetric a →
      ∀ a0 : ℝ, 0 < a0 →
      ∀ Jmax : ℝ,
        IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
            Homogenization.vecNormSq e = 1 ∧
            t = Homogenization.Book.Ch02.responseJ U a
              ((Real.sqrt a0)⁻¹ • e) (Real.sqrt a0 • e)} Jmax →
      ∀ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 →
        (a0⁻¹ * Homogenization.vecDot e
            (Homogenization.matVecMul
              (Homogenization.Book.Ch02.sigmaCoarse U a) e) - 1) ^ 2 +
          (a0 * Homogenization.vecDot e
            (Homogenization.matVecMul
              (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) e) - 1) ^ 2 ≤
        C * Jmax * (1 + Jmax)) := by
  letI : NeZero d := ⟨ne_of_gt (lt_of_lt_of_le (by norm_num) hd)⟩
  refine ⟨10, by norm_num, ?_⟩
  intro U a ha a0 ha0 Jmax hJ e he
  let b : Homogenization.Mat d := a0 • (1 : Homogenization.Mat d)
  have hb : b.PosDef := by
    have hI : (1 : Homogenization.Mat d).PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
      · exact Matrix.isHermitian_one
      · intro x hx
        simpa using (Matrix.dotProduct_star_self_pos_iff.mpr hx)
    exact hI.smul ha0
  have hroots := aux_inputs_J_deviation_by_J_scalar_roots (d := d) a0 ha0
  have hsqrt := hroots.1
  have hinvsqrt := hroots.2
  have hTheory := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory U a ha
  have hA : SubdiffusiveProcess.CoarseGrainingVocab.aMatrix U a =
      Homogenization.Book.Ch02.sigmaCoarse U a := by
    simpa [SubdiffusiveProcess.CoarseGrainingVocab.aMatrix] using hTheory.derived_matrices.1
  have hAstar : SubdiffusiveProcess.CoarseGrainingVocab.aStarMatrix U a =
      Homogenization.Book.Ch02.sigmaStarCoarse U a := by
    simpa [SubdiffusiveProcess.CoarseGrainingVocab.aStarMatrix] using hTheory.derived_matrices.2.1
  have hAstarInv : (SubdiffusiveProcess.CoarseGrainingVocab.aStarMatrix U a)⁻¹ =
      Homogenization.Book.Ch02.sigmaStarInvCoarse U a := by
    rw [hAstar, Homogenization.Book.Ch02.sigmaStarCoarse]
    exact Matrix.nonsing_inv_nonsing_inv _
      (Homogenization.Book.Ch02.isUnit_det_sigmaStarInvCoarse U a)
  have hprimalMatrix :
      SubdiffusiveProcess.CoarseGrainingVocab.matrixInvSqrt b *
          SubdiffusiveProcess.CoarseGrainingVocab.aMatrix U a *
          SubdiffusiveProcess.CoarseGrainingVocab.matrixInvSqrt b - 1 =
        a0⁻¹ • Homogenization.Book.Ch02.sigmaCoarse U a - 1 := by
    rw [hinvsqrt, hA]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (Real.sqrt a0)⁻¹ * (Real.sqrt a0)⁻¹ = a0⁻¹ by
      field_simp
      nlinarith [Real.sq_sqrt ha0.le]]
    simp
  have hdualMatrix :
      SubdiffusiveProcess.CoarseGrainingVocab.matrixSqrt b *
          (SubdiffusiveProcess.CoarseGrainingVocab.aStarMatrix U a)⁻¹ *
          SubdiffusiveProcess.CoarseGrainingVocab.matrixSqrt b - 1 =
        a0 • Homogenization.Book.Ch02.sigmaStarInvCoarse U a - 1 := by
    rw [hsqrt, hAstarInv]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hsqr : Real.sqrt a0 * Real.sqrt a0 = a0 := by
      rw [← sq]
      exact Real.sq_sqrt ha0.le
    rw [hsqr]
    simp
  have hsharpSubset :
      SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseValueSet U a b ⊆
        {t : ℝ | ∃ v : Homogenization.Vec d, Homogenization.vecNormSq v = 1 ∧
          t = Homogenization.Book.Ch02.responseJ U a
            ((Real.sqrt a0)⁻¹ • v) (Real.sqrt a0 • v)} := by
    rintro t ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    change SubdiffusiveProcess.CoarseGrainingVocab.J U a
      (Homogenization.matVecMul (SubdiffusiveProcess.CoarseGrainingVocab.matrixInvSqrt b) v)
      (Homogenization.matVecMul (SubdiffusiveProcess.CoarseGrainingVocab.matrixSqrt b) v) = _
    rw [hinvsqrt, hsqrt, Homogenization.matVecMul_smul_one,
      Homogenization.matVecMul_smul_one]
  have hJmaxMem : Jmax ∈ SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseValueSet U a b := by
    rcases hJ.1 with ⟨v, hv, hvval⟩
    refine ⟨v, hv, ?_⟩
    change Jmax = SubdiffusiveProcess.CoarseGrainingVocab.J U a
      (Homogenization.matVecMul (SubdiffusiveProcess.CoarseGrainingVocab.matrixInvSqrt b) v)
      (Homogenization.matVecMul (SubdiffusiveProcess.CoarseGrainingVocab.matrixSqrt b) v)
    rw [hinvsqrt, hsqrt, Homogenization.matVecMul_smul_one,
      Homogenization.matVecMul_smul_one]
    exact hvval
  have hH : SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b ≤ Jmax := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup
    exact csSup_le ⟨Jmax, hJmaxMem⟩ (fun t ht => hJ.2 (hsharpSubset ht))
  have hdev := SubdiffusiveProcess.CoarseGrainingVocab.sharpCompareJ_matrix_deviations U a ha b hb
  have hdev' :
      Homogenization.Book.Ch02.matrixOperatorNorm
          (a0 • Homogenization.Book.Ch02.sigmaStarInvCoarse U a - 1) ^ 2 +
        Homogenization.Book.Ch02.matrixOperatorNorm
          (a0⁻¹ • Homogenization.Book.Ch02.sigmaCoarse U a - 1) ^ 2 ≤
      10 * SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b *
        (1 + SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b) := by
    have hn0 := Homogenization.Book.Ch02.matrixOperatorNorm_nonneg
      (SubdiffusiveProcess.CoarseGrainingVocab.matrixInvSqrt b *
        (SubdiffusiveProcess.CoarseGrainingVocab.aMatrix U a - SubdiffusiveProcess.CoarseGrainingVocab.aStarMatrix U a) *
        SubdiffusiveProcess.CoarseGrainingVocab.matrixInvSqrt b)
    rw [hdualMatrix, hprimalMatrix] at hdev
    linarith [hdev]
  have hJmaxNonneg : 0 ≤ Jmax := by
    rcases hJ.1 with ⟨v, hv, hvval⟩
    rw [hvval]
    exact Homogenization.Book.Ch02.responseJ_nonneg U a
      ((Real.sqrt a0)⁻¹ • v) (Real.sqrt a0 • v)
  have hHnonneg : 0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup
    have hbdd : BddAbove (SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseValueSet U a b) :=
      ⟨Jmax, fun t ht => hJ.2 (hsharpSubset ht)⟩
    exact hJmaxNonneg.trans (le_csSup hbdd hJmaxMem)
  have hfactor : SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b *
        (1 + SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b) ≤ Jmax * (1 + Jmax) := by
    nlinarith [mul_nonneg (show 0 ≤ Jmax - SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b by linarith)
      (show 0 ≤ 1 + Jmax + SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b by linarith)]
  have hfactor' :
      10 * SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b *
          (1 + SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b) ≤
        10 * Jmax * (1 + Jmax) := by
    calc
      10 * SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b *
          (1 + SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b) =
        10 * (SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b *
          (1 + SubdiffusiveProcess.CoarseGrainingVocab.sharpResponseSup U a b)) := by ring
      _ ≤ 10 * (Jmax * (1 + Jmax)) :=
        mul_le_mul_of_nonneg_left hfactor (by norm_num)
      _ = 10 * Jmax * (1 + Jmax) := by ring
  have hdev'' := hdev'.trans hfactor'
  have hquad :
      (a0⁻¹ * Homogenization.vecDot e
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) e) - 1) ^ 2 ≤
        Homogenization.Book.Ch02.matrixOperatorNorm
            (a0⁻¹ • Homogenization.Book.Ch02.sigmaCoarse U a - 1) ^ 2 ∧
      (a0 * Homogenization.vecDot e
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) e) - 1) ^ 2 ≤
        Homogenization.Book.Ch02.matrixOperatorNorm
            (a0 • Homogenization.Book.Ch02.sigmaStarInvCoarse U a - 1) ^ 2 := by
    constructor
    · have habs := Homogenization.Book.Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
        (a0⁻¹ • Homogenization.Book.Ch02.sigmaCoarse U a - 1) e
      rw [he] at habs
      have hdot : Homogenization.vecDot e
          (Homogenization.matVecMul (a0⁻¹ • Homogenization.Book.Ch02.sigmaCoarse U a - 1) e) =
          a0⁻¹ * Homogenization.vecDot e
            (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) e) - 1 := by
        rw [Homogenization.sub_matVecMul, Homogenization.smul_matVecMul]
        rw [sub_eq_add_neg, Homogenization.vecDot_add_right,
          Homogenization.vecDot_neg_right, Homogenization.vecDot_smul_right]
        have hId : Homogenization.matVecMul (1 : Homogenization.Mat d) e = e := by
          ext i
          simp [Homogenization.matVecMul, Matrix.one_apply]
        rw [hId]
        change a0⁻¹ * Homogenization.vecDot e
            (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) e) -
          Homogenization.vecNormSq e = _
        rw [he]
      rw [hdot] at habs
      have habs' : |a0⁻¹ * Homogenization.vecDot e
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaCoarse U a) e) - 1| ≤
          Homogenization.Book.Ch02.matrixOperatorNorm
            (a0⁻¹ • Homogenization.Book.Ch02.sigmaCoarse U a - 1) := by
        simpa using habs
      have hsq := (sq_le_sq₀ (abs_nonneg _)
        (Homogenization.Book.Ch02.matrixOperatorNorm_nonneg _)).2 habs'
      simpa [sq_abs] using hsq
    · have habs := Homogenization.Book.Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
        (a0 • Homogenization.Book.Ch02.sigmaStarInvCoarse U a - 1) e
      rw [he] at habs
      have hdot : Homogenization.vecDot e
          (Homogenization.matVecMul (a0 • Homogenization.Book.Ch02.sigmaStarInvCoarse U a - 1) e) =
          a0 * Homogenization.vecDot e
            (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) e) - 1 := by
        rw [Homogenization.sub_matVecMul, Homogenization.smul_matVecMul]
        rw [sub_eq_add_neg, Homogenization.vecDot_add_right,
          Homogenization.vecDot_neg_right, Homogenization.vecDot_smul_right]
        have hId : Homogenization.matVecMul (1 : Homogenization.Mat d) e = e := by
          ext i
          simp [Homogenization.matVecMul, Matrix.one_apply]
        rw [hId]
        change a0 * Homogenization.vecDot e
            (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) e) -
          Homogenization.vecNormSq e = _
        rw [he]
      rw [hdot] at habs
      have habs' : |a0 * Homogenization.vecDot e
          (Homogenization.matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse U a) e) - 1| ≤
          Homogenization.Book.Ch02.matrixOperatorNorm
            (a0 • Homogenization.Book.Ch02.sigmaStarInvCoarse U a - 1) := by
        simpa using habs
      have hsq := (sq_le_sq₀ (abs_nonneg _)
        (Homogenization.Book.Ch02.matrixOperatorNorm_nonneg _)).2 habs'
      simpa [sq_abs] using hsq
  nlinarith [hquad.1, hquad.2, hdev'']

end Paper

