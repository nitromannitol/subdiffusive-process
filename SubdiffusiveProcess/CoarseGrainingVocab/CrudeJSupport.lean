import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
import SubdiffusiveProcess.CoarseGrainingVocab.Defect

/-!
# Support for the crude normalized-response seed

This module records the finite-volume order consequences available before the
small-disorder moment and homogenized lower-bound layers.  The proof-role split
mirrors the deterministic-bound and annealed-normalization stages of
`Algsuperdiff/Section3/Provider/Base/CutoffCoarseNormBounds.lean` and
`Algsuperdiff/Section3/Provider/Base/BaseCaseMStarStarError.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book
open scoped MatrixOrder

noncomputable section

private theorem randomAMatrix_diagonal_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (i : Fin d) :
    0 ≤ randomAMatrix M L U ω i i := by
  let hdata := aCutoffCoeffOnData M L ω U
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdata.toCoeffOn hdata.isSymmetric
  have hpsd : (randomAMatrix M L U ω).PosSemidef := by
    change (aMatrix U hdata.toCoeffOn).PosSemidef
    change (Ch02.aCoarse U hdata.toCoeffOn).PosSemidef
    rw [hTheory.derived_matrices.1, ← hTheory.derived_matrices.2.2]
    exact Ch02.bCoarse_posSemidef U hdata.toCoeffOn
  exact hpsd.diag_nonneg

private theorem randomAMatrix_diagonal_le_average {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (i : Fin d) :
    randomAMatrix M L U ω i i ≤
      Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) := by
  let hdata := aCutoffCoeffOnData M L ω U
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdata.toCoeffOn hdata.isSymmetric
  have hUpper := hTheory.dirichlet_neumann_bracketing.2.2 (Pi.single i 1)
  have hquad (A : Mat d) :
      vecDot (Pi.single i 1) (matVecMul A (Pi.single i 1)) = A i i := by
    unfold vecDot matVecMul
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, one_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _hj hji
        simp [hji]
      · simp
    · intro j _hj hji
      simp [Pi.single_apply, hji]
    · simp
  have hAverageApply :
      Ch02.averageMat U hdata.toCoeffOn.toCoeffField i i =
        Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) := by
    simp [Ch02.averageMat, hdata, ScalarCoeffOnData.toCoeffOn,
      scalarCoeffField, Homogenization.scalarMatrix]
  change Ch02.aCoarse U hdata.toCoeffOn i i ≤ _
  rw [hTheory.derived_matrices.1]
  rw [hquad, hquad, hAverageApply] at hUpper
  linarith

private theorem integrable_randomAMatrix_diagonal {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (i : Fin d) :
    Integrable (fun ω => randomAMatrix M L U ω i i) M.P.toMeasure :=
  ((integrable_randomAMatrix M L U).eval i).eval i

/-- Every finite-volume scalar annealed readout is nonnegative. -/
theorem abarScalarReadout_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m n : ℕ) :
    0 ≤ abarScalarReadout M m n := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hdiag : ∀ i : Fin d, 0 ≤
      abar M m (Ch02.cubeDomain (originCube d (n : ℤ))) i i := by
    intro i
    rw [abar, Homogenization.integral_matrix_apply
      (integrable_randomAMatrix M m (Ch02.cubeDomain (originCube d (n : ℤ)))) i i]
    exact integral_nonneg fun ω =>
      randomAMatrix_diagonal_nonneg M m
        (Ch02.cubeDomain (originCube d (n : ℤ))) ω i
  unfold abarScalarReadout Matrix.trace
  exact div_nonneg (Finset.sum_nonneg fun i _ => hdiag i) hd.le

/-- Every finite-volume scalar annealed readout is at most one. -/
theorem abarScalarReadout_le_one {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m n : ℕ) :
    abarScalarReadout M m n ≤ 1 := by
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  have hd : 0 < (d : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have hdiag : ∀ i : Fin d, abar M m U i i ≤ 1 := by
    intro i
    rw [abar, Homogenization.integral_matrix_apply (integrable_randomAMatrix M m U) i i]
    calc
      ∫ ω, randomAMatrix M m U ω i i ∂M.P.toMeasure ≤
          ∫ ω, Ch02.average U
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m ω) ∂M.P.toMeasure := by
        exact integral_mono
          (integrable_randomAMatrix_diagonal M m U i)
          (integrable_aCutoff_average M m U)
          (fun ω => randomAMatrix_diagonal_le_average M m U ω i)
      _ = 1 := integral_aCutoff_average M m U
  unfold abarScalarReadout Matrix.trace
  apply (div_le_iff₀ hd).2
  calc
    ∑ i, abar M m U i i ≤ ∑ _i : Fin d, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => hdiag i
    _ = (d : ℝ) := by simp
    _ = 1 * (d : ℝ) := by ring

/-- The infinite-volume scalar readout is nonnegative. -/
theorem ahom_nonneg {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) :
    0 ≤ ahom M m := by
  unfold ahom
  apply le_csInf
  · exact Set.range_nonempty _
  · rintro x ⟨n, rfl⟩
    exact abarScalarReadout_nonneg M m n

/-- The infinite-volume scalar readout is at most one. -/
theorem ahom_le_one {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) :
    ahom M m ≤ 1 := by
  unfold ahom
  have hbdd : BddBelow (Set.range (abarScalarReadout M m)) :=
    ⟨0, by rintro x ⟨n, rfl⟩; exact abarScalarReadout_nonneg M m n⟩
  exact (csInf_le hbdd ⟨0, rfl⟩).trans (abarScalarReadout_le_one M m 0)

/-- A zero scalar normalizer makes every normalized response probe vanish. -/
theorem paperScalarProbeMaxOn_zero {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) :
    paperScalarProbeMaxOn U a 0 = 0 := by
  have hJ : J U a 0 0 = 0 := by
    change Ch02.responseJ U a 0 0 = 0
    rw [Ch02.responseJ_zero_q_eq_sigmaStarInvCoarse]
    simp [vecDot, matVecMul]
  simp [paperScalarProbeMaxOn, hJ]

end

end SubdiffusiveProcess.CoarseGrainingVocab
