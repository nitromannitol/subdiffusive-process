import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseMeasureTheory

/-!
# Pathwise entry bounds for the finite-cutoff coarse matrices

Step 1 of the §44 programme needs a pathwise bound on the coarse matrices of a
single realization of `a_L`.  The bound is the *trivial-competitor* variational
fact: the Dirichlet coarse matrix is dominated by the spatial average of the
coefficient, and dually the inverse Neumann matrix is dominated by the average
of the reciprocal.  Both are immediate from the Chapter 2 bracketing

    `(averagedSymmPartInv U a)⁻¹ ≤ sigmaStarCoarse U a ≤ sigmaCoarse U a
        ≤ averageMat U a`

(`Ch02.ResponseSymmetricDirichletNeumannTheory.dirichlet_neumann_bracketing`).

These facts are already proved in
`Section4Recursion/ResponseMeasureTheory.lean` — but as `private theorem`s
(`abs_randomAMatrix_entry_le_average` at `:296`,
`abs_randomAStarInv_entry_le_inverse_average` at `:547`, and the scalar identity
`averagedSymmPartInv_aCutoff_eq_scalar` at `:481`), hence unusable from another
module.  This file re-establishes them publicly, by the same proofs, so that the
moment bound of the next module can use them.

No new mathematics; no `DRAFT_SORRY` conclusion is used.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The averaged symmetric-part inverse of the scalar cutoff is the scalar
matrix of the reciprocal average. -/
theorem averagedSymmPartInv_aCutoff_eq_scalar' {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) :
    Ch02.averagedSymmPartInv U (aCutoffCoeffOnData M L omega U).toCoeffOn =
      Ch02.average U (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹) • (1 : Mat d) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d106_averagedSymmPartInv_aCutoff_eq_scalar (d := d) (M := M) (L := L) (U := U) (omega := omega)

/-- A continuous strictly positive function has positive volume average on a
Chapter 2 domain. -/
theorem volumeAverage_pos_of_continuous_pos' {d : ℕ}
    (U : Ch02.Domain d) {f : Vec d → ℝ} (hf : Continuous f)
    (hf_pos : ∀ x, 0 < f x) :
    0 < Homogenization.volumeAverage (U : Set (Vec d)) f := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d197_volumeAverage_pos_of_continuous_pos (d := d) (U := U) (f := f) (hf := hf) (hf_pos := hf_pos)

/-- **Trivial-competitor bound, primal side.**  Every entry of the finite-cutoff
coarse matrix is bounded by the spatial average of the coefficient. -/
theorem abs_randomAMatrix_entry_le_average' {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) (i j : Fin d) :
    |randomAMatrix M L U omega i j| ≤
      Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d134_abs_randomAMatrix_entry_le_average (d := d) (M := M) (L := L) (U := U) (omega := omega) (i := i) (j := j)

/-- **Trivial-competitor bound, dual side.**  Every entry of the inverse dual
coarse matrix is bounded by the spatial average of the reciprocal. -/
theorem abs_randomAStarInv_entry_le_inverse_average' {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) (i j : Fin d) :
    |(randomAStarMatrix M L U omega)⁻¹ i j| ≤
      Ch02.average U (fun x =>
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)⁻¹) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d118_abs_randomAStarInv_entry_le_inverse_average (d := d) (M := M) (L := L) (U := U) (omega := omega) (i := i) (j := j)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
