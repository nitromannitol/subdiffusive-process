import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.IntermediateCampanatoRow
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.Restriction

/-!
# Theta ladder: restriction adapter for an intermediate row
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- Restrict a parent Sobolev solution to the moving comparison top before
invoking an intermediate stopped row. -/
theorem intermediateCampanatoRow_restrict
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {L ell top : ℕ}
    {z q : Vec d} {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    {theta : Vec d → ℝ} {K : ℝ}
    (hpath : ∀ u : H1Function (translatedCube d (top : ℤ) (z + q)),
      IsWeaklyHarmonicOn
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
          (translatedCube d (top : ℤ) (z + q)) u →
      normalizedL2On (translatedCube d (ell : ℤ) (z + q))
          (fun x ↦ u.toFun x - averageOn
            (translatedCube d (ell : ℤ) (z + q)) u.toFun) ≤
        K * normalizedL2On (translatedCube d (top : ℤ) (z + q))
          (fun x ↦ u.toFun x - averageOn
            (translatedCube d (top : ℤ) (z + q)) u.toFun))
    {W : Set (Vec d)} (hW : IsOpen W)
    (hsub : translatedCube d (top : ℤ) (z + q) ⊆ W)
    (u : H1Function W)
    (hu : IsWeaklyHarmonicOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x) W u) :
    normalizedL2On (translatedCube d (ell : ℤ) (z + q))
        (fun x ↦ u.toFun x - averageOn
          (translatedCube d (ell : ℤ) (z + q)) u.toFun) ≤
      K * normalizedL2On (translatedCube d (top : ℤ) (z + q))
        (fun x ↦ u.toFun x - averageOn
          (translatedCube d (top : ℤ) (z + q)) u.toFun) := by
  let uTop : H1Function (translatedCube d (top : ℤ) (z + q)) :=
    u.restrict (Section6CutoffRegularity.isOpen_translatedCube d _ _)
      hsub
  have huTop : IsWeaklyHarmonicOn
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * theta x)
      (translatedCube d (top : ℤ) (z + q)) uTop :=
    Section6BoundaryL2.isWeaklyHarmonicOn_restrict hW
      (Section6CutoffRegularity.isOpen_translatedCube d _ _)
      hsub hu
  simpa only [uTop, H1Function.restrict] using hpath uTop huTop

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
