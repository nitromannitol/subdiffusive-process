import SubdiffusiveProcess.CoarseGrainingVocab.Induction

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-!
# Finite and infinite scale recursion

This is the order-theoretic shell of the two block inductions.  It mirrors the
finite-corridor/union split in Algsuperdiff's
`IterateAssembly.lean` and `UnionCompletion.lean`; all probability estimates
enter only through the explicit pointwise norm bounds.
-/

private abbrev defectNorm {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (ξ : ℝ) (m : ℕ) : ℝ≥0∞ :=
  paperENNRealLpNorm M.P.toMeasure ξ
    (normalizedDefect M m
      (Homogenization.Book.Ch02.cubeDomain
        (Homogenization.originCube d (m : ℤ))))

/-- Assemble the finite induction predicate from scale-by-scale estimates. -/
theorem inductionHypothesis_of_scale_bounds {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m0 : ℕ) {ξ δ1 : ℝ}
    (hξ : 1 ≤ ξ) (hδ1 : 0 < δ1) (hδ1' : δ1 < 1)
    (hscale : ∀ m : ℕ, m ≤ m0 → defectNorm M ξ m ≤ ENNReal.ofReal δ1) :
    inductionHypothesis M m0 ξ δ1 := by
  refine ⟨hξ, hδ1, hδ1', iSup_le fun m => ?_⟩
  exact hscale m (by omega)

/-- A finite induction hypothesis supplies its estimate at every included
scale. -/
theorem inductionHypothesis_scale_bound {d : ℕ}
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {m0 : ℕ} {ξ δ1 : ℝ}
    (hS : inductionHypothesis M m0 ξ δ1) {m : ℕ} (hm : m ≤ m0) :
    defectNorm M ξ m ≤ ENNReal.ofReal δ1 := by
  rcases hS with ⟨_, _, _, hsup⟩
  let i : Fin (m0 + 1) := ⟨m, by omega⟩
  exact (le_iSup (fun j : Fin (m0 + 1) => defectNorm M ξ j) i).trans hsup



theorem inductionHypothesis_extend {d : ℕ}
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {m0 h : ℕ} {ξ δ1 : ℝ}
    (hS : inductionHypothesis M m0 ξ δ1)
    (hnew : ∀ r : ℕ, m0 < r → r ≤ m0 + h →
      defectNorm M ξ r ≤ ENNReal.ofReal δ1) :
    inductionHypothesis M (m0 + h) ξ δ1 := by
  refine inductionHypothesis_of_scale_bounds M (m0 + h) hS.1 hS.2.1 hS.2.2.1 ?_
  intro r hr
  by_cases hrold : r ≤ m0
  · exact inductionHypothesis_scale_bound hS hrold
  · exact hnew r (by omega) hr

/-- Assemble the infinite induction predicate from estimates at all scales. -/
theorem inductionHypothesisInfinity_of_scale_bounds {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {ξ δ1 : ℝ}
    (hξ : 1 ≤ ξ) (hδ1 : 0 < δ1) (hδ1' : δ1 < 1)
    (hscale : ∀ m : ℕ, defectNorm M ξ m ≤ ENNReal.ofReal δ1) :
    inductionHypothesisInfinity M ξ δ1 := by
  exact ⟨hξ, hδ1, hδ1', iSup_le hscale⟩

/-- Uniform finite induction hypotheses imply the infinite one. -/
theorem inductionHypothesisInfinity_of_finite {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {ξ δ1 : ℝ}
    (hfinite : ∀ m0 : ℕ, inductionHypothesis M m0 ξ δ1) :
    inductionHypothesisInfinity M ξ δ1 := by
  have hzero := hfinite 0
  refine inductionHypothesisInfinity_of_scale_bounds M hzero.1 hzero.2.1 hzero.2.2.1 ?_
  intro m
  exact inductionHypothesis_scale_bound (hfinite m) le_rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
