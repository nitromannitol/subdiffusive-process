module

public import SubdiffusiveProcess.Section3.CrudeJBound

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem lemma_crude_J_bound_convex {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (xi : ℝ)
        (U : Ch02.Domain d),
        1 ≤ xi →
        (U : Set (Vec d)) ⊆
          Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ)) →
        paperENNRealLpNorm M.P.toMeasure xi (normalizedDefect M m U) ≤
          ENNReal.ofReal
            (C * xi * (m + 1 : ℝ) * M.delta ^ 2 *
              Real.exp (C * xi * (m + 1 : ℝ) * M.delta ^ 2)) :=
  _root_.SubdiffusiveProcess.Section3.crude_j_bound 

end SubdiffusiveProcess.Paper
