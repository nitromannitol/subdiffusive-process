module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.SandwichNondegeneracyAttainment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Windows

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/OneStepBoundaryComposeGlue.lean
-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/OneStepTriangle.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/OneStepBoundaryComposeGlue.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/OneStepTriangle.lean

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass

open MeasureTheory
open Homogenization (Vec vecDot openCubeSet originCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-- **The affine minimum is attained on a truncated window.**  The window shape
of `Section6Iteration.exists_isAffineMinimizer_of_axisCubeSandwich`. -/
theorem exists_isAffineMinimizer_truncatedWindow {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m k))) :
    ∃ (c : ℝ) (g : Vec d), IsAffineMinimizer (truncatedWindow x m k) u c g := by
  obtain ⟨zin, zout, hin, hout⟩ := exists_axisCube_sandwich_truncatedCube x hx hkm
  exact exists_isAffineMinimizer_of_axisCubeSandwich (zpow_pos (by norm_num) (k - 2))
    (zpow_pos (by norm_num) k) (measurableSet_truncatedWindow x m k) hin hout u hu

/-- **`hmin` at consumption.**  On the truncated window the affine minimum is
attained, in the `(c − A·x, A)` parametrization the boundary producers print. -/
theorem exists_isAffineMinimizer_shifted_truncatedWindow {m k : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) {V : Vec d → ℝ}
    (hV : MemLp V 2 (volume.restrict (truncatedWindow x m k))) :
    ∃ (c : ℝ) (A : Vec d),
      IsAffineMinimizer (truncatedWindow x m k) V (c - vecDot A x) A := by
  obtain ⟨c₀, g, hmin⟩ := exists_isAffineMinimizer_truncatedWindow hx hkm hV
  refine ⟨c₀ + vecDot g x, g, ?_⟩
  have hc : c₀ + vecDot g x - vecDot g x = c₀ := by ring
  rw [hc]
  exact hmin

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass
