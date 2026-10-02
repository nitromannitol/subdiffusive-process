import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyCoverRatio

/-!
# Row 2's left-hand side at an off-grid base point

The assembly: the scale-`j` grid windows cover `U_{m,j}(x)` a.e.
(`GridCover`), energies are additive over covers with the volume ratio
(`EnergyCoverRatio`), so a uniform energy bound at the *grid* windows — where
Step 6 and row 1 both apply, since the grid scale matches the window scale —
transfers to the off-grid base point with a dimension-only constant.

This discharges the geometric half of row 2's leg.  What is still required from
the caller is the uniform bound `N` at the grid neighbours, i.e. Step 6 and the
row-2 conversion instantiated there together with the good-centre selection.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **Row 2's left-hand side, transferred from the grid neighbours.**  A uniform
energy bound at the scale-`j` grid windows around `x` gives the bound at the
off-grid window `U_{m,j}(x)`, with the dimension-only factor
`√(card · 9^d)`. -/
theorem vectorNormalizedL2On_offGrid_le_of_gridNeighbours
    (d j m : ℕ) (x : Vec d) (f : Vec d → Vec d) {N : ℝ}
    (hjm : j ≤ m) (hx : x ∈ cube d (m : ℤ))
    (hint : ∀ y : Vec d, IntegrableOn
      (fun p => Homogenization.euclideanNorm (f p) ^ 2)
      (truncatedCube d (m : ℤ) (j : ℤ) y) volume)
    (hN : ∀ y ∈ gridNeighbours d j m x,
      vectorNormalizedL2On (truncatedCube d (m : ℤ) (j : ℤ) y) f ≤ N)
    (hN0 : 0 ≤ N) :
    vectorNormalizedL2On (truncatedCube d (m : ℤ) (j : ℤ) x) f ≤
      Real.sqrt (((gridNeighbours d j m x).card : ℝ) *
        ((3 : ℝ) ^ (2 : ℤ)) ^ d) * N := by
  have hj1m : (j : ℤ) - 1 ≤ (m : ℤ) := by
    have : (j : ℤ) ≤ (m : ℤ) := by exact_mod_cast hjm
    omega
  refine vectorNormalizedL2On_le_of_aecover_ratio
    (fun y => measurableSet_truncatedCube d (m : ℤ) (j : ℤ) y)
    hint
    (truncatedCube_aecover_gridNeighbours d j m x hjm)
    (volume_toReal_truncatedCube_pos x hx hj1m)
    (fun y _ => (volume_truncatedCube_lt_top d (m : ℤ) (j : ℤ) y).ne)
    ?_ (by positivity) hN hN0
  intro y hy
  have hycube : y ∈ cube d (m : ℤ) := by
    have hmem : y ∈ Section6Stopping.gridCentersInCube d j m := by
      rw [gridNeighbours, Finset.mem_filter] at hy
      exact hy.1
    exact ((Section6Stopping.mem_gridCentersInCube_iff hjm).mp hmem).2
  exact volume_truncatedCube_le_ratio hx hycube hj1m

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
