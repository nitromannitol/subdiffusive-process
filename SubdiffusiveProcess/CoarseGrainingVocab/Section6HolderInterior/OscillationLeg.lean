module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CampanatoFamily
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OffGridOscillation

@[expose] public section

/-!
# The oscillation leg: off-grid window to base-grid family window

This is the paper's Step 6 transfer : fix
`x ∈ cu_{m-1}`, take `y = x`, let `z` be a nearest scale-`j` grid point, so
`|x - z|_infty ≤ 3^j / 2` and `x + cu_j ⊆ U_{m,j+1}(z)`.  The oscillation datum
on the off-grid window then transfers to the grid window by **set inclusion at a
fixed volume-ratio price** — no cover, no mean-difference chaining, the
superset's own mean being used on both sides
(`normalizedL2On_sub_average_crossCentre_le`).

The point that unblocks row 2 is what the target window is.  `z` sits on the
scale-`j` grid and the window sits at scale `j + 1`; the **printed Campanato
family** (`exists_interiorCampanatoFamily`) bounds exactly that — base scale `j`
fixing the grid and stopping structure, window scale `j + 1 ≥ j` free above it.
The narrowed own-scale form used earlier (window scale forced equal to the grid
scale) is what made this look impossible; it is a specialization, not the printed
statement.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The off-grid oscillation transfer, with the grid centre produced.**

`z` lands on the scale-`j` grid — the *base* grid of the Campanato family — while
the window it carries is at scale `j + 1`.  The price is the dimension-only
factor `sqrt ((3 ^ 3) ^ d)`. -/
theorem exists_gridCentre_oscillation_le (d m j : ℕ) (x : Vec d)
    (hx : x ∈ cube d (m : ℤ)) (hjm : j ≤ m)
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) :
    ∃ z : Vec d, OnTriadicGrid j z ∧ z ∈ cube d (m : ℤ) ∧
      (∀ i : Fin d, |x i - z i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ j) ∧
      normalizedL2On (truncatedCube d (m : ℤ) (j : ℤ) x)
          (fun p ↦ u.toFun p -
            averageOn (truncatedCube d (m : ℤ) (j : ℤ) x) u.toFun) ≤
        Real.sqrt (((3 : ℝ) ^ (3 : ℤ)) ^ d) *
          normalizedL2On (truncatedCube d (m : ℤ) ((j : ℤ) + 1) z)
            (fun p ↦ u.toFun p -
              averageOn (truncatedCube d (m : ℤ) ((j : ℤ) + 1) z) u.toFun) := by
  obtain ⟨z, hzgrid, hzcube, hdist⟩ := Section6Holder.exists_holderGridCentre hx hjm
  refine ⟨z, hzgrid, hzcube, hdist, ?_⟩
  have hsub : truncatedCube d (m : ℤ) (j : ℤ) x ⊆
      truncatedCube d (m : ℤ) ((j : ℤ) + 1) z := by
    refine Section6Holder.truncatedCube_subset_succ_of_holderGridCentre
      (m := (m : ℤ)) (n := (j : ℤ)) (x := x) (z := z) ?_
    intro i
    have := hdist i
    simpa using this
  have hjm' : (j : ℤ) ≤ (m : ℤ) := by exact_mod_cast hjm
  have hraw := normalizedL2On_sub_average_crossCentre_le
    (m := (m : ℤ)) (j := (j : ℤ)) (ell := (j : ℤ) + 1)
    hx hzcube (by omega) (by omega) hsub u
  have hexp : ((j : ℤ) + 1) - (j : ℤ) + 2 = (3 : ℤ) := by ring
  rw [hexp] at hraw
  exact hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
