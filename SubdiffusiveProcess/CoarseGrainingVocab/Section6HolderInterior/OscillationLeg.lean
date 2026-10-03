module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CampanatoFamily
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OffGridOscillation

@[expose] public section




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
