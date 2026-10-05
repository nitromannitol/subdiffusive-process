module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionCoefficientBounds

@[expose] public section

/-!
# Relative half-grid covers of stopping-cell enlargements

The stopping cells need not be centred on one global grid.  Around each cell
we therefore use the half-side-spaced grid translated to that cell's centre.
Its `7^d` nearby cells cover the centred threefold enlargement, including all
shared faces.

This is the deterministic localization required before the selected cells
are looked up in the stopping graph.  It deliberately proves a cover, not a
tiling statement.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

variable {d : ℕ}

/-- Centre of a half-grid cell relative to an arbitrary stopping-cell
centre. -/
def stoppingRelativeGridCentre (n : ℤ) (centre : Vec d)
    (k : Fin d → ℤ) : Vec d :=
  centre + gridCentre d n k

theorem mem_translatedCube_stoppingRelativeGridCentre_iff
    {n : ℤ} {centre x : Vec d} {k : Fin d → ℤ} :
    x ∈ translatedCube d n (stoppingRelativeGridCentre n centre k) ↔
      x - centre ∈ translatedCube d n (gridCentre d n k) := by
  rw [mem_translatedCube_iff, mem_translatedCube_iff]
  unfold stoppingRelativeGridCentre
  simp only [sub_add_eq_sub_sub]

theorem zero_gridCentre (d : ℕ) (n : ℤ) :
    gridCentre d n (0 : Fin d → ℤ) = 0 := by
  ext i
  simp [gridCentre]

/-- The centred enlargement of an arbitrary cell is covered by the `7^d`
relative half-grid cells at the original scale. -/
theorem translatedCube_succ_subset_stoppingRelativeGridNeighbours
    (d : ℕ) (n : ℤ) (centre : Vec d) :
    translatedCube d (n + 1) centre ⊆
      ⋃ k ∈ gridNeighbours d (0 : Fin d → ℤ),
        translatedCube d n (stoppingRelativeGridCentre n centre k) := by
  intro x hx
  have hx0 : x - centre ∈
      translatedCube d (n + 1) (gridCentre d n (0 : Fin d → ℤ)) := by
    rw [zero_gridCentre, mem_translatedCube_iff]
    simpa only [sub_zero] using (mem_translatedCube_iff.mp hx)
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp
    (translatedCube_succ_subset_gridNeighbours d n (0 : Fin d → ℤ) hx0)
  exact Set.mem_iUnion₂.mpr
    ⟨k, hk, mem_translatedCube_stoppingRelativeGridCentre_iff.mpr hxk⟩

/-- The relative neighbour family has the same dimension-only cardinal bound
as the unshifted half grid. -/
theorem card_stoppingRelativeGridNeighbours (d : ℕ) (n : ℤ)
    (centre : Vec d) :
    ((gridNeighbours d (0 : Fin d → ℤ)).image
      (stoppingRelativeGridCentre n centre)).card ≤ 7 ^ d := by
  exact Finset.card_image_le.trans_eq (card_gridNeighbours d 0)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
