module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.OffGridWindows
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyCoverAE

@[expose] public section

/-!
# The concrete grid cover of an off-grid window

The scale-`j` grid windows meeting `U_{m,j}(x)` cover it **up to the grid box
faces**, which form a null set: the windows are open boxes, so a point sitting
exactly on a face belongs to none of them.

That is why the cover must be stated a.e. — which is exactly the form
`EnergyCoverAE` accepts.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The scale-`j` grid points whose windows can meet `U_{m,j}(x)`. -/
def gridNeighbours (d j m : ℕ) (x : Vec d) : Finset (Vec d) :=
  (Section6Stopping.gridCentersInCube d j m).filter
    (fun y => ∀ i : Fin d, |x i - y i| ≤ (3 : ℝ) ^ j)

/-- A coordinate hyperplane is null. -/
theorem volume_coord_hyperplane (d : ℕ) (i : Fin d) (c : ℝ) :
    volume {p : Vec d | p i = c} = 0 := by
  have hset : {p : Vec d | p i = c}
      = Set.univ.pi (fun k => if k = i then ({c} : Set ℝ) else Set.univ) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
    constructor
    · intro hp k
      by_cases hk : k = i
      · subst hk; simpa using hp
      · simp [hk]
    · intro hp
      have := hp i
      simpa using this
  rw [hset, volume_pi, Measure.pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp

/-- The union of the scale-`j` grid box faces. -/
def gridFaces (d j : ℕ) : Set (Vec d) :=
  ⋃ (i : Fin d), ⋃ (k : ℤ),
    {p : Vec d | p i = (3 : ℝ) ^ j * (k : ℝ) + (1 / 2 : ℝ) * (3 : ℝ) ^ j}

/-- **The faces are null.**  A countable union of coordinate hyperplanes. -/
theorem volume_gridFaces (d j : ℕ) : volume (gridFaces d j) = 0 := by
  unfold gridFaces
  refine measure_iUnion_null (fun i => measure_iUnion_null (fun k => ?_))
  exact volume_coord_hyperplane d i _

/-- **The a.e. grid cover.**  Off the faces, every point of `U_{m,j}(x)` lies in
the scale-`j` grid window of its own grid centre, and that centre is one of the
neighbours of `x`. -/
theorem truncatedCube_aecover_gridNeighbours (d j m : ℕ) (x : Vec d)
    (hjm : j ≤ m) :
    truncatedCube d (m : ℤ) (j : ℤ) x ≤ᵐ[volume]
      ⋃ y ∈ gridNeighbours d j m x, truncatedCube d (m : ℤ) (j : ℤ) y := by
  have hnull := volume_gridFaces d j
  have hae : ∀ᵐ p ∂(volume : Measure (Vec d)),
      p ∈ truncatedCube d (m : ℤ) (j : ℤ) x →
      p ∈ ⋃ y ∈ gridNeighbours d j m x, truncatedCube d (m : ℤ) (j : ℤ) y := by
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) hnull
    rw [Set.mem_setOf_eq, Classical.not_imp] at hp
    obtain ⟨hpW, hpU⟩ := hp
    by_contra hnf
    apply hpU
    have hpcube : p ∈ cube d (m : ℤ) :=
      truncatedCube_subset_cube d (m : ℤ) (j : ℤ) x hpW
    obtain ⟨y, hygrid, hycube, hdist⟩ :=
      Section6Holder.exists_holderGridCentre hpcube hjm
    -- strictness off the faces
    have hstrict : ∀ i : Fin d, |p i - y i| < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
      intro i
      rcases lt_or_eq_of_le (hdist i) with hlt | heq
      · exact hlt
      · exfalso
        apply hnf
        obtain ⟨k, hk⟩ := hygrid i
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        rcases abs_eq (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ j)
          |>.mp heq with hcase | hcase
        · refine Set.mem_iUnion.mpr ⟨k, ?_⟩
          simp only [Set.mem_setOf_eq]
          rw [hk] at hcase
          linarith [hcase]
        · refine Set.mem_iUnion.mpr ⟨k - 1, ?_⟩
          simp only [Set.mem_setOf_eq]
          rw [hk] at hcase
          push_cast
          linarith [hcase]
    -- the point lies in its own grid window
    have hmemY : p ∈ truncatedCube d (m : ℤ) (j : ℤ) y := by
      refine ⟨?_, hpcube⟩
      rw [mem_translatedCube_iff, cube, mem_openCubeSet_originCube_iff]
      intro i
      have hi := abs_lt.mp (hstrict i)
      simp only [Pi.sub_apply]
      have hz : (3 : ℝ) ^ ((j : ℤ)) = (3 : ℝ) ^ j := by
        rw [zpow_natCast]
      rw [hz]
      constructor <;> linarith [hi.1, hi.2]
    -- the centre is a neighbour of `x`
    have hnbr : y ∈ gridNeighbours d j m x := by
      rw [gridNeighbours, Finset.mem_filter]
      refine ⟨(Section6Stopping.mem_gridCentersInCube_iff hjm).mpr ⟨hygrid, hycube⟩,
        ?_⟩
      intro i
      have hxp : |x i - p i| < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
        have hmem := (mem_openCubeSet_originCube_iff.mp
          (mem_translatedCube_iff.mp hpW.1)) i
        simp only [Pi.sub_apply] at hmem
        have hz : (3 : ℝ) ^ ((j : ℤ)) = (3 : ℝ) ^ j := by rw [zpow_natCast]
        rw [hz] at hmem
        rw [abs_lt]
        constructor <;> linarith [hmem.1, hmem.2]
      have hpy := hstrict i
      have htri : |x i - y i| ≤ |x i - p i| + |p i - y i| :=
        abs_sub_le (x i) (p i) (y i)
      linarith [htri, hxp, hpy]
    exact Set.mem_biUnion hnbr hmemY
  exact hae

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
