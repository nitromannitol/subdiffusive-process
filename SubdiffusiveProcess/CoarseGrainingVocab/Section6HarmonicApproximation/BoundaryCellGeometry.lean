module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ProjectedDirichletEnergy
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliScaleZeroCore

@[expose] public section

/-!
# Geometry of the projected boundary cells

The scale-`n-4` cells in the printed `9^d` cover are read through the
Caccioppoli core of a well-placed scale-`n-2` cube.  This file records that
readout and proves that every such projected cube stays inside the ambient
scale-`n` truncated window.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03

noncomputable section

variable {d : ℕ}

/-- A truncated window two scales below the projected cube lies in its
Caccioppoli core after recentering. -/
theorem truncatedCube_subset_translate_caccioppoliCore {m k j : ℤ}
    (q : Vec d) (hkm : k ≤ m) (hjk : j ≤ k - 2) :
    truncatedCube d m j q ⊆
      translateSet (Section6ExcessDecay.wellPlacedCentre q m k)
        (caccioppoliCoreSet (originCube d k)
          (q - Section6ExcessDecay.wellPlacedCentre q m k)) := by
  intro p hp
  let c := Section6ExcessDecay.wellPlacedCentre q m k
  have hcube : p - c ∈ openCubeSet (originCube d k) := by
    have h := Section6ExcessDecay.truncatedCube_subset_translatedCube_wellPlacedCentre
      q hkm (by omega : j ≤ k) hp
    exact Section6ExcessDecay.mem_translatedCube_iff.mp h
  have hpq : p - q ∈ cube d j :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hp
  have hpatch : p - c ∈ openCubeAtScale (q - c) ((originCube d k).scale - 2) := by
    rw [show (originCube d k).scale = k by rfl,
      openCubeAtScale_eq_translateSet, mem_translateSet_iff_sub_mem]
    have heq : p - c - (q - c) = p - q := by abel
    rw [heq]
    simpa [cube, openCubeAtScale_zero_eq_openCubeSet_originCube] using
      Section6ExcessDecay.cube_subset_cube_of_le hjk hpq
  rw [mem_translateSet_iff_sub_mem]
  exact ⟨hcube, hpatch⟩

/-- If the cell centre lies in `U_(m,n-1)(x)`, its well-placed scale-`n-2`
cube lies in `U_(m,n)(x)`.  This is the printed three-radius estimate. -/
theorem translatedCube_wellPlacedCentre_subset_nextWindow_of_mem
    {m n : ℤ} {x q : Vec d}
    (hq : q ∈ truncatedCube d m (n - 1) x) (hnm : n - 2 ≤ m) :
    translatedCube d (n - 2)
        (Section6ExcessDecay.wellPlacedCentre q m (n - 2)) ⊆
      truncatedCube d m n x := by
  intro p hp
  have hpDomain : p ∈ cube d m :=
    Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube q hnm hp
  refine ⟨?_, hpDomain⟩
  have hpqWindow : p ∈ truncatedCube d m (n - 1) q :=
    Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_truncatedCube_pred
      (Section6ExcessDecay.truncatedCube_subset_cube d m (n - 1) x hq) hnm hp
  have hpq := Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hpqWindow
  have hqx := Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hq
  rw [Section6ExcessDecay.mem_translatedCube_iff]
  rw [cube, mem_openCubeSet_originCube_iff] at hpq hqx ⊢
  intro i
  have hpqi := hpq i
  have hqxi := hqx i
  simp only [Pi.sub_apply] at hpqi hqxi ⊢
  have hpow : (3 : ℝ) ^ (n - 1) * 3 = (3 : ℝ) ^ n := by
    rw [show n = n - 1 + 1 by ring, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  have hpos : 0 < (3 : ℝ) ^ (n - 1) := zpow_pos (by norm_num) _
  constructor <;> linarith only [hpqi.1, hpqi.2, hqxi.1, hqxi.2, hpow, hpos]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
