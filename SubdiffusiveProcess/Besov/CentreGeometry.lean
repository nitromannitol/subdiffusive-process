import SubdiffusiveProcess.Besov.SignedGridCenters
import SubdiffusiveProcess.Besov.ThreeIndexNorms
import Homogenization.Geometry.TriadicCubeTranslation
import Mathlib.Data.Set.Card

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped BigOperators ENNReal
noncomputable section
namespace SubdiffusiveProcess.Besov
attribute [local instance] Classical.propDecidable

/-- The negative-norm centre set is exactly the descendant-shift finset. -/
theorem negativeCentres_eq_signedGridCenters {d : ℕ} {m n : ℤ} (hnm : n ≤ m) :
    negativeCentres d m n = (signedGridCenters d n m : Set (Vec d)) := by
  ext z
  exact (mem_signedGridCenters_iff hnm).symm

/-- The positive centres lie in the next finer grid. -/
theorem positiveCentres_subset_signedGridCenters {d : ℕ} {m n : ℤ} (hnm : n ≤ m) :
    positiveCentres d m n ⊆ (signedGridCenters d (n - 1) m : Set (Vec d)) := by
  intro z hz
  exact (mem_signedGridCenters_iff (show n - 1 ≤ m by omega)).mpr ⟨hz.1, hz.2.1⟩

/-- Every positive-norm spatial averaging set is finite. -/
theorem positiveCentres_finite {d : ℕ} {m n : ℤ} (hnm : n ≤ m) :
    (positiveCentres d m n).Finite :=
  (signedGridCenters d (n - 1) m).finite_toSet.subset
    (positiveCentres_subset_signedGridCenters hnm)

/-- Every negative-norm spatial averaging set is finite. -/
theorem negativeCentres_finite {d : ℕ} {m n : ℤ} (hnm : n ≤ m) :
    (negativeCentres d m n).Finite := by
  rw [negativeCentres_eq_signedGridCenters hnm]
  exact Finset.finite_toSet _

/-- Cardinality cost of replacing a partition by the overlapping centre family. -/
theorem positiveCentres_ncard_le {d : ℕ} {m n : ℤ} (hnm : n ≤ m) :
    (positiveCentres d m n).ncard ≤
      3 ^ d * (descendantsAtScale (originCube d m) n).card := by
  have hsub := Set.ncard_le_ncard (positiveCentres_subset_signedGridCenters hnm)
    (signedGridCenters d (n - 1) m).finite_toSet
  rw [Set.ncard_coe_finset, signedGridCenters_card (show n - 1 ≤ m by omega)] at hsub
  have heq : (m - (n - 1)).toNat = (m - n).toNat + 1 := by omega
  rw [heq, Nat.mul_add, Nat.mul_one, pow_add] at hsub
  rw [descendantsAtScale_eq_descendantsAtDepth _ hnm, descendantsAtDepth_card]
  simpa only [originCube, pow_mul, Nat.mul_comm] using hsub

/-- A shifted paper cube agrees with its open triadic realization. -/
theorem translatedCube_shift_eq {d : ℕ} (R : TriadicCube d) :
    translatedCube d R.scale (triadicCubeShift R) = openCubeSet R := by
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube]
  unfold translatedCube cube
  rw [show (fun x : Vec d => triadicCubeShift R + x) =
      (fun x => x + triadicCubeShift R) by funext x; exact add_comm _ _]
  exact image_addRight_eq_translateSet _ _

/-- Partition-cube centres occur among the overlapping positive centres. -/
theorem descendant_shift_mem_positiveCentres {d : ℕ} {m n : ℤ}
    (hnm : n ≤ m) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d m) n) :
    triadicCubeShift R ∈ positiveCentres d m n := by
  have hscale := Homogenization.scale_eq_of_mem_descendantsAtScale hR
  refine ⟨?_, signed_shift_mem_cube hnm hR, ?_⟩
  · intro i
    refine ⟨3 * R.index i, ?_⟩
    simp only [triadicCubeShift, cubeScaleFactor, hscale, Int.cast_mul, Int.cast_ofNat]
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring
  · rw [← hscale, translatedCube_shift_eq]
    exact openCubeSet_subset_of_mem_descendantsAtScale hnm hR

end SubdiffusiveProcess.Besov
