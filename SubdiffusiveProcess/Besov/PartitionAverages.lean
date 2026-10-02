import SubdiffusiveProcess.Besov.CubeNormBridge
import SubdiffusiveProcess.Besov.SpatialAggregation
import SubdiffusiveProcess.Besov.ScaleAggregation
import Mathlib.Data.Finset.Max

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped BigOperators ENNReal
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- Normalized spatial aggregation over a partition. -/
def depthAggregation {d : ℕ} (Q : TriadicCube d) (j : ℕ) (r : ℝ≥0∞)
    (a : TriadicCube d → ℝ≥0∞) : ℝ≥0∞ :=
  finiteAggregation (descendantsAtDepth Q j) ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ r a

/-- A child on which the absolute cell mean is largest. -/
def maximalChild {d : ℕ} (R : TriadicCube d) (f : Vec d → ℝ) : TriadicCube d :=
  Classical.choose ((childCubes R).exists_max_image (fun S => |cubeAverage S f|)
    (childCubes_nonempty R))

theorem maximalChild_mem {d : ℕ} (R : TriadicCube d) (f : Vec d → ℝ) :
    maximalChild R f ∈ childCubes R :=
  (Classical.choose_spec ((childCubes R).exists_max_image (fun S => |cubeAverage S f|)
    (childCubes_nonempty R))).1

theorem maximalChild_le {d : ℕ} (R S : TriadicCube d) (f : Vec d → ℝ)
    (hS : S ∈ childCubes R) : |cubeAverage S f| ≤ |cubeAverage (maximalChild R f) f| :=
  (Classical.choose_spec ((childCubes R).exists_max_image (fun S => |cubeAverage S f|)
    (childCubes_nonempty R))).2 S hS

theorem maximalChild_injective {d : ℕ} (f : Vec d → ℝ) :
    Function.Injective (fun R : TriadicCube d => maximalChild R f) := by
  intro R S h
  by_contra hRS
  have hd := Finset.disjoint_left.mp (disjoint_childCubes_of_ne hRS)
  have hs := maximalChild_mem S f
  change maximalChild R f = maximalChild S f at h
  rw [← h] at hs
  exact hd (maximalChild_mem R f) hs

/-- Selecting one child per parent loses at most the child count in spatial aggregation. -/
theorem maximalChild_depthAggregation_le {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (r : ℝ≥0∞) (hr : 1 ≤ r) (f : Vec d → ℝ) :
    depthAggregation Q j r (fun R => ENNReal.ofReal |cubeAverage (maximalChild R f) f|) ≤
      (3 ^ d : ℕ) * depthAggregation Q (j + 1) r (fun R => ENNReal.ofReal |cubeAverage R f|) := by
  classical
  apply finiteAggregation_sampling _ _ (descendantsAtDepth_nonempty Q j)
    (fun R => maximalChild R f) (maximalChild_injective f).injOn
  · intro R hR
    exact mem_descendantsAtDepth_succ_iff.mpr ⟨R, hR, maximalChild_mem R f⟩
  · exact Nat.one_le_pow d 3 (by omega)
  · rw [descendantsAtDepth_card_succ, Nat.mul_comm]
  · exact hr

/-- The signed descendant carrier at depth j. -/
theorem signedGridCenters_depth {d : ℕ} (m : ℤ) (j : ℕ) :
    signedGridCenters d (m - j) m =
      (descendantsAtDepth (originCube d m) j).image triadicCubeShift := by
  unfold signedGridCenters
  rw [descendantsAtScale_eq_descendantsAtDepth _ (show m - (j : ℤ) ≤ m by omega)]
  congr 2
  change (m - (m - (j : ℤ))).toNat = j
  omega

/-- The negative spatial average is exactly a partition average. -/
theorem negative_average_eq_depthAggregation {d : ℕ} (m : ℤ) (j : ℕ)
    (r : ℝ≥0∞) (f : Vec d → ℝ) :
    averageLr (negativeCentres d m (m - j)) r
      (fun z => ENNReal.ofReal |⨍ x in translatedCube d (m - j) z, f x|) =
      depthAggregation (originCube d m) j r (fun R => ENNReal.ofReal |cubeAverage R f|) := by
  classical
  have hnm : m - (j : ℤ) ≤ m := by omega
  have hfin := negativeCentres_finite (d := d) hnm
  have heq := negativeCentres_eq_signedGridCenters (d := d) hnm
  have hshift : Set.InjOn triadicCubeShift (↑(descendantsAtDepth (originCube d m) j) : Set (TriadicCube d)) := by
    have h := shift_injective_on_signed_descendants (d := d) (m := m) (n := m - j)
    rw [descendantsAtScale_eq_descendantsAtDepth _ hnm] at h
    have hdep : ((originCube d m).scale - (m - (j : ℤ))).toNat = j := by
      change (m - (m - (j : ℤ))).toNat = j
      omega
    rwa [hdep] at h
  have hfs : hfin.toFinset = (descendantsAtDepth (originCube d m) j).image triadicCubeShift := by
    ext z
    simp only [Set.Finite.mem_toFinset, heq, signedGridCenters_depth, Finset.mem_coe]
  have hc : (negativeCentres d m (m - j)).ncard =
      (descendantsAtDepth (originCube d m) j).card := by
    rw [heq, Set.ncard_coe_finset, signedGridCenters_depth,
      Finset.card_image_of_injOn hshift]
  rw [averageLr_eq_finiteAggregation _ hfin, hfs, hc, finiteAggregation_image _ _ hshift]
  unfold depthAggregation
  apply finiteAggregation_congr
  intro R hR
  have hscale : R.scale = m - j := by
    simpa only [originCube] using scale_eq_sub_of_mem_descendantsAtDepth hR
  rw [← hscale, translatedCube_shift_eq, openCube_average_eq]

/-- The partition oscillation norm is bounded by the source's overlapping average. -/
theorem positive_depthAggregation_le {d : ℕ} (m : ℤ) (j : ℕ)
    (r : ℝ≥0∞) (hr : 1 ≤ r) (g : Vec d → ℝ) :
    depthAggregation (originCube d m) j r
      (fun R => eLpNorm (cubeFluctuation R g) 1 (normalizedCubeMeasure R)) ≤
      (3 ^ d : ℕ) * averageLr (positiveCentres d m (m - j)) r
        (fun z => normalizedLp (translatedCube d (m - j) z) 1
          (fun x => g x - ⨍ y in translatedCube d (m - j) z, g y)) := by
  classical
  have hnm : m - (j : ℤ) ≤ m := by omega
  have hfin := positiveCentres_finite (d := d) hnm
  have hscaleSet : descendantsAtScale (originCube d m) (m - j) =
      descendantsAtDepth (originCube d m) j := by
    rw [descendantsAtScale_eq_descendantsAtDepth _ hnm]
    congr 1
    change (m - (m - (j : ℤ))).toNat = j
    omega
  have hshift : Set.InjOn triadicCubeShift (↑(descendantsAtDepth (originCube d m) j) : Set (TriadicCube d)) := by
    rw [← hscaleSet]
    exact shift_injective_on_signed_descendants
  rw [averageLr_eq_finiteAggregation _ hfin]
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have heq : depthAggregation (originCube d m) j r
      (fun R => eLpNorm (cubeFluctuation R g) 1 (normalizedCubeMeasure R)) =
      finiteAggregation (descendantsAtDepth (originCube d m) j)
        ((descendantsAtDepth (originCube d m) j).card : ℝ≥0∞)⁻¹ r
        (fun R => normalizedLp (translatedCube d (m - j) (triadicCubeShift R)) 1
          (fun x => g x - ⨍ y in translatedCube d (m - j) (triadicCubeShift R), g y)) := by
    apply finiteAggregation_congr
    intro R hR
    have hscale : R.scale = m - j := by
      simpa only [originCube] using scale_eq_sub_of_mem_descendantsAtDepth hR
    rw [← hscale, normalized_oscillation_shift_eq]
  rw [heq]
  apply finiteAggregation_sampling _ _ (descendantsAtDepth_nonempty _ j)
    triadicCubeShift hshift
  · intro R hR
    exact hfin.mem_toFinset.mpr (descendant_shift_mem_positiveCentres hnm (hscaleSet ▸ hR))
  · exact Nat.one_le_pow d 3 (by omega)
  · rw [← Set.ncard_eq_toFinset_card _ hfin]
    rw [← hscaleSet]
    exact positiveCentres_ncard_le hnm
  · exact hr

end SubdiffusiveProcess.Besov
