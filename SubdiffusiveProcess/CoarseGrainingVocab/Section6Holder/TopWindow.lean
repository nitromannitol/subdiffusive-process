import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.CampanatoFull
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.SandwichNondegeneracy
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Triangle

/-!
# Hölder Step 5: top-window oscillation

The iteration ends on a truncated window.  This module compares its
mean-zero normalized `L²` oscillation with the ambient cube oscillation,
paying only the explicit normalized-volume ratio.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

/-- The ambient cube divided by a scale-`j` truncated window has the same
dimension-only ratio used throughout the excess-decay geometry. -/
theorem cube_volume_div_truncatedCube_volume_le {d : ℕ} {m j : ℤ}
    {x : Vec d} (hx : x ∈ cube d m) (hjm : j - 1 ≤ m) :
    (volume (cube d m)).toReal /
        (volume (truncatedCube d m j x)).toReal ≤
      ((3 : ℝ) ^ (m - j + 2)) ^ d := by
  have hlo := (volume_toReal_truncatedCube_bounds x hx hjm).1
  have hden : 0 < ((3 : ℝ) ^ (j - 2)) ^ d := by positivity
  have hwindow : 0 < (volume (truncatedCube d m j x)).toReal :=
    hden.trans_le hlo
  have hcube : (volume (cube d m)).toReal = ((3 : ℝ) ^ m) ^ d := by
    rw [cube, volume_openCubeSet_toReal, cubeVolume,
      cubeScaleFactor_originCube]
  have hquot : ((3 : ℝ) ^ m) ^ d / ((3 : ℝ) ^ (j - 2)) ^ d =
      ((3 : ℝ) ^ (m - j + 2)) ^ d := by
    rw [← div_pow, ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 2
    ring
  rw [hcube, ← hquot, div_le_div_iff₀ hwindow hden]
  exact mul_le_mul_of_nonneg_left hlo (by positivity)

/-- Mean minimization followed by normalized-volume comparison transfers the
top iteration window to the global oscillation carrier. -/
theorem normalizedL2On_truncatedCube_sub_average_le_global
    {d : ℕ} {m j : ℤ} {x : Vec d}
    (hx : x ∈ cube d m) (hjm : j - 1 ≤ m)
    (u : H1Function (openCubeSet (originCube d m))) :
    normalizedL2On (truncatedCube d m j x)
        (fun z ↦ u.toFun z - averageOn (truncatedCube d m j x) u.toFun) ≤
      Real.sqrt (((3 : ℝ) ^ (m - j + 2)) ^ d) *
        normalizedL2On (cube d m)
          (fun z ↦ u.toFun z - averageOn (cube d m) u.toFun) := by
  let W := truncatedCube d m j x
  let Q := cube d m
  have hWm : MeasurableSet W := measurableSet_truncatedCube d m j x
  have hWpos : 0 < (volume W).toReal := volume_toReal_truncatedCube_pos x hx hjm
  have hWfin : volume W ≠ ⊤ := (volume_truncatedCube_lt_top d m j x).ne
  have hQpos : 0 < (volume Q).toReal := by
    dsimp only [Q]
    rw [cube, volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d m)
  have huW : MemLp u.toFun 2 (volume.restrict W) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedCube_subset_cube d m j x) le_rfl)
  have hmean : normalizedL2On W (fun z ↦ u.toFun z - volumeAverage W u.toFun) ≤
      normalizedL2On W (fun z ↦ u.toFun z - volumeAverage Q u.toFun) := by
    apply Section6Iteration.normalizedL2On_sub_volumeAverage_le hWm hWpos hWfin
    · exact integrableOn_truncatedCube x huW
    · exact huW.integrable_sq
  have hglobalMem : MemLp (fun z ↦ u.toFun z - volumeAverage Q u.toFun) 2
      (volume.restrict Q) := u.memL2.sub (memLp_const _)
  have hsubset := Section6Iteration.normalizedL2On_le_of_subset
    (truncatedCube_subset_cube d m j x) hQpos hWpos hglobalMem.integrable_sq
  have hratio := Real.sqrt_le_sqrt
    (cube_volume_div_truncatedCube_volume_le hx hjm)
  have hnorm0 : 0 ≤ normalizedL2On Q
      (fun z ↦ u.toFun z - volumeAverage Q u.toFun) :=
    Section6Iteration.normalizedL2On_nonneg _ _
  calc
    normalizedL2On W (fun z ↦ u.toFun z - averageOn W u.toFun) ≤
        normalizedL2On W (fun z ↦ u.toFun z - averageOn Q u.toFun) := hmean
    _ ≤ Real.sqrt ((volume Q).toReal / (volume W).toReal) *
        normalizedL2On Q (fun z ↦ u.toFun z - averageOn Q u.toFun) := hsubset
    _ ≤ Real.sqrt (((3 : ℝ) ^ (m - j + 2)) ^ d) *
        normalizedL2On Q (fun z ↦ u.toFun z - averageOn Q u.toFun) :=
      mul_le_mul_of_nonneg_right hratio hnorm0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
