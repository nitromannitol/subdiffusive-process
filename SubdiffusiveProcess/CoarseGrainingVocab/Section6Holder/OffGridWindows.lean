import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GridCenters
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows

/-!
# Hölder Step 7: off-grid window geometry

The stopped estimates are available at scale-`n` triadic grid centres, while
the frozen excess clause is stated at an arbitrary centre.  This file chooses
the descendant cube containing the arbitrary centre and records the three
nested windows used in Step 7 of the manuscript.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every point of `cube m` has a scale-`n` triadic grid centre at coordinate
distance at most `3^n / 2`.  The centre is the shift of the unique half-open
descendant containing the point. -/
theorem exists_holderGridCentre {d m n : ℕ} {x : Vec d}
    (hx : x ∈ cube d m) (hnm : n ≤ m) :
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
      ∀ i : Fin d, |x i - z i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
  have hxClosed : x ∈ cubeSet (originCube d (m : ℤ)) := by
    intro i
    have hi := hx i
    exact ⟨hi.1.le, hi.2⟩
  obtain ⟨R, hR, hxR⟩ :=
    exists_mem_descendantsAtDepth_of_mem_cubeSet (m - n) hxClosed
  have hscale : R.scale = (n : ℤ) := by
    rw [scale_eq_sub_of_mem_descendantsAtDepth hR]
    simp only [originCube]
    omega
  let z : Vec d := triadicCubeShift R
  have hzgrid : OnTriadicGrid n z := by
    simpa only [z] using onTriadicGrid_triadicCubeShift_of_scale hscale
  have hRscale : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ) := by
    have hnscale : (n : ℤ) ≤ (originCube d (m : ℤ)).scale := by
      change (n : ℤ) ≤ (m : ℤ)
      exact_mod_cast hnm
    rw [descendantsAtScale_eq_descendantsAtDepth _ hnscale]
    change R ∈ descendantsAtDepth (originCube d (m : ℤ))
      (Int.toNat ((m : ℤ) - (n : ℤ)))
    have hdepth : Int.toNat ((m : ℤ) - (n : ℤ)) = m - n := by
      omega
    rw [hdepth]
    exact hR
  have hzmem : z ∈ Section6Stopping.gridCentersInCube d n m := by
    exact Finset.mem_image.mpr ⟨R, hRscale, rfl⟩
  have hz := (Section6Stopping.mem_gridCentersInCube_iff hnm).mp hzmem
  refine ⟨z, hzgrid, hz.2, ?_⟩
  intro i
  have hi := hxR i
  have hpow : 0 < (3 : ℝ) ^ n := pow_pos (by norm_num) n
  have hfactor : cubeScaleFactor R = (3 : ℝ) ^ n := by
    simp only [cubeScaleFactor, hscale, zpow_natCast]
  have hzcoord : z i = (R.index i : ℝ) * (3 : ℝ) ^ n := by
    simp only [z, triadicCubeShift, hfactor]
  rw [hzcoord, abs_le]
  rw [hfactor] at hi
  constructor <;> nlinarith only [hi.1, hi.2, hpow]

/-- A scale-`n` window at an arbitrary centre is contained in the scale-`n+1`
window at any grid centre within half a scale. -/
theorem truncatedCube_subset_succ_of_holderGridCentre
    {d : ℕ} {m n : ℤ} {x z : Vec d}
    (hdist : ∀ i : Fin d, |x i - z i| ≤
      (1 / 2 : ℝ) * (3 : ℝ) ^ n) :
    truncatedCube d m n x ⊆ truncatedCube d m (n + 1) z := by
  intro p hp
  refine ⟨?_, hp.2⟩
  rw [mem_translatedCube_iff, cube, mem_openCubeSet_originCube_iff]
  intro i
  have hpx := (mem_openCubeSet_originCube_iff.mp
    (mem_translatedCube_iff.mp hp.1)) i
  have hxz := abs_le.mp (hdist i)
  have hpow : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hstep : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by
    rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  simp only [Pi.sub_apply] at hpx ⊢
  rw [hstep]
  constructor <;> nlinarith only [hpx.1, hpx.2, hxz.1, hxz.2, hpow]

/-- Conversely, once `n < ell`, the scale-`ell-1` window at the selected
grid centre is contained in the scale-`ell` window at the original centre. -/
theorem truncatedCube_pred_subset_of_holderGridCentre
    {d : ℕ} {m n ell : ℤ} {x z : Vec d}
    (hnell : n < ell)
    (hdist : ∀ i : Fin d, |x i - z i| ≤
      (1 / 2 : ℝ) * (3 : ℝ) ^ n) :
    truncatedCube d m (ell - 1) z ⊆ truncatedCube d m ell x := by
  intro p hp
  refine ⟨?_, hp.2⟩
  rw [mem_translatedCube_iff, cube, mem_openCubeSet_originCube_iff]
  intro i
  have hpz := (mem_openCubeSet_originCube_iff.mp
    (mem_translatedCube_iff.mp hp.1)) i
  have hxz := abs_le.mp (hdist i)
  have hpowN : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hpowMono : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (ell - 1) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hstep : (3 : ℝ) ^ ell = 3 * (3 : ℝ) ^ (ell - 1) := by
    calc
      (3 : ℝ) ^ ell = (3 : ℝ) ^ (ell - 1 + 1) := by
        congr 1
        ring
      _ = (3 : ℝ) ^ (ell - 1) * 3 :=
        zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0) (ell - 1)
      _ = 3 * (3 : ℝ) ^ (ell - 1) := by ring
  simp only [Pi.sub_apply] at hpz ⊢
  rw [hstep]
  constructor <;>
    nlinarith only [hpz.1, hpz.2, hxz.1, hxz.2, hpowN, hpowMono]

/-- The exact three-window sandwich used in Step 7. -/
theorem exists_holderOffGridWindowSandwich {d m n ell : ℕ} {x : Vec d}
    (hx : x ∈ cube d m) (hnm : n ≤ m) (hnell : n + 2 < ell) :
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
      truncatedCube d m n x ⊆ truncatedCube d m (n + 1) z ∧
      truncatedCube d m (n + 1) z ⊆ truncatedCube d m (ell - 1) z ∧
      truncatedCube d m (ell - 1) z ⊆ truncatedCube d m ell x := by
  obtain ⟨z, hzgrid, hzmem, hdist⟩ := exists_holderGridCentre hx hnm
  refine ⟨z, hzgrid, hzmem, ?_, ?_, ?_⟩
  · exact truncatedCube_subset_succ_of_holderGridCentre hdist
  · apply truncatedCube_mono d (m : ℤ) z
    show (n : ℤ) + 1 ≤ (ell : ℤ) - 1
    omega
  · exact truncatedCube_pred_subset_of_holderGridCentre
      (m := (m : ℤ)) (n := (n : ℤ)) (ell := (ell : ℤ)) (by omega) hdist

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
