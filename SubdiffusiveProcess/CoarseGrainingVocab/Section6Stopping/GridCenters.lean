import SubdiffusiveProcess.CoarseGrainingVocab.Section6AnnularCarrier
import Homogenization.Geometry.CubeColoring

/-!
# Finite carrier for section 6 triadic-grid centres

The manuscript repeatedly takes a maximum over the literal set
`3^n ℤ^d ∩ □_m`.  This file identifies that set with the shifts of the
scale-`n` descendants of the centered scale-`m` cube.  In particular it gives
the exact dimension-only cardinality used by both stopping-time arguments.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The finite family of literal scale-`n` grid centres in the centered
scale-`m` cube, represented by descendant-cube shifts. -/
def gridCentersInCube (d n m : ℕ) : Finset (Vec d) :=
  (descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).image triadicCubeShift

private theorem triadicCubeShift_eq_of_mem_cubeSet_of_onTriadicGrid
    {d n : ℕ} {R : TriadicCube d} (hscale : R.scale = (n : ℤ))
    {z : Vec d} (hzR : z ∈ cubeSet R) (hzgrid : OnTriadicGrid n z) :
    triadicCubeShift R = z := by
  funext i
  obtain ⟨k, hk⟩ := hzgrid i
  have hfactor : cubeScaleFactor R = (3 : ℝ) ^ n := by
    simp [cubeScaleFactor, hscale]
  have hfactor_pos : 0 < (3 : ℝ) ^ n := pow_pos (by norm_num) _
  have hlo := (hzR i).1
  have hhi := (hzR i).2
  rw [hfactor, hk] at hlo hhi
  have hlo' : (R.index i : ℝ) - 1 / 2 ≤ (k : ℝ) := by
    nlinarith
  have hhi' : (k : ℝ) < (R.index i : ℝ) + 1 / 2 := by
    nlinarith
  have hRk : R.index i ≤ k := by
    by_contra h
    have hkR : k + 1 ≤ R.index i := by omega
    have hkR' : (k : ℝ) + 1 ≤ (R.index i : ℝ) := by exact_mod_cast hkR
    linarith
  have hkR : k ≤ R.index i := by
    by_contra h
    have hRk' : R.index i + 1 ≤ k := by omega
    have hRk'' : (R.index i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hRk'
    linarith
  have hk_eq : k = R.index i := le_antisymm hkR hRk
  simp only [triadicCubeShift, hfactor, hk, hk_eq]
  ring

/-- Membership in the finite descendant-shift carrier is exactly membership
in the manuscript's literal grid intersection. -/
theorem mem_gridCentersInCube_iff {d n m : ℕ} (hnm : n ≤ m) {z : Vec d} :
    z ∈ gridCentersInCube d n m ↔ OnTriadicGrid n z ∧ z ∈ cube d m := by
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨R, hR, rfl⟩
    refine ⟨onTriadicGrid_triadicCubeShift_of_scale
      (Homogenization.scale_eq_of_mem_descendantsAtScale hR), ?_⟩
    exact triadicCubeShift_mem_cube_of_mem_descendantsAtScale
      (by exact_mod_cast hnm) hR
  · rintro ⟨hzgrid, hzmem⟩
    have hzmem' : z ∈ cubeSet (originCube d (m : ℤ)) := by
      intro i
      have hi := hzmem i
      exact ⟨hi.1.le, hi.2⟩
    obtain ⟨R, hR, hzR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet
      (m - n) hzmem'
    have hdepth : Int.toNat ((m : ℤ) - (n : ℤ)) = m - n := by
      rw [Int.toNat_sub']
      simp
    have hRscale : R.scale = (n : ℤ) := by
      have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
      simp only [originCube] at hscale
      rw [hscale]
      omega
    have hR' : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ) := by
      have hk : (n : ℤ) ≤ (originCube d (m : ℤ)).scale := by
        change (n : ℤ) ≤ (m : ℤ)
        exact_mod_cast hnm
      rw [descendantsAtScale_eq_descendantsAtDepth _ hk]
      change R ∈ descendantsAtDepth (originCube d (m : ℤ))
        (Int.toNat ((m : ℤ) - (n : ℤ)))
      rw [hdepth]
      exact hR
    refine Finset.mem_image.mpr ⟨R, hR', ?_⟩
    exact triadicCubeShift_eq_of_mem_cubeSet_of_onTriadicGrid hRscale hzR hzgrid

/-- Descendant-cube shifts are injective when the cube scale is fixed. -/
private theorem triadicCubeShift_injective_on_descendants
    {d n m : ℕ} : Set.InjOn triadicCubeShift
      (↑(descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) : Set (TriadicCube d)) := by
  intro R hR S hS hshift
  apply congrArg₂ Homogenization.TriadicCube.mk
  · rw [Homogenization.scale_eq_of_mem_descendantsAtScale hR,
      Homogenization.scale_eq_of_mem_descendantsAtScale hS]
  · funext i
    have hi := congrFun hshift i
    simp only [triadicCubeShift] at hi
    have hpos : 0 < cubeScaleFactor R := by
      exact zpow_pos (by norm_num) _
    have hfactor : cubeScaleFactor S = cubeScaleFactor R := by
      simp [cubeScaleFactor, Homogenization.scale_eq_of_mem_descendantsAtScale hR,
        Homogenization.scale_eq_of_mem_descendantsAtScale hS]
    rw [hfactor] at hi
    have hcast : (R.index i : ℝ) = (S.index i : ℝ) := by
      exact (mul_right_cancel₀ hpos.ne' hi)
    exact_mod_cast hcast

/-- Exact number of scale-`n` grid centres in the open centered scale-`m`
cube.  This is the `3^{d(m-n)}` count used in the manuscript union bounds. -/
theorem card_gridCentersInCube {d n m : ℕ} (hnm : n ≤ m) :
    (gridCentersInCube d n m).card = 3 ^ (d * (m - n)) := by
  unfold gridCentersInCube
  rw [Finset.card_image_iff.mpr triadicCubeShift_injective_on_descendants]
  have hk : (n : ℤ) ≤ (originCube d (m : ℤ)).scale := by
    change (n : ℤ) ≤ (m : ℤ)
    exact_mod_cast hnm
  rw [descendantsAtScale_eq_descendantsAtDepth _ hk]
  change (descendantsAtDepth (originCube d (m : ℤ))
    (Int.toNat ((m : ℤ) - (n : ℤ)))).card = _
  rw [descendantsAtDepth_card]
  have hdepth : Int.toNat ((m : ℤ) - (n : ℤ)) = m - n := by
    rw [Int.toNat_sub']
    simp
  rw [hdepth, pow_mul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
