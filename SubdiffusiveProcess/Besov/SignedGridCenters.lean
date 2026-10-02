import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GridCenters
import Homogenization.Geometry.CubeMetric

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped BigOperators ENNReal
noncomputable section
namespace SubdiffusiveProcess.Besov
attribute [local instance] Classical.propDecidable

/-- The finite family of literal scale-`n` grid centres in the centered
scale-`m` cube, represented by descendant-cube shifts. -/
def signedGridCenters (d : ℕ) (n m : ℤ) : Finset (Vec d) :=
  (descendantsAtScale (originCube d m) n).image triadicCubeShift

theorem signed_shift_mem_cube
    {d : ℕ} {m : ℤ} {k : ℤ} {R : TriadicCube d} (hk : k ≤ m)
    (hR : R ∈ Homogenization.descendantsAtScale
      (Homogenization.originCube d m) k) :
    Homogenization.triadicCubeShift R ∈ cube d m := by
  have hsub : Homogenization.cubeSet R ⊆
      Homogenization.cubeSet (Homogenization.originCube d m) :=
    Homogenization.cubeSet_subset_of_mem_descendantsAtScale hk hR
  set f : ℝ := Homogenization.cubeScaleFactor R with hf
  have hfpos : 0 < f := zpow_pos (by norm_num) _
  have hcenter : Homogenization.triadicCubeShift R ∈ Homogenization.cubeSet R := by
    intro i
    constructor
    · have : ((R.index i : ℝ) - 1 / 2) * f ≤ (R.index i : ℝ) * f := by nlinarith
      simpa [Homogenization.triadicCubeShift, hf] using this
    · have : (R.index i : ℝ) * f < ((R.index i : ℝ) + 1 / 2) * f := by nlinarith
      simpa [Homogenization.triadicCubeShift, hf] using this
  have hcorner : (fun i => ((R.index i : ℝ) - 1 / 2) * f) ∈
      Homogenization.cubeSet R := by
    intro i
    exact ⟨le_rfl, by nlinarith⟩
  intro i
  have h1 := hsub hcenter i
  have h2 := (hsub hcorner i).1
  simp only [Homogenization.originCube,
    Homogenization.triadicCubeShift] at h1 h2 ⊢
  constructor
  · nlinarith [h2]
  · exact h1.2


private theorem shift_eq_of_mem_cubeSet_of_on_signedGrid
    {d : ℕ} {n : ℤ} {R : TriadicCube d} (hscale : R.scale = n)
    {z : Vec d} (hzR : z ∈ cubeSet R) (hzgrid : (∀ i : Fin d, ∃ k : ℤ, z i = (3 : ℝ) ^ n * k)) :
    triadicCubeShift R = z := by
  funext i
  obtain ⟨k, hk⟩ := hzgrid i
  have hfactor : cubeScaleFactor R = (3 : ℝ) ^ n := by
    simp [cubeScaleFactor, hscale]
  have hfactor_pos : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
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
theorem mem_signedGridCenters_iff {d : ℕ} {n m : ℤ} (hnm : n ≤ m) {z : Vec d} :
    z ∈ signedGridCenters d n m ↔ (∀ i : Fin d, ∃ k : ℤ, z i = (3 : ℝ) ^ n * k) ∧ z ∈ cube d m := by
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨R, hR, rfl⟩
    constructor
    · intro i
      refine ⟨R.index i, ?_⟩
      simp only [triadicCubeShift, cubeScaleFactor,
        Homogenization.scale_eq_of_mem_descendantsAtScale hR]
      ring
    · exact signed_shift_mem_cube hnm hR
  · rintro ⟨hzgrid, hzmem⟩
    have hzmem' : z ∈ cubeSet (originCube d m) := by
      intro i
      have hi := hzmem i
      exact ⟨hi.1.le, hi.2⟩
    obtain ⟨R, hR, hzR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet
      (Int.toNat (m - n)) hzmem'
    have hRscale : R.scale = n := by
      have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
      simp only [originCube] at hscale
      rw [hscale]
      omega
    have hR' : R ∈ descendantsAtScale (originCube d m) n := by
      have hk : n ≤ (originCube d m).scale := by
        change n ≤ m
        exact_mod_cast hnm
      rw [descendantsAtScale_eq_descendantsAtDepth _ hk]
      change R ∈ descendantsAtDepth (originCube d m)
        (Int.toNat (m - n))
      exact hR
    refine Finset.mem_image.mpr ⟨R, hR', ?_⟩
    exact shift_eq_of_mem_cubeSet_of_on_signedGrid hRscale hzR hzgrid

/-- Descendant-cube shifts are injective when the cube scale is fixed. -/
theorem shift_injective_on_signed_descendants
    {d : ℕ} {n m : ℤ} : Set.InjOn triadicCubeShift
      (↑(descendantsAtScale (originCube d m) n) : Set (TriadicCube d)) := by
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


/-- Number of signed-scale grid centres in the parent cube. -/
theorem signedGridCenters_card {d : ℕ} {n m : ℤ} (hnm : n ≤ m) :
    (signedGridCenters d n m).card = 3 ^ (d * (m - n).toNat) := by
  unfold signedGridCenters
  rw [Finset.card_image_iff.mpr shift_injective_on_signed_descendants]
  rw [descendantsAtScale_eq_descendantsAtDepth _ hnm, descendantsAtDepth_card, pow_mul]
  rfl

end SubdiffusiveProcess.Besov
