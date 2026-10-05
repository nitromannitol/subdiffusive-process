module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeLayerEvents
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Auxiliary covers for compact descendant interiors

The torsion lower-bound argument uses finite auxiliary pairs inside each original
compact descendant pair. These cubes are
selected separately from the exported local geometry. They impose no additional
descendant obligations on that family.

Compactness gives a common sufficiently small outer triadic side. Inner cubes
with any prescribed positive relative depth then admit a finite subcover.
-/

set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- All sufficiently small concentric triadic cubes around a compact set stay inside its open neighborhood. -/
theorem exists_goodCube_auxiliary_depth {d : ℕ}
    {K W : Set (Vec d)} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ J : ℕ, ∀ k : ℕ, J ≤ k →
      (3 : ℝ) ^ (-(k : ℤ)) ≤ eta ∧
      ∀ x ∈ K, closure (centeredAxisCube x ((3 : ℝ) ^ (-(k : ℤ)))) ⊆ W := by
  obtain ⟨δ, hδpos, hδ⟩ := hK.exists_cthickening_subset_open hW hKW
  obtain ⟨J, hJ⟩ :=
    exists_pow_lt_of_lt_one (lt_min heta hδpos) (show (1 / 3 : ℝ) < 1 by norm_num)
  refine ⟨J, fun k hk => ?_⟩
  have h3 : (3 : ℝ) ^ (-(k : ℤ)) = (1 / 3 : ℝ) ^ k := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, inv_eq_one_div]
  have hle : (1 / 3 : ℝ) ^ k ≤ (1 / 3 : ℝ) ^ J :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have hlt : (1 / 3 : ℝ) ^ k < min eta δ := hle.trans_lt hJ
  refine ⟨h3 ▸ hlt.le.trans (min_le_left eta δ), fun x hx => ?_⟩
  set s := (3 : ℝ) ^ (-(k : ℤ)) with hs_def
  have hs : 0 < s := by rw [h3]; exact pow_pos (by norm_num) k
  have hsub : centeredAxisCube x s ⊆ Metric.closedBall x (s / 2) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_pi_le_iff (by linarith)]
    intro i
    rw [Real.dist_eq]
    exact (mem_centeredAxisCube.mp hz i).le
  have hclos : closure (centeredAxisCube x s) ⊆ Metric.closedBall x (s / 2) :=
    closure_minimal hsub Metric.isClosed_closedBall
  intro y hy
  have hdy : dist y x ≤ s / 2 := by
    have h := hclos hy
    rwa [Metric.mem_closedBall] at h
  have h2 : y ∈ Metric.closedBall x δ :=
    Metric.mem_closedBall.mpr (by linarith [hlt, min_le_right eta δ])
  exact hδ (Metric.closedBall_subset_cthickening hx δ h2)

/-- A compact set is covered by finitely many cubes of a prescribed positive side, with centers in the compact set. -/
theorem exists_goodCube_finite_center_cover {d : ℕ}
    {K : Set (Vec d)} (hK : IsCompact K) {side : ℝ} (hside : 0 < side) :
    ∃ centers : Finset (Vec d),
      (↑centers : Set (Vec d)) ⊆ K ∧
      K ⊆ ⋃ x ∈ centers, centeredAxisCube x side := by
  classical
  have hsU : K ⊆ ⋃ x : ↥K, centeredAxisCube (x : Vec d) side := by
    intro z hz
    exact Set.mem_iUnion.2 ⟨⟨z, hz⟩, mem_centeredAxisCube.2 fun i => by
      rw [sub_self, abs_zero]
      linarith [hside]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (U := fun x : ↥K => centeredAxisCube (x : Vec d) side)
    (fun x => isOpen_centeredAxisCube _ _) hsU
  refine ⟨t.image (fun x : ↥K => (x : Vec d)), ?_, ?_⟩
  · intro z hz
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hz
    exact x.property
  · intro z hz
    have hz' := ht hz
    simp only [Set.mem_iUnion, exists_prop] at hz'
    obtain ⟨x, hx, hzx⟩ := hz'
    refine Set.mem_iUnion₂.2 ⟨x, Finset.mem_image.2 ⟨x, hx, rfl⟩, hzx⟩

/-- An auxiliary inner cube of positive triadic depth lies compactly inside the middle half of its outer cube. -/
theorem goodCube_auxiliary_pair_middle_half {d : ℕ}
    (x : Vec d) (j k : ℕ) (hj : 1 ≤ j) :
    closure (centeredAxisCube x
      ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ)))) ⊆
      centeredAxisCube x ((3 : ℝ) ^ (-(k : ℤ)) / 2) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hinv : (3 : ℝ) ^ (-(j : ℤ)) ≤ 1 / 3 := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  have hk : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos h3pos _
  have hmul : (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ)) ≤ (1 / 3) * (3 : ℝ) ^ (-(k : ℤ)) :=
    mul_le_mul_of_nonneg_right hinv hk.le
  have hlt : (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ)) < (3 : ℝ) ^ (-(k : ℤ)) / 2 := by
    have h1 : (1 / 3) * (3 : ℝ) ^ (-(k : ℤ)) < (1 / 2) * (3 : ℝ) ^ (-(k : ℤ)) := by
      nlinarith [hk]
    linarith
  exact closure_centeredAxisCube_subset hlt

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
