import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometry
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Finset.Max

/-!
# Interior fractions from compact containment

A compact subset of an open cube lies inside a strictly smaller concentric
cube. The fraction is obtained from an attained maximum of the distance to
the center. A finite family of fractions below one admits a common fraction
still below one, including when the index type is empty.
-/

set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Compact containment supplies a strictly positive interior margin in a parent cube. -/
theorem exists_goodCube_compact_interior_fraction {d : ℕ}
    {K : Set (Vec d)} (hK : IsCompact K) (B : Cube d) (hB : 0 < B.2)
    (hKB : K ⊆ cubeSet B) :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
      K ⊆ centeredAxisCube B.1 (theta * B.2) := by
  rcases Set.eq_empty_or_nonempty K with hempty | ⟨y, hyK⟩
  · exact ⟨1 / 2, by norm_num, by norm_num, by rw [hempty]; exact Set.empty_subset _⟩
  · obtain ⟨x0, hx0K, hmax⟩ := hK.exists_isMaxOn ⟨y, hyK⟩
      (Continuous.continuousOn (continuous_id.dist continuous_const :
        Continuous fun x : Vec d => dist x B.1))
    have hxB' : x0 ∈ centeredAxisCube B.1 B.2 := hKB hx0K
    rw [mem_centeredAxisCube] at hxB'
    set r := dist x0 B.1 with hrdef
    have hr_nonneg : 0 ≤ r := dist_nonneg
    have hr : r < B.2 / 2 := by
      rw [dist_pi_lt_iff (half_pos hB)]
      intro i
      rw [Real.dist_eq]
      exact hxB' i
    have h2 : 2 * r < B.2 := by
      have h5 : B.2 / 2 + B.2 / 2 = B.2 := by ring
      calc 2 * r = r + r := by ring
        _ < B.2 / 2 + B.2 / 2 := add_lt_add hr hr
        _ = B.2 := h5
    set theta := (1 + 2 * r / B.2) / 2 with htheta
    have htheta_pos : 0 < theta := by
      rw [htheta]
      refine div_pos ?_ two_pos
      have h2r : 0 ≤ 2 * r := mul_nonneg zero_le_two hr_nonneg
      positivity
    have htheta_lt : theta < 1 := by
      rw [htheta]
      have h4 : (0 : ℝ) < 2 := by norm_num
      rw [div_lt_iff₀ h4]
      have h3 : 2 * r / B.2 < 1 := (div_lt_one hB).mpr h2
      linarith
    have hkey : theta * B.2 = B.2 / 2 + r := by
      rw [htheta]
      field_simp
    refine ⟨theta, htheta_pos, htheta_lt, ?_⟩
    intro x hxK
    rw [mem_centeredAxisCube, hkey]
    have hle : dist x B.1 ≤ r := hmax hxK
    have hcoord : ∀ i, dist (x i) (B.1 i) ≤ r := (dist_pi_le_iff hr_nonneg).mp hle
    have hb : r < (B.2 / 2 + r) / 2 := by
      have h4 : (0 : ℝ) < 2 := by norm_num
      rw [lt_div_iff₀ h4]
      linarith
    intro i
    calc |x i - B.1 i| = dist (x i) (B.1 i) := (Real.dist_eq (x i) (B.1 i)).symm
      _ ≤ r := hcoord i
      _ < (B.2 / 2 + r) / 2 := hb

/-- Finitely many fractions below one admit a common positive upper bound below one. -/
theorem exists_goodCube_common_fraction {ι : Type*} [Finite ι]
    (a : ι → ℝ) (ha : ∀ i, a i < 1) :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧ ∀ i, a i ≤ theta := by
  letI := Fintype.ofFinite ι
  let s : Finset ℝ := insert 0 (Finset.univ.image a)
  have hne : s.Nonempty := Finset.insert_nonempty 0 _
  have hlt : ∀ x ∈ s, x < 1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · linarith
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ha i
  have h0mem : (0 : ℝ) ∈ s := Finset.mem_insert_self 0 _
  have hb0 : 0 ≤ s.max' hne := by
    have := Finset.le_max' s 0 h0mem
    linarith
  have hblt : s.max' hne < 1 := hlt _ (Finset.max'_mem s hne)
  refine ⟨(1 + s.max' hne) / 2, by linarith, by linarith, ?_⟩
  intro i
  have hmem : a i ∈ s :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem a (Finset.mem_univ i))
  have := Finset.le_max' s (a i) hmem
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
