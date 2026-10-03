module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeGeometry

@[expose] public section




set_option autoImplicit false

open Homogenization hiding Vec
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Enlarging the finite offset grid preserves an admissible geometry. -/
theorem isLocalCubeGeometry_mono_grid {d j1 j2 : ℕ}
    {grid grid' : Finset (Vec d)} {U : Cube d}
    {Pfam : Set (Cube d × Cube d)} {Qfam Afam : Set (Cube d)}
    (h : IsLocalCubeGeometry grid j1 j2 U Pfam Qfam Afam)
    (hgrid : grid ⊆ grid') :
    IsLocalCubeGeometry grid' j1 j2 U Pfam Qfam Afam := by
  refine { h with gridded := ?_ }
  intro Q hQ
  obtain ⟨g, hg, m, k, hs, hy⟩ := h.gridded Q hQ
  exact ⟨g, hgrid hg, m, k, hs, hy⟩

/-- An additional positive grid cube in the middle quarter can be placed
in both families; the existing pairs and chain witnesses still work. -/
theorem isLocalCubeGeometry_insert_cube {d j1 j2 : ℕ}
    {grid : Finset (Vec d)} {U R : Cube d}
    {Pfam : Set (Cube d × Cube d)} {Qfam Afam : Set (Cube d)}
    (h : IsLocalCubeGeometry grid j1 j2 U Pfam Qfam Afam)
    (hR : 0 < R.2) (hgR : IsGridCube grid R.1 R.2)
    (hRU : cubeSet R ⊆ middleQuarter U) :
    IsLocalCubeGeometry grid j1 j2 U Pfam (insert R Qfam) (insert R Afam) := by
  refine {
    finite_Q := h.finite_Q.insert R
    finite_P := h.finite_P
    self_mem := mem_insert_of_mem _ h.self_mem
    side_pos := ?_
    gridded := ?_
    pair_mem := ?_
    pair_nested := h.pair_nested
    pair_middle_half := h.pair_middle_half
    pair_in_half := h.pair_in_half
    pair_outer_side := h.pair_outer_side
    pair_inner_side := h.pair_inner_side
    cover := h.cover
    A_subset := ?_
    A_in_quarter := ?_
    chain := ?_ }
  · intro Q hQ
    rcases mem_insert_iff.mp hQ with rfl | hQ
    · exact hR
    · exact h.side_pos Q hQ
  · intro Q hQ
    rcases mem_insert_iff.mp hQ with rfl | hQ
    · exact hgR
    · exact h.gridded Q hQ
  · intro p hp
    exact ⟨mem_insert_of_mem _ (h.pair_mem p hp).1,
      mem_insert_of_mem _ (h.pair_mem p hp).2⟩
  · intro A hA
    rcases mem_insert_iff.mp hA with rfl | hA
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (h.A_subset hA)
  · intro A hA
    rcases mem_insert_iff.mp hA with rfl | hA
    · exact hRU
    · exact h.A_in_quarter A hA
  · intro x hx y hy
    obtain ⟨k, ch, hp, hxch, hych, hchain⟩ := h.chain x hx y hy
    refine ⟨k, ch, hp, hxch, hych, ?_⟩
    intro i hi
    obtain ⟨A, hA, hsub⟩ := hchain i hi
    exact ⟨A, mem_insert_of_mem _ hA, hsub⟩



theorem exists_isGridCube_near_insert {d : ℕ} (grid : Finset (Vec d))
    (x : Vec d) (k : ℕ) :
    ∃ z : Vec d, IsGridCube (insert x grid) z ((3 : ℝ) ^ (-(k : ℤ))) ∧
      ∀ i, |z i - x i| ≤ (3 : ℝ) ^ (-(k : ℤ)) / 2 := by
  classical
  set L : ℝ := (3 : ℝ) ^ (-(k : ℤ)) with hLdef
  have hLpos : (0 : ℝ) < L := by rw [hLdef]; positivity
  set v : Fin d → ℤ := fun i => round ((x i - L * x i) / L) with hvdef
  refine ⟨fun i => L * (x i + (v i : ℝ)), ⟨x, Finset.mem_insert_self _ _,
    -(k : ℤ), v, rfl, rfl⟩, ?_⟩
  intro i
  have hround : |(x i - L * x i) / L - ((v i : ℤ) : ℝ)| ≤ 1 / 2 := abs_sub_round _
  have hrw : L * (x i + (v i : ℝ)) - x i
      = -(L * ((x i - L * x i) / L - ((v i : ℤ) : ℝ))) := by
    field_simp
    ring
  rw [hrw, abs_neg, abs_mul, abs_of_pos hLpos]
  calc L * |(x i - L * x i) / L - ((v i : ℤ) : ℝ)| ≤ L * (1 / 2) :=
        mul_le_mul_of_nonneg_left hround hLpos.le
    _ = L / 2 := by ring

/-- Every overlap cube lies compactly inside the parent. -/
theorem compactlyInside_of_mem_Afam {d j1 j2 : ℕ}
    {grid : Finset (Vec d)} {U A : Cube d}
    {Pfam : Set (Cube d × Cube d)} {Qfam Afam : Set (Cube d)}
    (h : IsLocalCubeGeometry grid j1 j2 U Pfam Qfam Afam) (hA : A ∈ Afam) :
    CompactlyInside A U := by
  have hU : 0 < U.2 := h.side_pos U h.self_mem
  exact (closure_mono (h.A_in_quarter A hA)).trans
    (closure_centeredAxisCube_subset (by linarith : U.2 / 4 < U.2))

/-- The overlap mass hypothesis is already a consequence of the descendant
mass hypothesis for an admissible geometry. -/
theorem mass_overlap_of_mass_descendant {d j1 j2 : ℕ}
    {grid : Finset (Vec d)} {U : Cube d}
    {Pfam : Set (Cube d × Cube d)} {Qfam Afam : Set (Cube d)}
    (h : IsLocalCubeGeometry grid j1 j2 U Pfam Qfam Afam)
    (mu : Measure (Vec d)) (c : ℝ≥0∞)
    (hmass : ∀ B' ∈ Qfam, ∀ B ∈ Qfam, CompactlyInside B' B →
      c * mu (cubeSet B) ≤ mu (cubeSet B')) :
    ∀ A ∈ Afam, c * mu (cubeSet U) ≤ mu (cubeSet A) := by
  intro A hA
  exact hmass A (h.A_subset hA) U h.self_mem (compactlyInside_of_mem_Afam h hA)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
