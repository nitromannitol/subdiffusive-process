module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerCoefficient

@[expose] public section

/-!
# Retained indices for strict decay starting at an arbitrary scale

The proof of `lim:lem-strict-decay` keeps every layer through `ell` and then
`ell + R, ..., ell + N * R`. The starting case `N = 0` is the full prefix,
not the single layer zero of the Section 5 sparse induction.
-/

namespace SubdiffusiveProcess.Section10

/-- The literal retained set in the arbitrary-scale strict-decay argument. -/
def retainedPrefixIndices (ell R N : ℕ) : Finset ℕ :=
  Finset.range (ell + 1) ∪
    (Finset.range N).image (fun j => ell + (j + 1) * R)

/-- Layers omitted from a finite cutoff when keeping the retained prefix. -/
def omittedPrefixIndices (ell R N m : ℕ) : Finset ℕ :=
  Finset.range (m + 1) \ retainedPrefixIndices ell R N

@[simp] theorem retainedPrefixIndices_zero (ell R : ℕ) :
    retainedPrefixIndices ell R 0 = Finset.range (ell + 1) := by
  simp only [retainedPrefixIndices, Finset.range_zero, Finset.image_empty,
    Finset.union_empty]

theorem mem_retainedPrefixIndices {ell R N k : ℕ} :
    k ∈ retainedPrefixIndices ell R N ↔
      k ≤ ell ∨ ∃ j < N, ell + (j + 1) * R = k := by
  simp only [retainedPrefixIndices, Finset.mem_union, Finset.mem_range,
    Finset.mem_image, Nat.lt_succ_iff]

theorem range_subset_retainedPrefixIndices (ell R N : ℕ) :
    Finset.range (ell + 1) ⊆ retainedPrefixIndices ell R N :=
  Finset.subset_union_left

/-- Positive spacing keeps every later retained layer strictly above `ell`. -/
theorem disjoint_prefix_retained_tail (ell : ℕ) {R : ℕ} (hR : 0 < R) (N : ℕ) :
    Disjoint (Finset.range (ell + 1))
      ((Finset.range N).image (fun j => ell + (j + 1) * R)) := by
  refine Finset.disjoint_left.2 ?_
  intro k hk htail
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 htail
  have hpos : 0 < (j + 1) * R := Nat.mul_pos (Nat.succ_pos j) hR
  have hle : ell + (j + 1) * R ≤ ell := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  omega

theorem retained_tail_injective (ell : ℕ) {R : ℕ} (hR : 0 < R) :
    Function.Injective (fun j : ℕ => ell + (j + 1) * R) := by
  intro i j hij
  have hmul := Nat.add_left_cancel hij
  have hsucc := Nat.eq_of_mul_eq_mul_right hR hmul
  omega

/-- All retained layers are no higher than the current induction scale. -/
theorem le_scale_of_mem_retainedPrefixIndices {ell R N k : ℕ}
    (hk : k ∈ retainedPrefixIndices ell R N) : k ≤ ell + N * R := by
  rcases mem_retainedPrefixIndices.1 hk with hk | ⟨j, hj, rfl⟩
  · exact hk.trans (Nat.le_add_right ell (N * R))
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right R (by omega : j + 1 ≤ N)) ell

theorem retainedPrefixIndices_subset_range (ell R N : ℕ) :
    retainedPrefixIndices ell R N ⊆ Finset.range (ell + N * R + 1) := by
  intro k hk
  exact Finset.mem_range.2 (Nat.lt_succ_iff.2
    (le_scale_of_mem_retainedPrefixIndices hk))

theorem retainedPrefixIndices_subset_range_of_scale_le {ell R N m : ℕ}
    (hm : ell + N * R ≤ m) :
    retainedPrefixIndices ell R N ⊆ Finset.range (m + 1) := by
  intro k hk
  exact Finset.mem_range.2 (Nat.lt_succ_iff.2
    ((le_scale_of_mem_retainedPrefixIndices hk).trans hm))

theorem scale_mem_retainedPrefixIndices (ell R N : ℕ) :
    ell + N * R ∈ retainedPrefixIndices ell R N := by
  cases N with
  | zero => exact mem_retainedPrefixIndices.2 (Or.inl (by simp only [Nat.zero_mul,
      Nat.add_zero, le_refl]))
  | succ n => exact mem_retainedPrefixIndices.2 (Or.inr ⟨n, Nat.lt_succ_self n, rfl⟩)

theorem retainedPrefixIndices_succ (ell R N : ℕ) :
    retainedPrefixIndices ell R (N + 1) =
      insert (ell + (N + 1) * R) (retainedPrefixIndices ell R N) := by
  classical
  rw [retainedPrefixIndices, (Finset.range_add_one (n := N)), Finset.image_insert,
    Finset.union_insert]
  rfl

theorem scale_lt_next_scale (ell : ℕ) {R : ℕ} (hR : 0 < R) (N : ℕ) :
    ell + N * R < ell + (N + 1) * R := by
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem next_layer_not_mem_retainedPrefixIndices (ell : ℕ) {R : ℕ}
    (hR : 0 < R) (N : ℕ) :
    ell + (N + 1) * R ∉ retainedPrefixIndices ell R N := by
  intro hk
  have hle := le_scale_of_mem_retainedPrefixIndices hk
  have hlt := scale_lt_next_scale ell hR N
  omega

theorem disjoint_retainedPrefixIndices_next (ell : ℕ) {R : ℕ}
    (hR : 0 < R) (N : ℕ) :
    Disjoint (retainedPrefixIndices ell R N) {ell + (N + 1) * R} := by
  exact Finset.disjoint_singleton_right.2
    (next_layer_not_mem_retainedPrefixIndices ell hR N)

theorem disjoint_retainedPrefixIndices_next_set (ell : ℕ) {R : ℕ}
    (hR : 0 < R) (N : ℕ) :
    Disjoint (retainedPrefixIndices ell R N : Set ℕ)
      ({ell + (N + 1) * R} : Set ℕ) := by
  exact Set.disjoint_singleton_right.2
    (next_layer_not_mem_retainedPrefixIndices ell hR N)

theorem retainedPrefixIndices_mono (ell R : ℕ) {N K : ℕ} (hNK : N ≤ K) :
    retainedPrefixIndices ell R N ⊆ retainedPrefixIndices ell R K := by
  intro k hk
  rcases mem_retainedPrefixIndices.1 hk with hk | ⟨j, hj, hjk⟩
  · exact mem_retainedPrefixIndices.2 (Or.inl hk)
  · exact mem_retainedPrefixIndices.2 (Or.inr ⟨j, hj.trans_le hNK, hjk⟩)

/-- Taking `N = floor ((m - ell) / R)` fits the retained set inside cutoff `m`. -/
theorem floor_scale_le {ell m R : ℕ} (hell : ell ≤ m) :
    ell + ((m - ell) / R) * R ≤ m := by
  have h := Nat.div_mul_le_self (m - ell) R
  omega

theorem lt_next_floor_scale (ell m : ℕ) {R : ℕ} (hR : 0 < R) :
    m < ell + ((m - ell) / R + 1) * R := by
  have h := Nat.lt_mul_div_succ (m - ell) hR
  rw [Nat.mul_comm R] at h
  omega

theorem disjoint_retainedPrefixIndices_omitted (ell R N m : ℕ) :
    Disjoint (retainedPrefixIndices ell R N) (omittedPrefixIndices ell R N m) := by
  exact Finset.disjoint_sdiff

theorem retainedPrefixIndices_union_omitted {ell R N m : ℕ}
    (hm : ell + N * R ≤ m) :
    retainedPrefixIndices ell R N ∪ omittedPrefixIndices ell R N m =
      Finset.range (m + 1) := by
  exact Finset.union_sdiff_of_subset (retainedPrefixIndices_subset_range_of_scale_le hm)

@[simp] theorem omittedPrefixIndices_zero_at_base (ell R : ℕ) :
    omittedPrefixIndices ell R 0 ell = ∅ := by
  simp only [omittedPrefixIndices, retainedPrefixIndices_zero, Finset.sdiff_self]

end SubdiffusiveProcess.Section10
