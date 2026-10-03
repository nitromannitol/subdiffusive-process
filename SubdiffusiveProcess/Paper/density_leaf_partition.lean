module

public import SubdiffusiveProcess.Paper.lem_finite_stopping_partition_tree
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- Enumerate exactly the stopping leaves, retaining closed coverage and the
literal leaf-cost sum required by finite harmonic gluing. -/
theorem density_leaf_partition {d : ℕ} (m : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop) (nmax : ℕ) :
    ∃ (ncell : ℕ) (depth : Fin ncell → ℕ)
      (word : (i : Fin ncell) → Fin (depth i) → OddGridIndex d m),
      (∀ i, aux_lem_finite_stopping_partition_IsLeaf stop nmax (depth i) (word i)) ∧
      (∀ (n : ℕ) (w : Fin n → OddGridIndex d m), aux_lem_finite_stopping_partition_IsLeaf stop nmax n w →
        ∃ i, (⟨depth i, word i⟩ : Σ k, Fin k → OddGridIndex d m) = ⟨n, w⟩) ∧
      Pairwise (fun i j =>
        Disjoint (descendantCell m z hr (depth i) (word i) : Set (SpatialCoordinates d))
          (descendantCell m z hr (depth j) (word j) : Set (SpatialCoordinates d))) ∧
      ((⋃ i, (descendantCell m z hr (depth i) (word i) : Set (SpatialCoordinates d)))
        =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (∀ i, (descendantCell m z hr (depth i) (word i) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (⋃ i, closure (descendantCell m z hr (depth i) (word i) : Set (SpatialCoordinates d))) =
        closure (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (∀ cost : (n : ℕ) → (Fin n → OddGridIndex d m) → ℝ,
        (∑ i, cost (depth i) (word i)) =
          ∑ p ∈ aux_lem_finite_stopping_partition_leafFinset stop nmax, cost p.1 p.2) := by
  classical
  let F := aux_lem_finite_stopping_partition_leafFinset stop nmax
  let e : F ≃ Fin F.card := F.equivFin
  let leaf : Fin F.card → Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m :=
    fun i => (e.symm i).1
  have hleaf : ∀ i, aux_lem_finite_stopping_partition_IsLeaf stop nmax (leaf i).1 (leaf i).2 := fun i =>
    (aux_lem_finite_stopping_partition_mem_leafFinset stop nmax _).1 (e.symm i).2
  have hcoverAE : ((⋃ i, (descendantCell m z hr (leaf i).1 (leaf i).2 :
      Set (SpatialCoordinates d))) =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    have hsub : (⋃ i, (descendantCell m z hr (leaf i).1 (leaf i).2 :
        Set (SpatialCoordinates d))) ⊆ centeredCube z r hr :=
      Set.iUnion_subset fun i => aux_lem_finite_stopping_partition_descendantCell_subset_root m z hr _ _
    have hD := aux_lem_finite_stopping_partition_descendantCells_union_ae_eq m z hr nmax
    have hsup : (⋃ w : Fin nmax → OddGridIndex d m,
        (descendantCell m z hr nmax w : Set (SpatialCoordinates d))) ⊆
        ⋃ i, (descendantCell m z hr (leaf i).1 (leaf i).2 : Set (SpatialCoordinates d)) := by
      intro x hx
      obtain ⟨w, hxw⟩ := Set.mem_iUnion.1 hx
      obtain ⟨n, v, hv, hxv⟩ := aux_lem_finite_stopping_partition_exists_leaf_of_mem z hr stop nmax w x hxw
      have hn : n < nmax + 1 := Nat.lt_succ_of_le hv.1
      let p : Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m := ⟨⟨n, hn⟩, v⟩
      have hp : p ∈ F := (aux_lem_finite_stopping_partition_mem_leafFinset stop nmax p).2 hv
      refine Set.mem_iUnion.2 ⟨e ⟨p, hp⟩, ?_⟩
      have hl : leaf (e ⟨p, hp⟩) = p := by
        simp only [leaf]
        rw [e.symm_apply_apply]
      rw [hl]
      exact hxv
    rw [ae_eq_set]
    constructor
    · rw [Set.diff_eq_empty.2 hsub, measure_empty]
    · refine measure_mono_null (Set.diff_subset_diff_right hsup) ?_
      exact (ae_eq_set.1 hD).2
  have hsub : ∀ i, (descendantCell m z hr (leaf i).1 (leaf i).2 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)) := fun i =>
    aux_lem_finite_stopping_partition_descendantCell_subset_root m z hr _ _
  have hclosed := isClosed_iUnion_of_finite (fun i : Fin F.card =>
    isClosed_closure (s := (descendantCell m z hr (leaf i).1 (leaf i).2 : Set (SpatialCoordinates d))))
  have hcover : (⋃ i, closure (descendantCell m z hr (leaf i).1 (leaf i).2 : Set (SpatialCoordinates d))) =
      closure (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    apply subset_antisymm (Set.iUnion_subset fun i => closure_mono (hsub i))
    apply closure_minimal _ hclosed
    apply Set.diff_eq_empty.mp
    apply ((centeredCube z r hr).isOpen.sdiff hclosed).eq_empty_of_measure_zero (μ := volume)
    apply measure_mono_null (Set.diff_subset_diff_right (Set.iUnion_mono fun _ => subset_closure))
    exact (ae_eq_set.mp hcoverAE).2
  refine ⟨F.card, fun i => (leaf i).1, fun i => (leaf i).2, hleaf, ?_, ?_, hcoverAE, hsub, hcover, ?_⟩
  · intro n w hw
    have hn : n < nmax + 1 := Nat.lt_succ_of_le hw.1
    let p : Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m := ⟨⟨n, hn⟩, w⟩
    have hp : p ∈ F := (aux_lem_finite_stopping_partition_mem_leafFinset stop nmax p).2 hw
    refine ⟨e ⟨p, hp⟩, ?_⟩
    have hl : leaf (e ⟨p, hp⟩) = p := by
      simp only [leaf]
      rw [e.symm_apply_apply]
    beta_reduce
    rw [hl]
  · intro i j hij
    apply aux_lem_finite_stopping_partition_leaf_cells_disjoint z hr stop nmax (hleaf i) (hleaf j)
    intro heq
    apply hij
    apply e.symm.injective
    apply Subtype.ext
    change leaf i = leaf j
    generalize leaf i = p at heq ⊢
    generalize leaf j = q at heq ⊢
    rcases p with ⟨⟨a, ha⟩, u⟩
    rcases q with ⟨⟨b, hb⟩, v⟩
    simp only [Sigma.mk.inj_iff] at heq
    obtain ⟨rfl, h⟩ := heq
    obtain rfl := eq_of_heq h
    rfl
  · intro cost
    calc
      (∑ i : Fin F.card, cost (leaf i).1 (leaf i).2) =
          ∑ p : F, cost p.val.1 p.val.2 := e.symm.sum_comp (fun p => cost p.val.1 p.val.2)
      _ = ∑ p ∈ F, cost p.1 p.2 := Finset.sum_coe_sort F (fun (p : Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m) => cost p.1 p.2)
end Paper
