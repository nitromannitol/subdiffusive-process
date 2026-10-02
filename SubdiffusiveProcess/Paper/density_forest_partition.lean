import SubdiffusiveProcess.Paper.density_leaf_partition
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- Join stopping partitions of finitely many base cells. Each base may use its
own stopping horizon; costs are exactly the sum of its own leaf costs. -/
theorem density_forest_partition {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (nb m : ℕ) (zc : Fin nb → SpatialCoordinates d) (rc : Fin nb → ℝ)
    (hrc : ∀ i, 0 < rc i)
    (hBaseSub : ∀ i, (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hBaseDisj : Pairwise (fun i j => Disjoint
      (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d))
      (centeredCube (zc j) (rc j) (hrc j) : Set (SpatialCoordinates d))))
    (hBaseCover : (⋃ i, closure (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d))) =
      closure (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hBaseAE : (⋃ i, (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d)))
      =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d)))
    (stop : Fin nb → (n : ℕ) → (Fin n → OddGridIndex d m) → Prop)
    (nmax : Fin nb → ℕ) :
    ∃ (total : ℕ) (root : Fin total → Fin nb) (depth : Fin total → ℕ)
      (word : (i : Fin total) → Fin (depth i) → OddGridIndex d m),
      let cell := fun i => descendantCell m (zc (root i)) (hrc (root i)) (depth i) (word i)
      (∀ i, aux_lem_finite_stopping_partition_IsLeaf (stop (root i)) (nmax (root i)) (depth i) (word i)) ∧
      (∀ i, (cell i : Set (SpatialCoordinates d)) ⊆
        (centeredCube (zc (root i)) (rc (root i)) (hrc (root i)) : Set (SpatialCoordinates d))) ∧
      (∀ i, (cell i : Set (SpatialCoordinates d)) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      Pairwise (fun i j => Disjoint (cell i : Set (SpatialCoordinates d)) (cell j : Set (SpatialCoordinates d))) ∧
      (⋃ i, closure (cell i : Set (SpatialCoordinates d))) = closure (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      ∀ cost : Fin nb → (n : ℕ) → (Fin n → OddGridIndex d m) → ℝ,
        (∑ i, cost (root i) (depth i) (word i)) =
          ∑ b, ∑ p ∈ aux_lem_finite_stopping_partition_leafFinset (stop b) (nmax b), cost b p.1 p.2 := by
  classical
  choose nc dep wd hLeaf hExhaust hDisj hAE hSub hCover hSum using
    fun i => density_leaf_partition m (zc i) (hrc i) (stop i) (nmax i)
  let T := (i : Fin nb) × Fin (nc i)
  let e := (Fintype.equivFin T).symm
  let cells := fun p : T => descendantCell m (zc p.1) (hrc p.1) (dep p.1 p.2) (wd p.1 p.2)
  have hUnion : ∀ f : T → Set (SpatialCoordinates d),
      (⋃ j, f (e j)) = ⋃ i, ⋃ a, f ⟨i, a⟩ := by
    intro f
    rw [e.surjective.iUnion_comp, Set.iUnion_sigma]
  have hPair : Pairwise (fun p q : T => Disjoint (cells p : Set (SpatialCoordinates d))
      (cells q : Set (SpatialCoordinates d))) := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hne
    by_cases hij : i = j
    · subst j
      exact hDisj i (fun hab => hne (by cases hab; rfl))
    · exact (hBaseDisj hij).mono (hSub i a) (hSub j b)
  refine ⟨Fintype.card T, fun j => (e j).1, fun j => dep (e j).1 (e j).2,
    fun j => wd (e j).1 (e j).2, ?_⟩
  intro cell
  refine ⟨(fun j => hLeaf (e j).1 (e j).2), (fun j => hSub (e j).1 (e j).2),
    (fun j => (hSub (e j).1 (e j).2).trans (hBaseSub (e j).1)), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hPair (fun heq => hij (e.injective heq))
  · change (⋃ j, closure (cells (e j) : Set (SpatialCoordinates d))) = _
    rw [hUnion (fun p => closure (cells p : Set (SpatialCoordinates d)))]
    simp_rw [cells, hCover]
    exact hBaseCover
  · change (⋃ j, (cells (e j) : Set (SpatialCoordinates d))) =ᵐ[volume] _
    rw [hUnion (fun p => (cells p : Set (SpatialCoordinates d)))]
    filter_upwards [ae_all_iff.mpr hAE, hBaseAE] with x hx hxbase
    have hp : (∃ i, ∃ j, x ∈ (cells ⟨i, j⟩ : Set (SpatialCoordinates d))) ↔
        ∃ i, x ∈ (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d)) := by
      apply exists_congr
      intro i
      have hi : x ∈ (⋃ a, (descendantCell m (zc i) (hrc i) (dep i a) (wd i a) : Set (SpatialCoordinates d))) ↔
          x ∈ (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d)) := Iff.of_eq (hx i)
      simpa only [cells, Set.mem_iUnion] using hi
    have hb : (∃ i, x ∈ (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d))) ↔
        x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      have hb' : x ∈ (⋃ i, (centeredCube (zc i) (rc i) (hrc i) : Set (SpatialCoordinates d))) ↔
          x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := Iff.of_eq hxbase
      simpa only [Set.mem_iUnion] using hb'
    apply propext
    change x ∈ (⋃ i, ⋃ j, (cells ⟨i, j⟩ : Set (SpatialCoordinates d))) ↔ _
    simpa only [Set.mem_iUnion] using hp.trans hb
  · intro cost
    calc
      (∑ j, cost (e j).1 (dep (e j).1 (e j).2) (wd (e j).1 (e j).2)) =
          ∑ p : T, cost p.1 (dep p.1 p.2) (wd p.1 p.2) := e.sum_comp (fun p : T => cost p.1 (dep p.1 p.2) (wd p.1 p.2))
      _ = ∑ i, ∑ a, cost i (dep i a) (wd i a) := Fintype.sum_sigma _
      _ = _ := Finset.sum_congr rfl (fun i _ => hSum i (cost i))
end Paper
