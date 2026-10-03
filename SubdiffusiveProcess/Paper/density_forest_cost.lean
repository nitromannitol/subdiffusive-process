module

public import SubdiffusiveProcess.Paper.density_forest_partition
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- Choose a separate sufficiently cheap stopping horizon in each base cell,
then join the leaves with a global source-mass cost bound. -/
theorem density_forest_cost {d : ℕ}
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
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (C : ℝ) (hC : 0 ≤ C)
    (cost : Fin nb → (n : ℕ) → (Fin n → OddGridIndex d m) → ℝ)
    (hsmall : ∀ b, ∀ eps : ℝ, 0 < eps → ∃ᶠ J : ℕ in atTop,
      (∑ p ∈ aux_lem_finite_stopping_partition_leafFinset (stop b) J, cost b p.1 p.2) ≤
        C * nu.real (centeredCube (zc b) (rc b) (hrc b) : Set (SpatialCoordinates d)) + eps) :
    ∀ eps : ℝ, 0 < eps → ∃ nmax : Fin nb → ℕ,
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
      (∀ cost' : Fin nb → (n : ℕ) → (Fin n → OddGridIndex d m) → ℝ,
        (∑ i, cost' (root i) (depth i) (word i)) =
          ∑ b, ∑ p ∈ aux_lem_finite_stopping_partition_leafFinset (stop b) (nmax b), cost' b p.1 p.2) ∧
      (∑ i, cost (root i) (depth i) (word i)) ≤ C * nu.real (centeredCube z r hr : Set (SpatialCoordinates d)) + eps := by
  classical
  intro eps heps
  let small := eps / ((nb : ℝ) + 1)
  have hsmallPos : 0 < small := div_pos heps (by positivity)
  choose nmax hmax using fun b => (hsmall b small hsmallPos).exists
  obtain ⟨total, root, depth, word, hLeaf, hBase, hSub, hDisj, hCover, hAE, hSum⟩ :=
    density_forest_partition z r hr nb m zc rc hrc hBaseSub hBaseDisj hBaseCover hBaseAE stop nmax
  refine ⟨nmax, total, root, depth, word, hLeaf, hBase, hSub, hDisj, hCover, hAE, hSum, ?_⟩
  have hMass : (∑ b, nu.real (centeredCube (zc b) (rc b) (hrc b) : Set (SpatialCoordinates d))) ≤
      nu.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [← measureReal_iUnion_fintype hBaseDisj
      (fun b => (centeredCube (zc b) (rc b) (hrc b)).isOpen.measurableSet)]
    exact measureReal_mono (Set.iUnion_subset hBaseSub) (measure_ne_top _ _)
  have hError : (nb : ℝ) * small ≤ eps := by
    have hEq : small * ((nb : ℝ) + 1) = eps := div_mul_cancel₀ eps (by positivity)
    nlinarith [hsmallPos]
  rw [hSum cost]
  calc
    _ ≤ ∑ b : Fin nb, (C * nu.real (centeredCube (zc b) (rc b) (hrc b) : Set (SpatialCoordinates d)) + small) :=
      Finset.sum_le_sum (fun b _ => hmax b)
    _ = C * (∑ b, nu.real (centeredCube (zc b) (rc b) (hrc b) : Set (SpatialCoordinates d))) + (nb : ℝ) * small := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hMass hC) hError
end Paper
