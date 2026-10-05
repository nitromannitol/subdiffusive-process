module

public import SubdiffusiveProcess.Geometry.TriadicGridScale
public import SubdiffusiveProcess.Geometry.OddGridPartition
public import SubdiffusiveProcess.Geometry.ClosedOddGridCover
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- Every sufficiently fine absolute triadic mesh partitions a triadic killed
cube exactly, with integer centres, disjoint interiors and full closed coverage. -/
theorem density_base_partition {d : ℕ}
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (ell : ℤ) (hscale : R = (3 : ℝ) ^ ell) (k : ℕ) (hk : 0 ≤ ell + (k : ℤ)) :
    ∃ depth : ℕ, (depth : ℤ) = ell + (k : ℤ) ∧
      let m := triadicHalf depth
      let centre := fun q : OddGridIndex d m => triadicGridCenter z R ⟨depth, q⟩
      let side := (3 : ℝ) ^ (-(k : ℤ))
      let cells := fun q : OddGridIndex d m =>
        centeredCube (centre q) side (zpow_pos (by norm_num) _)
      (∀ q, centre q = fun i => z i + side * (((q i).val : ℤ) - (m : ℤ))) ∧
      (∀ q, (cells q : Set (SpatialCoordinates d)) = (oddGridCell z R hR m q : Set (SpatialCoordinates d))) ∧
      (∀ q, (cells q : Set (SpatialCoordinates d)) ⊆ (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      Pairwise (fun q q' => Disjoint (cells q : Set (SpatialCoordinates d)) (cells q' : Set (SpatialCoordinates d))) ∧
      (⋃ q, closure (cells q : Set (SpatialCoordinates d))) = closure (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      (⋃ q, (cells q : Set (SpatialCoordinates d))) =ᵐ[volume] (centeredCube z R hR : Set (SpatialCoordinates d)) := by
  let depth := (ell + (k : ℤ)).toNat
  have hdepth : (depth : ℤ) = ell + (k : ℤ) := Int.toNat_of_nonneg hk
  refine ⟨depth, hdepth, ?_⟩
  dsimp only
  have hside : ∀ q : OddGridIndex d (triadicHalf depth),
      triadicGridSide R ⟨depth, q⟩ = (3 : ℝ) ^ (-(k : ℤ)) := by
    intro q
    rw [triadicGridSide_eq_zpow R ell hscale, hdepth]
    congr 1
    ring
  have hcell : ∀ q : OddGridIndex d (triadicHalf depth),
      (centeredCube (triadicGridCenter z R ⟨depth, q⟩) ((3 : ℝ) ^ (-(k : ℤ)))
        (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) =
      (oddGridCell z R hR (triadicHalf depth) q : Set (SpatialCoordinates d)) := by
    intro q
    change Metric.ball _ _ = Metric.ball _ _
    change Metric.ball (triadicGridCenter z R ⟨depth, q⟩) _ =
      Metric.ball (triadicGridCenter z R ⟨depth, q⟩) (triadicGridSide R ⟨depth, q⟩ / 2)
    rw [hside]
  refine ⟨?_, hcell, ?_, ?_, ?_, ?_⟩
  · intro q
    rw [triadicGridCenter_eq_int_shift, hside]
  · intro q
    rw [hcell]
    exact oddGridCell_subset z hR (triadicHalf depth) q
  · intro q q' hqq
    rw [hcell, hcell]
    exact oddGridCell_pairwiseDisjoint z hR (triadicHalf depth) hqq
  · simp_rw [hcell]
    exact oddGridCell_closure_iUnion_eq_closure_centeredCube z hR (triadicHalf depth)
  · simp_rw [hcell]
    exact oddGrid_union_ae_eq z hR (triadicHalf depth)
end SubdiffusiveProcess.Paper
