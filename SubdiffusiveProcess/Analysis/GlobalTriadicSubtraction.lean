module

public import SubdiffusiveProcess.Geometry.TriadicNesting
public import SubdiffusiveProcess.Analysis.TriadicChildAverages
public import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra

@[expose] public section

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section
namespace SubdiffusiveProcess

/-- The triadic-average operator at fixed depth `m` is additive under subtraction:
restricting integrability to each actual cell and using linearity of the volume
average there, the per-cell difference matches the difference of the cell values,
and this is unaffected by the indicator since both sides vanish off the cell. -/
theorem globalTriadicAverages_sub {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (u v : SpatialCoordinates d → ℝ)
    (hu : IntegrableOn u (centeredCube z r hr : Set (SpatialCoordinates d)) volume)
    (hv : IntegrableOn v (centeredCube z r hr : Set (SpatialCoordinates d)) volume) :
    let E : (SpatialCoordinates d → ℝ) → SpatialCoordinates d → ℝ := fun f x =>
      ∑ k : OddGridIndex d (triadicHalf m),
        (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
          (fun _ => averageOn
            (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
    E (fun x => u x - v x) = fun x => E u x - E v x := by
  dsimp only
  let E : (SpatialCoordinates d → ℝ) → SpatialCoordinates d → ℝ := fun f x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  change E (fun x => u x - v x) = fun x => E u x - E v x
  funext x
  show (∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d))
            (fun x => u x - v x)) x) =
    (∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) u) x) -
    (∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) v) x)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  set W : Set (SpatialCoordinates d) :=
    (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) with hW
  have hsub : W ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [hW]
    exact oddGridCell_subset z hr (triadicHalf m) k
  have huk : IntegrableOn u W volume := hu.mono_set hsub
  have hvk : IntegrableOn v W volume := hv.mono_set hsub
  have havg : averageOn W (fun x => u x - v x) = averageOn W u - averageOn W v := by
    unfold averageOn
    exact volumeAverage_sub huk hvk
  by_cases hx : x ∈ W
  · simp only [Set.indicator_of_mem hx]
    exact havg
  · simp only [Set.indicator_of_notMem hx, sub_zero]

end SubdiffusiveProcess
