module

public import SubdiffusiveProcess.Analysis.GlobalTriadicSubtraction

@[expose] public section

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section
namespace SubdiffusiveProcess

theorem globalTriadicAverages_congr_ae
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (f g : SpatialCoordinates d → ℝ)
    (hfg : f =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g) :
    let E : (SpatialCoordinates d → ℝ) → SpatialCoordinates d → ℝ := fun h x =>
      ∑ k : OddGridIndex d (triadicHalf m),
        (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
          (fun _ => averageOn
            (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) h) x
    E f = E g := by
  dsimp only
  funext x
  refine Finset.sum_congr rfl (fun k hk => ?_)
  let W : Set (SpatialCoordinates d) :=
    (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d))
  have hsub : W ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [show W = (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) by rfl]
    exact oddGridCell_subset z hr (triadicHalf m) k
  have hfgW : f =ᵐ[volume.restrict W] g :=
    ae_restrict_of_ae_restrict_of_subset hsub hfg
  have havg : averageOn W f = averageOn W g := by
    unfold averageOn Homogenization.volumeAverage
    rw [MeasureTheory.integral_congr_ae hfgW]
  change W.indicator (fun _ => averageOn W f) x =
    W.indicator (fun _ => averageOn W g) x
  by_cases hx : x ∈ W
  · simpa only [Set.indicator_of_mem hx] using havg
  · simp only [Set.indicator_of_notMem hx]

end SubdiffusiveProcess
