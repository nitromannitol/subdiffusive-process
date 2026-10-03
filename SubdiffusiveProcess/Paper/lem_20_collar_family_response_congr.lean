module

public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Sobolev.ResponseSpace

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_20_collar_family_response_congr
    (d : ℕ) (Ω : Opens (SpatialCoordinates d))
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (u v : S.space)
    (hvalue : (u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))]
      (v.val.1 : SpatialCoordinates d → ℝ))
    (hgrad : ∀ i : Fin d,
      (u.val.2 i : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (Ω : Set (SpatialCoordinates d))]
        (v.val.2 i : SpatialCoordinates d → ℝ)) :
    responseForm S a u u = responseForm S a v v := by
  rw [responseForm_apply S a u u, responseForm_apply S a v v]
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [hgrad i] with x hx
  rw [hx]

end Paper
