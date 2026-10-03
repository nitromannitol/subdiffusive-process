module

public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Paper.in_killed_inverse
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Paper.lem_20_product_h10
public import SubdiffusiveProcess.Paper.lem_20_product_leibniz

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal

namespace Paper



theorem lem_20_product
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (u chi : S.space) (uc : SpatialCoordinates d → ℝ)
    (huc : (u.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] uc)
    (hcontinuous : ContinuousOn uc
      (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hchi : ∀ᵐ x ∂(volume.restrict
        (centeredCube z R hR : Set (SpatialCoordinates d))),
      0 ≤ (chi.val.1 : SpatialCoordinates d → ℝ) x ∧
        (chi.val.1 : SpatialCoordinates d → ℝ) x ≤ 1) :
    ∃ prod : S.space,
      (prod.val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          (fun x => uc x * (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x)) ∧
      (∀ i : Fin d, (prod.val.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          (fun x => (1 - (chi.val.1 : SpatialCoordinates d → ℝ) x) *
            (u.val.2 i : SpatialCoordinates d → ℝ) x -
              uc x * (chi.val.2 i : SpatialCoordinates d → ℝ) x)) := by
  obtain ⟨prod, hprod⟩ := Paper.lem_20_product_h10 d hd z R hR S hS u chi uc huc hcontinuous hchi
  exact ⟨prod, hprod, fun i => Paper.lem_20_product_leibniz d hd z R hR S hS u chi uc huc hcontinuous hchi prod hprod i⟩


end Paper
