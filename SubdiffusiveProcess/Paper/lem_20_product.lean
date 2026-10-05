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

namespace SubdiffusiveProcess.Paper

/-- The product construction and its identity.
- `in_killed_inverse`: u belongs to the actual killed Sobolev graph.
- `prop_growth`: uc is its continuous representative on the closed cube;
  compactness of that cube supplies boundedness inside this construction.
- `lem_cutoffs`: chi belongs to the same killed graph and 0 <= chi <= 1.
- CONCLUDED: existence in H1_0 of u(1-chi), its value and every coordinate
  of its weak gradient. No product membership or Leibniz rule is assumed.
- The response space is pinned by hS, and huc pins the representative.
  This is the one-index construction used for each r,n by the parent.
  
-/
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
  obtain ⟨prod, hprod⟩ := _root_.SubdiffusiveProcess.Paper.lem_20_product_h10 d hd z R hR S hS u chi uc huc hcontinuous hchi
  exact ⟨prod, hprod, fun i => _root_.SubdiffusiveProcess.Paper.lem_20_product_leibniz d hd z R hR S hS u chi uc huc hcontinuous hchi prod hprod i⟩


end SubdiffusiveProcess.Paper
