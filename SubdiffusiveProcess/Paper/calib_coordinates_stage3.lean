module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib_stage3_constants
public import SubdiffusiveProcess.Paper.calib_H0_triadic_root_growth
public import SubdiffusiveProcess.Paper.prop_conc_mesh_cutoff_family

@[expose] public section

/-! Stage-3 coordinates of the calibration: for every calibration exponent `k` (cell side `3^{K0+k}`, `K0 ≥ 1`) and every one of the
`3^d` cells of the padded cube, a measurable tight random constant whose `GrowthAt` conclusion holds almost surely.  From
`calib_H0_triadic_root_growth` and `calib_stage3_constants`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- **Stage-3 coordinates.** -/
theorem calib_coordinates_stage3 (d : ℕ) (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), M.delta ≤ δ0 →
      ∀ K0 : ℕ, 1 ≤ K0 →
      ∃ Kc : ℕ × OddGridIndex d (triadicHalf 1) → ℕ → BilateralField d → ℝ,
        (∀ p N, Measurable (Kc p N)) ∧
        (∀ p, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N,
          (chaosSampleLaw M).toMeasure {β | Mb < |Kc p N β|} ≤ ENNReal.ofReal rho) ∧
        ∀ p : ℕ × OddGridIndex d (triadicHalf 1), ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ (r : ℝ) (hr : 0 < r), r = (3 : ℝ) ^ (K0 + p.1) →
            aux_prop_growth_large_root_GrowthAt M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
              (oddGridCenter (0 : SpatialCoordinates d) (3 * (3 : ℝ) ^ (K0 + p.1 + 1) / 3) (triadicHalf 1) p.2) r hr
              t alpha om (fun N => Kc p N om) := by
  obtain ⟨δ0, hδ0, hS3⟩ := calib_H0_triadic_root_growth d hd Jc Pc Xc W Cp Sf t alpha 1 (fun _ => 1) ht htd ha0 ha1
    (fun _ => le_rfl)
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm hδ K0 hK0
  have hp : ∀ p : ℕ × OddGridIndex d (triadicHalf 1), ∃ K : ℕ → BilateralField d → ℝ,
      (∀ N, Measurable (K N)) ∧
      (∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N, (chaosSampleLaw M).toMeasure {β | Mb < |K N β|} ≤ ENNReal.ofReal rho) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        aux_prop_growth_large_root_GrowthAt M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          (oddGridCenter (0 : SpatialCoordinates d) (3 * (3 : ℝ) ^ (K0 + p.1 + 1) / 3) (triadicHalf 1) p.2)
          ((3 : ℝ) ^ (K0 + p.1)) (by positivity) t alpha om (fun N => K N om) := by
    intro p
    obtain ⟨K0', Cb, hGB⟩ := hS3 M Rm hδ (K0 + p.1) (by omega)
      (oddGridCenter (0 : SpatialCoordinates d) (3 * (3 : ℝ) ^ (K0 + p.1 + 1) / 3) (triadicHalf 1) p.2) (by positivity)
    exact calib_stage3_constants M _ _ _ _ t alpha K0' Cb hGB
  choose Kc hKm hKt hKae using hp
  refine ⟨Kc, hKm, hKt, ?_⟩
  intro p
  filter_upwards [hKae p] with om hom
  intro r hr hrj
  subst hrj
  exact hom

end
end SubdiffusiveProcess.Paper
