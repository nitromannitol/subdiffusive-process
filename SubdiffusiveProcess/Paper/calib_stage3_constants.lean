import Mathlib
import SubdiffusiveProcess.Paper.prop_growth_large_root
import SubdiffusiveProcess.Paper.conv_represented_tight_of_bounded

/-! Measurable, tight versions of the random constants of `prop_growth` on a cube (Stage 3 coordinates).  The constants `K_N` of
`aux_prop_growth_large_root_GrowthBody` are only almost-surely measurable (`MemLp`); a measurable version with the same
`GrowthAt` conclusion and tightness (Markov, from the `L¹` bound) is what the represented-sequence extraction needs. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology
namespace Paper
noncomputable section

/-- **Measurable tight majorant with the `GrowthAt` conclusion.** -/
theorem calib_stage3_constants {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t alpha : ℝ)
    (K0 : ℕ → BilateralField d → ℝ) (Cb : Fin 1 → ℝ)
    (hGB : aux_prop_growth_large_root_GrowthBody M H z r hr t alpha 1 (fun _ => (1 : ℝ)) K0 Cb) :
    ∃ K : ℕ → BilateralField d → ℝ, (∀ N, Measurable (K N)) ∧
      (∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N, (chaosSampleLaw M).toMeasure {β | Mb < |K N β|} ≤ ENNReal.ofReal rho) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, aux_prop_growth_large_root_GrowthAt M H z r hr t alpha om (fun N => K N om) := by
  obtain ⟨hmem, hbd, -, hG⟩ := hGB
  have hmem1 : ∀ N, MemLp (K0 N) 1 (chaosSampleLaw M).toMeasure := fun N => by
    simpa using hmem 0 N
  have hbd1 : ∀ N, eLpNorm (K0 N) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cb 0) := fun N => by
    simpa using hbd 0 N
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → BilateralField d → ℝ, K = fun N => (hmem1 N).1.mk (K0 N) := ⟨_, rfl⟩
  have hKm : ∀ N, Measurable (K N) := fun N => by
    rw [hKdef]; exact (hmem1 N).1.stronglyMeasurable_mk.measurable
  have hKae : ∀ N, K0 N =ᵐ[(chaosSampleLaw M).toMeasure] K N := fun N => by
    rw [hKdef]; exact (hmem1 N).1.ae_eq_mk
  refine ⟨K, hKm, ?_, ?_⟩
  · have hB : ∀ N, ∫⁻ ω, ‖K N ω‖ₑ ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (max (Cb 0) 0) := fun N => by
      have h1 : eLpNorm (K N) 1 (chaosSampleLaw M).toMeasure = eLpNorm (K0 N) 1 (chaosSampleLaw M).toMeasure :=
        eLpNorm_congr_ae (hKae N).symm
      rw [← eLpNorm_one_eq_lintegral_enorm, h1]
      exact (hbd1 N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    exact aux_conv_represented_tight_of_bounded_L1_bounded (chaosSampleLaw M).toMeasure K hKm (max (Cb 0) 0)
      (le_max_right _ _) hB
  · filter_upwards [hG, ae_all_iff.2 hKae] with om hom heq
    have hfun : (fun N => K0 N om) = fun N => K N om := funext heq
    rw [← hfun]
    exact hom

end
end Paper
