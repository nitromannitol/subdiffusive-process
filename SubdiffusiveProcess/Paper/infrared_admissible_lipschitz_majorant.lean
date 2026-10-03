module

public import SubdiffusiveProcess.Paper.infrared_characterization_local_lipschitz_majorant
public import SubdiffusiveProcess.Paper.truncation_local_lipschitz_majorant
public import SubdiffusiveProcess.Main.InfraredAdmissible
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

/-!
# Local Lipschitz majorant of every admissible infrared field

The characterized field (`infrared_characterization_local_lipschitz_majorant`) and every finite
truncation (`truncation_local_lipschitz_majorant`, uniform in the truncation level) have a local
Lipschitz majorant with `L^p` norm at most `C δ √p`; one constant `C` serves both.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric Filter
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess

noncomputable section
namespace Paper

theorem infrared_admissible_lipschitz_majorant :
  ∀ (d : ℕ), 2 ≤ d →
  ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
  ∀ (p : ℝ), 1 ≤ p →
  ∃ C : ℝ, 0 < C ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H →
      ∃ G : BilateralField d → ℝ,
        (∀ om, 0 ≤ G om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
            y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
            |H om x - H om y| ≤ G om * dist x y) ∧
        MemLp G (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        eLpNorm G (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C * M.delta * Real.sqrt p) := by
  intro d hd instMeas instBorel z r hr p hp
  obtain ⟨C1, hC1, h1⟩ := infrared_characterization_local_lipschitz_majorant d hd z r hr p hp
  obtain ⟨C2, hC2, h2⟩ := truncation_local_lipschitz_majorant d hd z r hr p hp
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, ?_⟩
  intro M H hH
  have hδ : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hsp : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  rcases hH with hH | ⟨L, rfl⟩
  · obtain ⟨G, hG0, hGae, hGmem, hGnorm⟩ := h1 M H hH
    exact ⟨G, hG0, hGae, hGmem, hGnorm.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ) hsp))⟩
  · obtain ⟨G, hG0, hGae, hGmem, hGnorm⟩ := h2 M L
    exact ⟨G, hG0, hGae, hGmem, hGnorm.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ) hsp))⟩

end Paper
