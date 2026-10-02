import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn

/-! Packaging a global continuous positive function as the concrete positive
coefficient on any bounded cube. The certificate imposes no uniform bound over
a family of coefficients.
-/
open MeasureTheory Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess

/-- The concrete cube coefficient associated to a continuous positive function. -/
def continuousCubeCoefficient {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : SpatialCoordinates d → ℝ) (ha : Continuous a) (hpos : ∀ x, 0 < a x) :
    PositiveCoefficient (centeredCube z r hr) :=
  @normalizedContinuousPositiveCoefficient d (centeredCube z r hr) (closedCube z r hr)
    ⟨centeredCube_subset_closedCube z hr⟩
    ⟨fun x => a x, ha.comp continuous_subtype_val⟩ (fun x => hpos x) 1 zero_lt_one

/-- The packaged coefficient equals the original function almost everywhere on its cube. -/
theorem continuousCubeCoefficient_ae {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : SpatialCoordinates d → ℝ) (ha : Continuous a) (hpos : ∀ x, 0 < a x) :
    ((continuousCubeCoefficient z r hr a ha hpos).val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] a := by
  have hco := @normalizedContinuousPositiveCoefficient_coeFn d (centeredCube z r hr)
    (closedCube z r hr) ⟨centeredCube_subset_closedCube z hr⟩
    ⟨fun x => a x, ha.comp continuous_subtype_val⟩ (fun x => hpos x) 1 zero_lt_one
  filter_upwards [hco, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hmem
  exact (hx hmem).trans (div_one (a x))

end SubdiffusiveProcess
