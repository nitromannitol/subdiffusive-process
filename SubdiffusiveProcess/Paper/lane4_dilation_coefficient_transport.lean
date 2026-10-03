module

public import SubdiffusiveProcess.Lane4.CubeDilation
public import SubdiffusiveProcess.Paper.lane4_dilation_quasi_measure_preserving

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lane4_dilation_coefficient_transport :
  ∀ (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1)
    (a : PositiveCoefficient (centeredCube z r hr)),
    ∃ b : PositiveCoefficient (centeredCube z' 1 h1),
      ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        b.val x = a.val (cubeDilation z z' r x) := by
  intro d z z' r hr h1 a
  have hq := lane4_dilation_quasi_measure_preserving d z z' r hr h1
  -- strong measurability of the composite, through the quasi-measure-preserving map
  have hae : AEStronglyMeasurable
      (fun x => (a.val : SpatialCoordinates d → ℝ) (cubeDilation z z' r x))
      (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) :=
    (Lp.aestronglyMeasurable a.val).comp_quasiMeasurePreserving hq
  -- the essential bound transfers along the same map, with no loss
  have hbound := hq.ae (ae_le_eLpNormEssSup (f := (a.val : SpatialCoordinates d → ℝ))
      (μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
  have hsup : eLpNormEssSup
      (fun x => (a.val : SpatialCoordinates d → ℝ) (cubeDilation z z' r x))
      (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) ≤
      eLpNormEssSup (a.val : SpatialCoordinates d → ℝ)
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    essSup_le_of_ae_le _ hbound
  have hmem : MemLp (fun x => (a.val : SpatialCoordinates d → ℝ) (cubeDilation z z' r x))
      ∞ (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) := by
    change eLpNorm _ ∞ _ < ∞
    rw [eLpNorm_exponent_top hae]
    refine lt_of_le_of_lt hsup ?_
    have := Lp.eLpNorm_lt_top a.val
    rwa [eLpNorm_exponent_top (Lp.aestronglyMeasurable a.val)] at this
  -- and so does the a.e. lower bound, with the *same* constant
  obtain ⟨c, hc, hca⟩ := a.2
  refine ⟨⟨hmem.toLp _, ⟨c, hc, ?_⟩⟩, ?_⟩
  · filter_upwards [hmem.coeFn_toLp, hq.ae hca] with x hx hcx
    rw [hx]; exact hcx
  · filter_upwards [hmem.coeFn_toLp] with x hx
    exact hx

end Paper
