module

public import SubdiffusiveProcess.Sobolev.WeakGradient
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace SubdiffusiveProcess

/-- The literal Euclidean-kernel fractional square integral depends only on the coordinate almost-everywhere classes, including when the integral is infinite. -/
theorem fractional_square_integral_congr_ae
    {d k : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (f g : Fin k → SpatialCoordinates d → ℝ)
    (hfg : ∀ i, f i =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] g i)
    (s : ℝ) :
    (∫⁻ x in (Ω : Set (SpatialCoordinates d)),
      ∫⁻ y in (Ω : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s)) =
    ∫⁻ x in (Ω : Set (SpatialCoordinates d)),
      ∫⁻ y in (Ω : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k, (g i x - g i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s) := by
  have hfg_all : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      ∀ i, f i x = g i x := ae_all_iff.mpr hfg
  apply lintegral_congr_ae
  filter_upwards [hfg_all] with x hx
  apply lintegral_congr_ae
  filter_upwards [hfg_all] with y hy
  simp only [hx, hy]

end SubdiffusiveProcess
