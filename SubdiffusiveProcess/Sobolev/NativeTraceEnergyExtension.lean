import SubdiffusiveProcess.Sobolev.ContinuousNativeZeroExtension
import SubdiffusiveProcess.Sobolev.ZeroExtensionEnergyMeasure

/-! # Native trace energy extension

This module combines continuous native zero extension with preservation of the
whole gradient energy measure. It makes no additional regularity claim.
-/

open MeasureTheory Set TopologicalSpace Homogenization
noncomputable section
namespace SubdiffusiveProcess

/-- A continuous boundary-zero native function extends to a larger domain while preserving its full energy measure when the coefficients agree on the original domain. -/
theorem exists_continuous_native_energy_extension
    {d : ℕ} {V Q : Opens (SpatialCoordinates d)} (hVQ : V ≤ Q)
    (a : PositiveCoefficient Q) (b : PositiveCoefficient V)
    (hab : (a.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] b.val)
    (v : H10Function (V : Set (SpatialCoordinates d)))
    (hcont : ContinuousOn v.toH1Function.toFun (closure (V : Set (SpatialCoordinates d))))
    (hzero : ∀ x ∈ frontier (V : Set (SpatialCoordinates d)), v.toH1Function.toFun x = 0) :
    ∃ w : H10Function (Q : Set (SpatialCoordinates d)),
      Continuous w.toH1Function.toFun ∧
      EqOn w.toH1Function.toFun v.toH1Function.toFun (closure (V : Set (SpatialCoordinates d))) ∧
      (∀ x ∉ (V : Set (SpatialCoordinates d)), w.toH1Function.toFun x = 0) ∧
      gradientEnergyMeasure a (sobolevGradient (sobolevDataOfH1 w.toH1Function)) =
        gradientEnergyMeasure b (sobolevGradient (sobolevDataOfH1 v.toH1Function)) := by
  obtain ⟨w, hwcont, hdata, hwagree, hwzero⟩ :=
    exists_continuous_native_zero_extension hVQ v hcont hzero
  refine ⟨w, hwcont, hwagree, hwzero, ?_⟩
  rw [hdata]
  exact gradientEnergyMeasure_zeroExtensionSobolevData hVQ a b hab
    (sobolevDataOfH1 v.toH1Function)

end SubdiffusiveProcess
