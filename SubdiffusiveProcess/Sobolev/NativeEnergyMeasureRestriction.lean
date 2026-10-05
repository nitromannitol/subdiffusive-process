module

public import SubdiffusiveProcess.Sobolev.GradientEnergyMeasureIntegral
public import SubdiffusiveProcess.Sobolev.NativeRepresentativeData

@[expose] public section

/-! # Restriction of native energy measures

This file proves that a native coefficient-gradient energy measure restricts
exactly to the local measure of the restricted Sobolev datum. It does not make
any convergence claim about energy measures.
-/

open MeasureTheory Set TopologicalSpace Homogenization
noncomputable section
namespace SubdiffusiveProcess

/-- Restricting a native global energy measure to a cell recovers the exact local Sobolev energy measure. -/
theorem gradientEnergyMeasure_restrict_of_native_data
    {d : ℕ} {Q W : Opens (SpatialCoordinates d)} (hWQ : W ≤ Q)
    (a : PositiveCoefficient Q) (b : PositiveCoefficient W)
    (hab : (a.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (W : Set (SpatialCoordinates d))] b.val)
    (u : H1Function (Q : Set (SpatialCoordinates d))) (v : weakSobolevGraph W)
    (hdata : sobolevDataOfH1 (u.restrict W.isOpen hWQ) = v.val) :
    (gradientEnergyMeasure a (sobolevGradient (sobolevDataOfH1 u))).restrict (W : Set (SpatialCoordinates d)) =
      gradientEnergyMeasure b (sobolevGradient v.val) := by
  rw [gradientEnergyMeasure, MeasureTheory.restrict_withDensity W.isOpen.measurableSet,
    MeasureTheory.Measure.restrict_restrict_of_subset hWQ]
  apply MeasureTheory.withDensity_congr_ae
  let μW := volume.restrict (W : Set (SpatialCoordinates d))
  have hglobalData (i : Fin d) :
      (((sobolevDataOfH1 u).2 i : DomainL2 Q) : SpatialCoordinates d → ℝ) =ᵐ[μW]
        fun x => u.grad x i := by
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset hWQ
      (sobolevDataOfH1_snd_coeFn u i)
  have hlocalData (i : Fin d) :
      (((v.val).2 i : DomainL2 W) : SpatialCoordinates d → ℝ) =ᵐ[μW]
        fun x => u.grad x i := by
    rw [← hdata]
    simpa only [H1Function.restrict] using
      (sobolevDataOfH1_snd_coeFn (u.restrict W.isOpen hWQ) i)
  have hgrad : ∀ᵐ x ∂μW, ∀ i : Fin d,
      (sobolevGradient (sobolevDataOfH1 u)) i x = (sobolevGradient v.val) i x := by
    apply MeasureTheory.ae_all_iff.mpr
    intro i
    filter_upwards [hglobalData i, hlocalData i] with x hxg hxl
    calc
      (sobolevGradient (sobolevDataOfH1 u)) i x = u.grad x i := hxg
      _ = (((v.val).2 i : DomainL2 W) : SpatialCoordinates d → ℝ) x := hxl.symm
      _ = (sobolevGradient v.val) i x := rfl
  filter_upwards [hab, hgrad] with x hcoeff hcoord
  congr 1
  rw [hcoeff]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcoord i]

end SubdiffusiveProcess
