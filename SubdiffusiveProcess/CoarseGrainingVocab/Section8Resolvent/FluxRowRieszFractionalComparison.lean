module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszStoppingLimit

@[expose] public section

/-!
# Fractional Gagliardo--Fourier comparison required by the flux row

This file gives an exact Lean statement to the remaining Fourier-analysis
collection.  The Gagliardo kernel includes the paper's leading factor `sigma`,
and the massive terms use the same `R` and frequency base as the proved
Fourier-space Riesz construction.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.Frozen.Section8
open scoped ENNReal

noncomputable section

/-- The scalar Gagliardo kernel of the inverse Fourier transform, including
the normalization factor `sigma` from the paper's seminorm convention. -/
def fluxRowFractionalGagliardoKernel {d : ℕ} (sigma : ℝ)
    (phi : SchwartzMap (Vec d) ℂ) (z : Vec d × Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal <|
    sigma * ‖inverseFourierSchwartz phi z.1 -
      inverseFourierSchwartz phi z.2‖ ^ 2 /
      Real.rpow ‖z.1 - z.2‖ ((d : ℝ) + 2 * sigma)

/-- Squared modulus of the inverse Fourier test field. -/
def fluxRowInverseFourierDensity {d : ℕ}
    (phi : SchwartzMap (Vec d) ℂ) (x : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal ‖inverseFourierSchwartz phi x‖ ^ 2

/-- The exact massive Fourier density against which the global physical
Gagliardo energy must be compared. -/
def fluxRowMassiveFourierEnergyDensity {d : ℕ} (R sigma : ℝ)
    (phi : SchwartzMap (Vec d) ℂ) (xi : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal <|
    Real.rpow (fluxRowMassiveFrequencyBase R xi) sigma * ‖phi xi‖ ^ 2

/-- **Missing fractional Gagliardo--Fourier comparison.**

For each dimension and order there is one constant, uniform in the massive
radius and Schwartz test, which controls the physical Gagliardo energy plus
the massive `L²` term by the massive Fourier energy.  The assertion is kept
in `ENNReal`, so finiteness cannot be hidden by `ENNReal.toReal ∞ = 0`.

This is the precise substantive theorem needed to populate
`FluxRowRieszPartitionInput.globalEnergy_ne_top` and `globalEnergy_le` after
the routine identification of the weighted `L²` norm. -/
def FluxRowFractionalGagliardoFourierComparison (d : ℕ) : Prop :=
  ∀ sigma : ℝ, sigma ∈ Set.Ioo (0 : ℝ) 1 →
    ∃ Csigma : ℝ, 0 < Csigma ∧
      ∀ R : ℝ, 0 < R → ∀ phi : SchwartzMap (Vec d) ℂ,
        fluxRowGlobalPositiveEnergy volume
            (ENNReal.ofReal (Real.rpow R (-2 * sigma)))
            (fluxRowFractionalGagliardoKernel sigma phi)
            (fluxRowInverseFourierDensity phi) ≤
          ENNReal.ofReal Csigma *
            ∫⁻ xi, fluxRowMassiveFourierEnergyDensity R sigma phi xi ∂volume

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
