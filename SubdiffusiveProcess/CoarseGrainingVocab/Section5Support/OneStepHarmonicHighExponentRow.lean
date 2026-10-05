module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHarmonicGainCarrier

@[expose] public section

/-!
# One-row high-exponent harmonic localization

This module converts the selected `L^(16d)` harmonic-gradient gain from its
`ENNReal` form to the normalized real `cubeLpNorm` form used by the one-step
cell estimates.  The theorem is deliberately phrased for an arbitrary
harmonic `H1Function`: specializing it to a weak-Hessian row is a separate,
lightweight operation and does not unfold the dependent Hessian carrier.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- A coordinate of the gradient of a harmonic function inherits the chosen
normalized `L^(16d)` interior gain. -/
theorem oneStepHarmonic_gain_row_bound
    (d : ℕ) (hd : 3 ≤ d) (Q : TriadicCube d)
    (v : H1Function (openCubeSet Q))
    (hv : WeakPoissonEquationOn (openCubeSet Q) v (fun _ => 0))
    (j : Fin d) :
    MemLp (fun x => v.grad x j)
        (oneStepHarmonicExponent d hd).exponent
        (normalizedCubeMeasure
          (CubeCalderonZygmund.centralDescendant Q
            (oneStepHarmonicGainDepth d hd))) ∧
      cubeLpNorm
          (CubeCalderonZygmund.centralDescendant Q
            (oneStepHarmonicGainDepth d hd))
          (oneStepHarmonicExponent d hd).exponent
          (fun x => v.grad x j) ≤
        oneStepHarmonicGainConstant d hd *
          ∑ k : Fin d, cubeLpNorm Q 2 (fun x => v.grad x k) := by
  refine ⟨oneStepHarmonicGain_memLp d hd Q v hv j, ?_⟩
  have hbound := oneStepHarmonicGain_bound d hd Q v hv j
  have hrightTop :
      (ENNReal.ofReal (oneStepHarmonicGainConstant d hd) *
        ∑ k : Fin d, eLpNorm (fun x => v.grad x k) 2
          (normalizedCubeMeasure Q)) ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.sum_ne_top.2 fun k _ =>
        (v.grad_memL2_normalizedCubeMeasure k).eLpNorm_ne_top)
  have hreal := ENNReal.toReal_mono hrightTop hbound
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (oneStepHarmonicGainConstant_pos d hd).le,
    ENNReal.toReal_sum (fun k _ =>
      (v.grad_memL2_normalizedCubeMeasure k).eLpNorm_ne_top)] at hreal
  simpa [cubeLpNorm] using hreal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
