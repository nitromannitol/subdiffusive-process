module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeWeightedVolumeReadout
public import Mathlib.Topology.Instances.NNReal.Lemmas

@[expose] public section

/-!
# Positivity and finiteness of bounded weighted masses

The Section 9 logarithmic mass ratios require the underlying extended nonnegative integrals
to be nonzero and finite.  This file isolates the exact measure-theoretic criterion used for
positive locally bounded coefficients on finite positive-volume sets.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Alpha : Type*} [MeasurableSpace Alpha]

/-- A measurable positive density that is bounded on a set of positive finite measure has a
nonzero finite weighted mass there.

For the source coefficient, positivity comes from its exponential definition and local
boundedness comes from continuity on the closure of a ball or cube.

Source: the logarithmic weighted-mass readouts -/
theorem setLIntegral_ne_zero_and_ne_top_of_pos_of_le (mu : Measure Alpha)
    (s : Set Alpha) (f : Alpha → ENNReal) (hf : Measurable f)
    (hmuZero : mu s ≠ 0) (hmuTop : mu s ≠ ∞)
    (hpos : ∀ x ∈ s, f x ≠ 0) (M : NNReal)
    (hle : ∀ x ∈ s, f x ≤ M) :
    (∫⁻ x in s, f x ∂mu) ≠ 0 ∧ (∫⁻ x in s, f x ∂mu) ≠ ∞ := by
  constructor
  · apply ne_of_gt
    rw [setLIntegral_pos_iff hf]
    have hsupport : Function.support f ∩ s = s := by
      ext x
      constructor
      · exact fun hx ↦ hx.2
      · intro hx
        exact ⟨hpos x hx, hx⟩
    rw [hsupport]
    exact pos_iff_ne_zero.mpr hmuZero
  · exact ne_of_lt (setLIntegral_lt_top_of_le_nnreal hmuTop ⟨M, hle⟩)

variable [TopologicalSpace Alpha] [BorelSpace Alpha]

/-- A continuous positive real density has positive finite weighted mass on every set of
positive finite measure with compact closure.

This directly supplies the real-readout hypotheses for bounded balls and cubes once their
standard volume facts are available.
-/
theorem setLIntegral_ofReal_ne_zero_and_ne_top_of_compact_closure
    (mu : Measure Alpha) (s : Set Alpha) (f : Alpha → ℝ)
    (hf : Continuous f) (hsCompact : IsCompact (closure s))
    (hmuZero : mu s ≠ 0) (hmuTop : mu s ≠ ∞)
    (hpos : ∀ x ∈ s, 0 < f x) :
    (∫⁻ x in s, ENNReal.ofReal (f x) ∂mu) ≠ 0 ∧
      (∫⁻ x in s, ENNReal.ofReal (f x) ∂mu) ≠ ∞ := by
  have hmeas : Measurable fun x ↦ ENNReal.ofReal (f x) :=
    (ENNReal.continuous_ofReal.comp hf).measurable
  constructor
  · apply ne_of_gt
    rw [setLIntegral_pos_iff hmeas]
    have hsupport : Function.support (fun x ↦ ENNReal.ofReal (f x)) ∩ s = s := by
      ext x
      constructor
      · exact fun hx ↦ hx.2
      · intro hx
        exact ⟨ENNReal.ofReal_ne_zero_iff.mpr (hpos x hx), hx⟩
    rw [hsupport]
    exact pos_iff_ne_zero.mpr hmuZero
  · have hcontinuousNNReal : Continuous fun x ↦ Real.toNNReal (f x) :=
      continuous_real_toNNReal.comp hf
    have hbddClosure : BddAbove ((fun x ↦ Real.toNNReal (f x)) '' closure s) :=
      (hsCompact.image hcontinuousNNReal).bddAbove
    have hbdd : BddAbove ((fun x ↦ Real.toNNReal (f x)) '' s) :=
      hbddClosure.mono (image_mono subset_closure)
    exact ne_of_lt (setLIntegral_lt_top_of_bddAbove hmuTop hbdd)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
