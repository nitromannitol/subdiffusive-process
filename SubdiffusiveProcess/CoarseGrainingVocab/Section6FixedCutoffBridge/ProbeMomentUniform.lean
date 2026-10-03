module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.ProbeSubadditivity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.ResponseStationarity
public import Mathlib.Analysis.MeanInequalitiesPow

@[expose] public section

/-!
# Moments of the probe form, uniform in the cube scale

The `L^p` route needs a moment bound for `cutoffProbeForm` on the centered cube
of scale `n` that does **not** grow with `n`.  §46's
`memLp_cutoffResponseOnCube` is proved through a *supremum* envelope over the
cube, whose `xi`-th moment grows like `exp(c xi^2 n)`; that growth is fatal to
the assembly.

The fix uses only landed material:

* `cutoffProbeForm_le_descendantsAverage` (subdivision subadditivity) writes the
  scale-`n` probe form below the average of the `3^{dn}` unit-scale ones;
* `Real.rpow_arith_mean_le_arith_mean_rpow` (Jensen for a finite average, no
  measure theory) raises that to the `xi`-th power;
* `integral_abs_cutoffResponseOnCube_rpow_eq_originCube` (§65) identifies every
  unit-scale moment with the moment on the centred unit cube.

The result is a moment bound that is *the same at every nonnegative scale*.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Integrability of the `xi`-th power of the probe form. -/
theorem integrable_cutoffProbeForm_rpow [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (alpha : ℝ)
    (R : TriadicCube d) (v : Vec d) {xi : ℝ} (hxi : 1 ≤ xi) :
    Integrable (fun omega =>
      (cutoffProbeForm M L alpha R omega v) ^ xi) M.P.toMeasure := by
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  have hmem := memLp_cutoffResponseOnCube M L ((Real.sqrt alpha)⁻¹ • v)
    (Real.sqrt alpha • v) R hxi
  have hint := hmem.integrable_norm_rpow
    (by simpa using (ENNReal.ofReal_pos.mpr hxi0).ne') ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hxi0.le] at hint
  refine hint.congr ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs]
  exact congrArg (fun t : ℝ => t ^ xi)
    (abs_of_nonneg (cutoffProbeForm_nonneg M L alpha R omega v))

/-- Every triadic cube of scale zero carries the same probe moment as the
centred unit cube. -/
theorem integral_cutoffProbeForm_rpow_eq_originCube [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (alpha : ℝ)
    (R : TriadicCube d) (v : Vec d) (xi : ℝ) :
    (∫ omega, (cutoffProbeForm M L alpha R omega v) ^ xi ∂M.P.toMeasure) =
      ∫ omega, (cutoffProbeForm M L alpha
        (originCube d R.scale) omega v) ^ xi ∂M.P.toMeasure := by
  have habs : ∀ (S : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
      (cutoffProbeForm M L alpha S omega v) ^ xi =
        |cutoffResponseOnCube M L ((Real.sqrt alpha)⁻¹ • v)
          (Real.sqrt alpha • v) S omega| ^ xi := by
    intro S omega
    exact (congrArg (fun t : ℝ => t ^ xi)
      (abs_of_nonneg (cutoffProbeForm_nonneg M L alpha S omega v))).symm
  simp only [habs]
  exact integral_abs_cutoffResponseOnCube_rpow_eq_originCube M L
    ((Real.sqrt alpha)⁻¹ • v) (Real.sqrt alpha • v) R xi

/-- **Scale-uniform moments of the probe form.**

At every nonnegative scale `n`, the `xi`-th moment of the probe form on the
centred cube of scale `n` is at most the moment on the centred unit cube. -/
theorem integral_cutoffProbeForm_rpow_originCube_le [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) (n : ℕ) (v : Vec d) {xi : ℝ} (hxi : 1 ≤ xi) :
    (∫ omega, (cutoffProbeForm M L alpha (originCube d (n : ℤ)) omega v) ^ xi
        ∂M.P.toMeasure) ≤
      ∫ omega, (cutoffProbeForm M L alpha (originCube d (0 : ℤ)) omega v) ^ xi
        ∂M.P.toMeasure := by
  classical
  set Q : TriadicCube d := originCube d (n : ℤ) with hQ
  set D : Finset (TriadicCube d) := descendantsAtDepth Q n with hD
  have hcardpos : (0 : ℝ) < (D.card : ℝ) := by
    rw [hD, Homogenization.descendantsAtDepth_card]
    positivity
  have hcardne : (D.card : ℝ) ≠ 0 := ne_of_gt hcardpos
  have hscale0 : ∀ R ∈ D, R.scale = (0 : ℤ) := by
    intro R hR
    have := Homogenization.scale_eq_sub_of_mem_descendantsAtDepth hR
    rw [this, hQ]
    simp [Homogenization.originCube]
  have hxi0 : (0 : ℝ) ≤ xi := le_trans zero_le_one hxi
  -- pointwise bound
  have hpoint : ∀ omega,
      (cutoffProbeForm M L alpha Q omega v) ^ xi ≤
        ∑ R ∈ D, (D.card : ℝ)⁻¹ * (cutoffProbeForm M L alpha R omega v) ^ xi := by
    intro omega
    have hsub := cutoffProbeForm_le_descendantsAverage M L halpha Q n omega v
    have hsum : Homogenization.descendantsAverage Q n
        (fun R => cutoffProbeForm M L alpha R omega v) =
        ∑ R ∈ D, (D.card : ℝ)⁻¹ * cutoffProbeForm M L alpha R omega v := by
      simp only [Homogenization.descendantsAverage, hD, Finset.mul_sum]
    rw [hsum] at hsub
    have hstep1 : (cutoffProbeForm M L alpha Q omega v) ^ xi ≤
        (∑ R ∈ D, (D.card : ℝ)⁻¹ * cutoffProbeForm M L alpha R omega v) ^ xi :=
      Real.rpow_le_rpow (cutoffProbeForm_nonneg M L alpha Q omega v) hsub hxi0
    refine hstep1.trans ?_
    refine Real.rpow_arith_mean_le_arith_mean_rpow D
      (fun _ => (D.card : ℝ)⁻¹)
      (fun R => cutoffProbeForm M L alpha R omega v)
      (fun R _ => by positivity) ?_
      (fun R _ => cutoffProbeForm_nonneg M L alpha R omega v) hxi
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  -- integrate
  have hintL := integrable_cutoffProbeForm_rpow M L alpha Q v hxi
  have hintR : Integrable (fun omega =>
      ∑ R ∈ D, (D.card : ℝ)⁻¹ *
        (cutoffProbeForm M L alpha R omega v) ^ xi) M.P.toMeasure :=
    integrable_finset_sum _ fun R _ =>
      (integrable_cutoffProbeForm_rpow M L alpha R v hxi).const_mul _
  have hmono := integral_mono hintL hintR hpoint
  refine hmono.trans (le_of_eq ?_)
  rw [integral_finset_sum _ fun R _ =>
    (integrable_cutoffProbeForm_rpow M L alpha R v hxi).const_mul _]
  have hterm : ∀ R ∈ D,
      (∫ omega, (D.card : ℝ)⁻¹ *
          (cutoffProbeForm M L alpha R omega v) ^ xi ∂M.P.toMeasure) =
        (D.card : ℝ)⁻¹ *
          ∫ omega, (cutoffProbeForm M L alpha (originCube d (0 : ℤ)) omega v) ^ xi
            ∂M.P.toMeasure := by
    intro R hR
    rw [integral_const_mul,
      integral_cutoffProbeForm_rpow_eq_originCube M L alpha R v xi,
      hscale0 R hR]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
    ← mul_assoc]
  field_simp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
