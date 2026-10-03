module

public import SubdiffusiveProcess.MeyersRegularity.Moments

@[expose] public section

/-! Layer-cake bounds for finite truncations, without an integrability assumption. -/

open MeasureTheory Filter Set
open Homogenization
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

variable {α β γ E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [NormedAddCommGroup E]

/-- Three-measure distribution comparison, including a bounded low-level contribution. -/
theorem rpow_moment_le_of_tail {μ : Measure α} {ν : Measure β} {ξ : Measure γ}
    {u : α → ℝ} {v : β → ℝ} {w : γ → ℝ} {r L : ℝ} {κ B : ℝ≥0∞}
    (hu : AEMeasurable u μ) (hv : AEMeasurable v ν) (hw : AEMeasurable w ξ)
    (hu0 : ∀ᵐ x ∂μ, 0 ≤ u x) (hv0 : ∀ᵐ x ∂ν, 0 ≤ v x) (hw0 : ∀ᵐ x ∂ξ, 0 ≤ w x)
    (hr : 0 < r) (hL : 0 ≤ L)
    (htail : ∀ t : ℝ, 0 < t → μ {x | t < u x} ≤
      μ {x | t < L} + κ * (ν {x | t < v x} + B * ξ {x | t < w x})) :
    (∫⁻ x, ENNReal.ofReal (u x ^ r) ∂μ) ≤
      μ univ * ENNReal.ofReal (L^r) + κ *
        ((∫⁻ x, ENNReal.ofReal (v x ^ r) ∂ν) + B * ∫⁻ x, ENNReal.ofReal (w x ^ r) ∂ξ) := by
  have hlayeru := lintegral_rpow_eq_lintegral_meas_lt_mul μ hu0 hu hr
  have hlayerv := lintegral_rpow_eq_lintegral_meas_lt_mul ν hv0 hv hr
  have hlayerw := lintegral_rpow_eq_lintegral_meas_lt_mul ξ hw0 hw hr
  have hlayerL := lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (ae_of_all _ (fun _ => hL)) (aemeasurable_const : AEMeasurable (fun _ : α => L) μ) hr
  let f0 : ℝ → ℝ≥0∞ := fun t => μ {x | t < L}
  let f1 : ℝ → ℝ≥0∞ := fun t => ν {x | t < v x}
  let f2 : ℝ → ℝ≥0∞ := fun t => ξ {x | t < w x}
  let weight : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t^(r-1))
  have hf0 : Measurable f0 := Antitone.measurable (by
    intro s t hst
    exact measure_mono (fun x hx => hst.trans_lt hx))
  have hf1 : Measurable f1 := Antitone.measurable (by
    intro s t hst
    exact measure_mono (fun x hx => hst.trans_lt hx))
  have hf2 : Measurable f2 := Antitone.measurable (by
    intro s t hst
    exact measure_mono (fun x hx => hst.trans_lt hx))
  have hweight : Measurable weight := (measurable_id.pow measurable_const).ennreal_ofReal
  have hmain :
      (∫⁻ t in Ioi (0 : ℝ), μ {x | t < u x} * weight t) ≤
      (∫⁻ t in Ioi (0 : ℝ), f0 t * weight t) + κ *
        ((∫⁻ t in Ioi (0 : ℝ), f1 t * weight t) +
          B * ∫⁻ t in Ioi (0 : ℝ), f2 t * weight t) := by
    calc
      (∫⁻ t in Ioi (0 : ℝ), μ {x | t < u x} * weight t) ≤
          ∫⁻ t in Ioi (0 : ℝ), (f0 t + κ*(f1 t+B*f2 t))*weight t := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        simpa only [f0, f1, f2, mul_comm] using mul_le_mul_right (htail t ht) (weight t)
      _ = _ := by
        simp_rw [add_mul, mul_assoc]
        rw [lintegral_add_left' (f := fun t => f0 t * weight t) (by exact (hf0.mul hweight).aemeasurable.restrict),
          lintegral_const_mul'' κ (f := fun t => (f1 t + B * f2 t) * weight t) (by exact ((hf1.add (measurable_const.mul hf2)).mul hweight).aemeasurable.restrict)]
        simp_rw [add_mul, mul_assoc]
        rw [lintegral_add_left' (f := fun t => f1 t * weight t) (by exact (hf1.mul hweight).aemeasurable.restrict),
          lintegral_const_mul'' B (f := fun t => f2 t * weight t) (by exact (hf2.mul hweight).aemeasurable.restrict)]
  have hh := mul_le_mul_right hmain (ENNReal.ofReal r)
  have heq : ENNReal.ofReal r *
      ((∫⁻ t in Ioi (0 : ℝ), f0 t*weight t) + κ *
        ((∫⁻ t in Ioi (0 : ℝ), f1 t*weight t) + B * ∫⁻ t in Ioi (0 : ℝ), f2 t*weight t)) =
      ENNReal.ofReal r * (∫⁻ t in Ioi (0 : ℝ), f0 t*weight t) + κ *
        (ENNReal.ofReal r * (∫⁻ t in Ioi (0 : ℝ), f1 t*weight t) +
          B * (ENNReal.ofReal r * ∫⁻ t in Ioi (0 : ℝ), f2 t*weight t)) := by ring
  rw [heq] at hh
  change ENNReal.ofReal r * (∫⁻ t in Ioi (0 : ℝ), μ {x | t < u x} * ENNReal.ofReal (t^(r-1))) ≤
    ENNReal.ofReal r * (∫⁻ t in Ioi (0 : ℝ), μ {x | t < L} * ENNReal.ofReal (t^(r-1))) + κ *
    (ENNReal.ofReal r * (∫⁻ t in Ioi (0 : ℝ), ν {x | t < v x} * ENNReal.ofReal (t^(r-1))) +
      B * (ENNReal.ofReal r * ∫⁻ t in Ioi (0 : ℝ), ξ {x | t < w x} * ENNReal.ofReal (t^(r-1)))) at hh
  rw [← hlayeru, ← hlayerL, ← hlayerv, ← hlayerw, lintegral_const, mul_comm (ENNReal.ofReal (L^r))] at hh
  exact hh


/-- A scaled clipped power is a constant multiple of the truncated weighted moment. -/
theorem clipped_rpow_moment_eq {μ : Measure α} {f : α → E} {p T a : ℝ}
    (hf : AEStronglyMeasurable f μ) (hp : 2 < p) (hT : 0 ≤ T) (ha : 0 < a) :
    (∫⁻ x, ENNReal.ofReal ((min ‖f x‖ T / a)^(p-2))
      ∂CubeCalderonZygmund.sqWeightedMeasure f μ) =
      ENNReal.ofReal (a^(p-2))⁻¹ * truncatedMoment μ f p T := by
  unfold truncatedMoment
  have hreal : ∀ x, (min ‖f x‖ T / a)^(p-2) = (a^(p-2))⁻¹ * (min ‖f x‖ T)^(p-2) := by
    intro x
    rw [Real.div_rpow (le_min (norm_nonneg _) hT) ha.le]
    ring
  simp_rw [hreal, ENNReal.ofReal_mul (inv_nonneg.mpr (Real.rpow_nonneg ha.le _)),
    ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos ha _)]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos ha _)))]


end SubdiffusiveProcess.MeyersRegularity
