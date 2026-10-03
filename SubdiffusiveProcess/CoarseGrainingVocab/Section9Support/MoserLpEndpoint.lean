module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Order.Lattice

@[expose] public section

/-! # The `L∞` endpoint from uniform bounds at diverging exponents -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Uniform finite-exponent bounds imply the almost-everywhere endpoint bound. -/
theorem moser_ae_bound_of_eLpNorm_bounds {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    {p : ℕ → ℝ} (hp : ∀ n, 0 < p n) (hpinf : Tendsto p atTop atTop)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ n, eLpNorm f (ENNReal.ofReal (p n)) μ ≤ ENNReal.ofReal K) :
    ∀ᵐ x ∂μ, |f x| ≤ K := by
  have hnull (t : ℝ) (ht : K < t) : μ {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} = 0 := by
    have ht0 : 0 < t := hK.trans_lt ht
    have hratio : ENNReal.ofReal K / ENNReal.ofReal t < 1 := by
      rw [ENNReal.div_lt_iff (Or.inl (by positivity : ENNReal.ofReal t ≠ 0))
        (Or.inl ENNReal.ofReal_ne_top), one_mul]
      exact ENNReal.ofReal_lt_ofReal_iff ht0 |>.mpr ht
    have hlim := (ENNReal.tendsto_rpow_atTop_of_base_lt_one hratio).comp hpinf
    apply le_antisymm (ge_of_tendsto' hlim fun n => ?_) bot_le
    have h := meas_ge_le_mul_pow_eLpNorm_enorm (f := f) μ
      (ENNReal.ofReal_pos.mpr (hp n)).ne' ENNReal.ofReal_ne_top
      (by positivity : ENNReal.ofReal t ≠ 0) (by simp)
    rw [ENNReal.toReal_ofReal (hp n).le] at h
    refine h.trans ((mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hbound n) (hp n).le)).trans_eq ?_)
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (hp n).le, div_eq_mul_inv, mul_comm]
    rfl
  have hseq : ∀ n : ℕ, ∀ᵐ x ∂μ, |f x| ≤ K + 1 / ((n : ℝ) + 1) := by
    intro n
    have ht : K < K + 1 / ((n : ℝ) + 1) := lt_add_of_pos_right _ (by positivity)
    have ha : ∀ᵐ x ∂μ, ¬ ENNReal.ofReal (K + 1 / ((n : ℝ) + 1)) ≤ ‖f x‖ₑ := by
      rw [ae_iff]
      simpa only [not_not] using hnull _ ht
    filter_upwards [ha] with x hx
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (le_of_lt (lt_of_not_ge hx))
    simpa only [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (hK.trans ht.le)] using h
  filter_upwards [ae_all_iff.mpr hseq] with x hx
  have hlim : Tendsto (fun n : ℕ => K + 1 / ((n : ℝ) + 1)) atTop (𝓝 K) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => K) atTop (𝓝 K)).add
        tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto' hlim hx

/-- Continuity upgrades an almost-everywhere bound to every point of an open set. -/
theorem moser_pointwise_bound_of_ae {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} [Measure.IsOpenPosMeasure μ]
    {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : ContinuousOn f U)
    {K : ℝ} (hbound : ∀ᵐ x ∂μ.restrict U, |f x| ≤ K) :
    ∀ x ∈ U, |f x| ≤ K := by
  have heq : (fun x => min |f x| K) =ᵐ[μ.restrict U] fun x => |f x| :=
    hbound.mono fun x hx => min_eq_left hx
  have hevery := Measure.eqOn_open_of_ae_eq heq hU (hf.abs.inf continuousOn_const) hf.abs
  intro x hx
  exact (min_eq_left_iff).mp (hevery hx)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
