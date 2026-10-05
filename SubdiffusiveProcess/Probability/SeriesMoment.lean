module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

/-! `L^q` moment bounds for a discounted countable series of `sup'`s over finite index sets, on a
probability space. Establishes no new mathematics beyond the standard Minkowski inequality for
`L^q` (`eLpNorm_sum_le`) and monotone-limit control of `L^q` norms along an a.e. convergent,
`L^q`-norm-bounded sequence (`MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto`); it packages them for a
term-by-term-dominated countable series of finite maxima, which is not otherwise in Mathlib. Does
not claim anything about compactness. -/

open MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess

/-- Minkowski's inequality for a countable sum of functions, at any exponent `q ≥ 1` on a
probability space: if each term's `L^q` norm is bounded by a summable nonnegative sequence `b`,
the (pointwise) `tsum` is `MemLp` at `q` and its `L^q` norm is bounded by `∑' b`. -/
theorem eLpNorm_tsum_le_of_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (b : ℕ → ℝ) (q : ℝ) (hq : 1 ≤ q)
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hfb : ∀ n, eLpNorm (f n) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (b n)) :
    MemLp (fun ω => ∑' n, f n ω) (ENNReal.ofReal q) μ ∧
      eLpNorm (fun ω => ∑' n, f n ω) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (∑' n, b n) := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  have hfb1 : ∀ n, eLpNorm (f n) 1 μ ≤ ENNReal.ofReal (b n) := fun n =>
    (eLpNorm_le_eLpNorm_of_exponent_le hq1).trans (hfb n)
  have htail : (∀ᵐ ω ∂μ, Summable fun n => f n ω) ∧
      AEStronglyMeasurable (fun ω => ∑' n, f n ω) μ := by
    have hint : ∀ H : ℕ, ∫⁻ ω, ∑' i, ‖f (i + H) ω‖ₑ ∂μ ≤ ENNReal.ofReal (∑' i, b (i + H)) := by
      intro H
      rw [lintegral_tsum (fun i => (hfm (i + H)).enorm)]
      calc ∑' i, ∫⁻ ω, ‖f (i + H) ω‖ₑ ∂μ ≤ ∑' i, ENNReal.ofReal (b (i + H)) :=
            ENNReal.tsum_le_tsum (fun i => by
              rw [← eLpNorm_one_eq_lintegral_enorm (hfm (i + H))]; exact hfb1 (i + H))
        _ = ENNReal.ofReal (∑' i, b (i + H)) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun i => hb0 (i + H))
              ((summable_nat_add_iff H).2 hb)).symm
    have hfin : ∀ᵐ ω ∂μ, ∑' j, ‖f j ω‖ₑ < ⊤ := by
      have h0 := hint 0
      simp only [add_zero] at h0
      exact ae_lt_top' (AEMeasurable.tsum (fun j => (hfm j).enorm))
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h0)
    have hsumm : ∀ᵐ ω ∂μ, Summable fun j => f j ω := by
      filter_upwards [hfin] with ω hω
      apply Summable.of_norm
      have := ENNReal.summable_toReal hω.ne
      simpa using this
    refine ⟨hsumm, ?_⟩
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun H ω => ∑ j ∈ Finset.range H, f j ω)
      (fun H => by
        have e : (fun ω => ∑ j ∈ Finset.range H, f j ω) = ∑ j ∈ Finset.range H, f j := by
          funext ω; rw [Finset.sum_apply]
        show AEStronglyMeasurable (fun ω => ∑ j ∈ Finset.range H, f j ω) μ
        rw [e]
        exact Finset.aestronglyMeasurable_sum (Finset.range H) (fun j _ => hfm j)) ?_
    filter_upwards [hsumm] with ω hω
    exact hω.hasSum.tendsto_sum_nat
  obtain ⟨hsumm, hmeas⟩ := htail
  set S : ℕ → Ω → ℝ := fun H ω => ∑ n ∈ Finset.range H, f n ω with hSdef
  have hSm : ∀ H, AEStronglyMeasurable (S H) μ := by
    intro H
    have e : S H = ∑ n ∈ Finset.range H, f n := by
      funext ω; simp [hSdef, Finset.sum_apply]
    rw [e]
    exact Finset.aestronglyMeasurable_sum _ (fun n _ => hfm n)
  have hSbound : ∀ H : ℕ, eLpNorm (S H) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (∑' n, b n) := by
    intro H
    have h1 : eLpNorm (S H) (ENNReal.ofReal q) μ ≤
        ∑ n ∈ Finset.range H, eLpNorm (f n) (ENNReal.ofReal q) μ := by
      have e : S H = ∑ n ∈ Finset.range H, f n := by
        funext ω; simp [hSdef, Finset.sum_apply]
      rw [e]
      exact eLpNorm_sum_le hq1
    have h2 : ∑ n ∈ Finset.range H, eLpNorm (f n) (ENNReal.ofReal q) μ ≤
        ∑ n ∈ Finset.range H, ENNReal.ofReal (b n) := Finset.sum_le_sum (fun n _ => hfb n)
    have h3 : ∑ n ∈ Finset.range H, ENNReal.ofReal (b n) =
        ENNReal.ofReal (∑ n ∈ Finset.range H, b n) :=
      (ENNReal.ofReal_sum_of_nonneg (fun n _ => hb0 n)).symm
    have h4 : (∑ n ∈ Finset.range H, b n) ≤ ∑' n, b n :=
      hb.sum_le_tsum (Finset.range H) (fun n _ => hb0 n)
    calc eLpNorm (S H) (ENNReal.ofReal q) μ
        ≤ ∑ n ∈ Finset.range H, eLpNorm (f n) (ENNReal.ofReal q) μ := h1
      _ ≤ ∑ n ∈ Finset.range H, ENNReal.ofReal (b n) := h2
      _ = ENNReal.ofReal (∑ n ∈ Finset.range H, b n) := h3
      _ ≤ ENNReal.ofReal (∑' n, b n) := ENNReal.ofReal_le_ofReal h4
  have htendsto : ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun H => S H ω) Filter.atTop (nhds (∑' n, f n ω)) := by
    filter_upwards [hsumm] with ω hω
    simpa [hSdef] using hω.hasSum.tendsto_sum_nat
  have hbound_ev : ∀ᶠ H in (Filter.atTop : Filter ℕ),
      eLpNorm (S H) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (∑' n, b n) :=
    Filter.Eventually.of_forall hSbound
  have hle : eLpNorm (fun ω => ∑' n, f n ω) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (∑' n, b n) :=
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto hbound_ev hSm hmeas htendsto
  exact ⟨lt_of_le_of_lt hle ENNReal.ofReal_lt_top, hle⟩

/-- `L^q` moment bound on the `sup'` over a finite index set, from a uniform per-element bound. -/
theorem eLpNorm_sup'_le_of_le
    {Ω α : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Finset α) (hD : D.Nonempty) (V : α → Ω → ℝ) (hVnonneg : ∀ a ω, 0 ≤ V a ω)
    (hVm : ∀ a ∈ D, AEStronglyMeasurable (V a) μ)
    (C q : ℝ) (hq : 1 < q)
    (hVq : ∀ a ∈ D, eLpNorm (V a) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun ω => D.sup' hD (fun a => V a ω)) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal ((D.card : ℝ) ^ (1 / q) * max C 0) := by
  have hq0 : 0 < q := by linarith
  have hqE0 : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  have hqtop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0.le
  let : Fintype {a // a ∈ D} := inferInstance
  have hcard : Fintype.card {a // a ∈ D} = D.card := by simp [Fintype.card_coe]
  have hYnn : ∀ ω, 0 ≤ D.sup' hD (fun a => V a ω) :=
    fun ω => hD.elim (fun a ha => (hVnonneg a ω).trans (Finset.le_sup' (fun a => V a ω) ha))
  have hYm : AEStronglyMeasurable (fun ω => D.sup' hD (fun a => V a ω)) μ := by
    classical
    let g : α → Ω → ℝ := fun a => if h : a ∈ D then (hVm a h).mk (V a) else 0
    have hg : ∀ a ∈ D, Measurable (g a) := by
      intro a ha
      simp only [g, dite_eq_left ha]
      exact (hVm a ha).stronglyMeasurable_mk.measurable
    refine ⟨fun ω => D.sup' hD (fun a => g a ω), ?_, ?_⟩
    · have hm : Measurable (D.sup' hD g) := Finset.measurable_sup' hD hg
      have heq : (fun ω => D.sup' hD (fun a => g a ω)) = D.sup' hD g := by
        funext ω; rw [Finset.sup'_apply]
      rw [heq]; exact hm.stronglyMeasurable
    · have hall : ∀ᵐ ω ∂μ, ∀ a ∈ D, V a ω = g a ω := by
        rw [Filter.eventually_all_finset]
        intro a ha
        filter_upwards [(hVm a ha).ae_eq_mk] with ω ho
        simp only [g, dite_eq_left ha]; exact ho
      filter_upwards [hall] with ω ho
      exact Finset.sup'_congr hD rfl (fun a ha => ho a ha)
  have hYle : ∀ ω : Ω, ‖D.sup' hD (fun a => V a ω)‖ₑ ^ q ≤
      ∑ a ∈ D, ‖V a ω‖ₑ ^ q := by
    intro ω
    have h := Finset.exists_mem_eq_sup' hD (fun a => V a ω)
    obtain ⟨i, hi, hival⟩ := h
    have hl : ‖D.sup' hD (fun a => V a ω)‖ₑ ^ q = ENNReal.ofReal (V i ω) ^ q := by
      rw [hival, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hVnonneg i ω)]
    have hr : ∀ a, ‖V a ω‖ₑ ^ q = ENNReal.ofReal (V a ω) ^ q := fun a => by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hVnonneg a ω)]
    rw [hl]
    calc ENNReal.ofReal (V i ω) ^ q ≤ ∑ a ∈ D, ENNReal.ofReal (V a ω) ^ q :=
          Finset.single_le_sum (f := fun a => ENNReal.ofReal (V a ω) ^ q)
            (fun a _ => by positivity) hi
      _ = ∑ a ∈ D, ‖V a ω‖ₑ ^ q := by
          refine Finset.sum_congr rfl (fun a _ => (hr a).symm)
  have h3 : ∀ a ∈ D, ∫⁻ ω, ‖V a ω‖ₑ ^ q ∂μ ≤ ENNReal.ofReal (max C 0) ^ q := by
    intro a ha
    have h := hVq a ha
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqE0 hqtop (hVm a ha), hqr] at h
    have h' : (∫⁻ ω, ‖V a ω‖ₑ ^ q ∂μ) ^ (1 / q) ≤ ENNReal.ofReal (max C 0) :=
      h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have := ENNReal.rpow_le_rpow h' hq0.le
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one] at this
  have h2 : ∫⁻ ω, ‖D.sup' hD (fun a => V a ω)‖ₑ ^ q ∂μ ≤
      (D.card : ℝ≥0∞) * ENNReal.ofReal (max C 0) ^ q := by
    calc ∫⁻ ω, ‖D.sup' hD (fun a => V a ω)‖ₑ ^ q ∂μ
        ≤ ∫⁻ ω, ∑ a ∈ D, ‖V a ω‖ₑ ^ q ∂μ := lintegral_mono hYle
      _ = ∑ a ∈ D, ∫⁻ ω, ‖V a ω‖ₑ ^ q ∂μ :=
          lintegral_finsetSum' _ (fun a ha => ((hVm a ha).enorm.pow_const q))
      _ ≤ ∑ _a ∈ D, ENNReal.ofReal (max C 0) ^ q := Finset.sum_le_sum h3
      _ = (D.card : ℝ≥0∞) * ENNReal.ofReal (max C 0) ^ q := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqE0 hqtop hYm, hqr]
  calc (∫⁻ ω, ‖D.sup' hD (fun a => V a ω)‖ₑ ^ q ∂μ) ^ (1 / q)
      ≤ ((D.card : ℝ≥0∞) * ENNReal.ofReal (max C 0) ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow h2 (by positivity)
    _ = ENNReal.ofReal ((D.card : ℝ) ^ (1 / q) * max C 0) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hq0.ne', ENNReal.rpow_one,
          ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg (by positivity)
            (by positivity)]
        simp

/-- Combine `eLpNorm_sup'_le_of_le` termwise with `eLpNorm_tsum_le_of_le` to bound the `L^q`
moment of a discounted series of `sup'`s, given the (deterministic) summability of the
discounted-and-domination-inflated bound. -/
theorem eLpNorm_tsum_sup'_le
    {Ω α : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Finset α) (hD : ∀ n, (D n).Nonempty)
    (V : ℕ → α → Ω → ℝ) (hVnonneg : ∀ n a ω, 0 ≤ V n a ω)
    (hVm : ∀ n a, a ∈ D n → AEStronglyMeasurable (V n a) μ)
    (w C : ℕ → ℝ) (q : ℝ) (hq : 1 < q) (hw : ∀ n, 0 ≤ w n)
    (hVq : ∀ n a, a ∈ D n → eLpNorm (V n a) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C n))
    (hsum : Summable (fun n => w n * ((D n).card : ℝ) ^ (1 / q) * max (C n) 0)) :
    MemLp (fun ω => ∑' n, w n * (D n).sup' (hD n) (fun a => V n a ω)) (ENNReal.ofReal q) μ ∧
    eLpNorm (fun ω => ∑' n, w n * (D n).sup' (hD n) (fun a => V n a ω)) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (∑' n, w n * ((D n).card : ℝ) ^ (1 / q) * max (C n) 0) := by
  set f : ℕ → Ω → ℝ := fun n ω => w n * (D n).sup' (hD n) (fun a => V n a ω) with hfdef
  have hfm : ∀ n, AEStronglyMeasurable (f n) μ := fun n => by
    classical
    let g : α → Ω → ℝ := fun a => if h : a ∈ D n then (hVm n a h).mk (V n a) else 0
    have hg : ∀ a ∈ D n, Measurable (g a) := by
      intro a ha
      simp only [g, dite_eq_left ha]
      exact (hVm n a ha).stronglyMeasurable_mk.measurable
    have hYm : AEStronglyMeasurable (fun ω => (D n).sup' (hD n) (fun a => V n a ω)) μ := by
      refine ⟨fun ω => (D n).sup' (hD n) (fun a => g a ω), ?_, ?_⟩
      · have hm : Measurable ((D n).sup' (hD n) g) := Finset.measurable_sup' (hD n) hg
        have heq : (fun ω => (D n).sup' (hD n) (fun a => g a ω)) = (D n).sup' (hD n) g := by
          funext ω; rw [Finset.sup'_apply]
        rw [heq]; exact hm.stronglyMeasurable
      · have hall : ∀ᵐ ω ∂μ, ∀ a ∈ D n, V n a ω = g a ω := by
          rw [Filter.eventually_all_finset]
          intro a ha
          filter_upwards [(hVm n a ha).ae_eq_mk] with ω ho
          simp only [g, dite_eq_left ha]; exact ho
        filter_upwards [hall] with ω ho
        exact Finset.sup'_congr (hD n) rfl (fun a ha => ho a ha)
    exact hYm.const_mul (w n)
  have hfb : ∀ n, eLpNorm (f n) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (w n * ((D n).card : ℝ) ^ (1 / q) * max (C n) 0) := by
    intro n
    have hsm := eLpNorm_sup'_le_of_le μ (D n) (hD n) (V n) (fun a ω => hVnonneg n a ω)
      (fun a ha => hVm n a ha) (C n) q hq (fun a ha => hVq n a ha)
    have hfeq : f n = w n • (fun ω => (D n).sup' (hD n) (fun a => V n a ω)) := rfl
    rw [hfeq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hw n)]
    calc ENNReal.ofReal (w n) * eLpNorm (fun ω => (D n).sup' (hD n) (fun a => V n a ω))
          (ENNReal.ofReal q) μ
        ≤ ENNReal.ofReal (w n) * ENNReal.ofReal (((D n).card : ℝ) ^ (1 / q) * max (C n) 0) :=
          mul_le_mul_right hsm _
      _ = ENNReal.ofReal (w n * (((D n).card : ℝ) ^ (1 / q) * max (C n) 0)) :=
          (ENNReal.ofReal_mul (hw n)).symm
      _ = ENNReal.ofReal (w n * ((D n).card : ℝ) ^ (1 / q) * max (C n) 0) := by ring_nf
  have hb0 : ∀ n, 0 ≤ w n * ((D n).card : ℝ) ^ (1 / q) * max (C n) 0 := fun n => by
    have hcardpow : 0 ≤ ((D n).card : ℝ) ^ (1 / q) := by positivity
    have hmax : 0 ≤ max (C n) 0 := le_max_right _ _
    exact mul_nonneg (mul_nonneg (hw n) hcardpow) hmax
  exact eLpNorm_tsum_le_of_le μ f _ q hq.le hfm hsum hb0 hfb

end SubdiffusiveProcess
