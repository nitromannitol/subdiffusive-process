import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic.Linarith

/-!
# Higher moments and strong convergence

Source: Lemma 32, `lem:conditional-compact`. A strict finite exponent gap
gives uniform integrability by the restricted-measure Holder inequality.
Fatou and Mathlib Vitali then turn almost-everywhere convergence into Lp
convergence. No model-specific input is required.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace SubdiffusiveProcess

/-- A uniform higher moment gives uniform integrability at each smaller finite exponent. -/
theorem unifIntegrable_of_eLpNorm_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {ι : Type*} {f : ι → X → ℝ} {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hpq : p < q) (hq : q ≠ ∞) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hb : ∀ i, eLpNorm (f i) q μ ≤ K) :
    UnifIntegrable f p μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpt : p ≠ ∞ := (hpq.trans_le le_top).ne
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hpqr : p.toReal < q.toReal := (ENNReal.toReal_lt_toReal hpt hq).mpr hpq
  have hr : 0 < 1 / p.toReal - 1 / q.toReal :=
    sub_pos.mpr (one_div_lt_one_div_of_lt hpr hpqr)
  have hlim : Tendsto (fun d : ℝ => K * (ENNReal.ofReal d) ^
      (1 / p.toReal - 1 / q.toReal)) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_apply, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hr, mul_zero] using
      (((ENNReal.continuous_const_mul hK).comp
        ((ENNReal.continuous_rpow_const (y := 1 / p.toReal - 1 / q.toReal)).comp ENNReal.continuous_ofReal)).tendsto 0)
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp
    (hlim.eventually_lt_const (ENNReal.ofReal_pos.mpr hε))
  refine ⟨δ / 2, by linarith, fun i s hs hμs => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  calc
    eLpNorm (f i) p (μ.restrict s) ≤ eLpNorm (f i) q (μ.restrict s) *
        (μ.restrict s) univ ^ (1 / p.toReal - 1 / q.toReal) :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq.le (hf i).restrict
    _ ≤ K * (ENNReal.ofReal (δ / 2)) ^ (1 / p.toReal - 1 / q.toReal) := by
      rw [Measure.restrict_apply_univ]
      exact mul_le_mul' ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hb i))
        (ENNReal.rpow_le_rpow hμs hr.le)
    _ ≤ ENNReal.ofReal ε := (hδbound (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (show 0 < δ / 2 by linarith)]
      linarith)).le

/-- Pointwise convergence and a bounded higher moment imply convergence in every smaller Lp. -/
theorem tendsto_eLpNorm_of_ae_tendsto_of_higher_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : ℕ → X → ℝ} {g : X → ℝ} {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hpq : p < q) (hq : q ≠ ∞) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hb : ∀ n, eLpNorm (f n) q μ ≤ K)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MemLp g q μ ∧ Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := by
  have hgb : eLpNorm g q μ ≤ K := Lp.eLpNorm_le_of_ae_tendsto
    (Eventually.of_forall hb) hf hlim
  have hgq : MemLp g q μ := ⟨hg, hgb.trans_lt (lt_top_iff_ne_top.mpr hK)⟩
  refine ⟨hgq, tendsto_Lp_finite_of_tendsto_ae hp (hpq.trans_le le_top).ne hf
    (hgq.mono_exponent hpq.le) ?_ hlim⟩
  exact unifIntegrable_of_eLpNorm_bound hp hpq hq hK hf hb

end SubdiffusiveProcess
