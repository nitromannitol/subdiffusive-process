import SubdiffusiveProcess.Probability.LiminfGrowth
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Pass random local growth estimates through weak convergence of finite
measures. Normalizing finite measures is used only to apply Portmanteau; the
growth bound retains their actual masses. -/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess

/-- The open-set part of Portmanteau for arbitrary finite measures. -/
theorem finiteMeasure_le_liminf_open
    {X : Type*} [Nonempty X] [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {muN : ℕ → FiniteMeasure X} {mu : FiniteMeasure X}
    (hconv : Tendsto muN atTop (𝓝 mu)) {U : Set X} (hU : IsOpen U) :
    (mu : Measure X) U ≤ liminf (fun n => (muN n : Measure X) U) atTop := by
  by_cases hzero : mu = 0
  · simp only [hzero, FiniteMeasure.toMeasure_zero, Measure.coe_zero, Pi.zero_apply, zero_le]
  have hnorm := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (FiniteMeasure.tendsto_normalize_of_tendsto hconv hzero) hU
  have hmass : Tendsto (fun n => ((muN n).mass : ℝ≥0∞)) atTop (𝓝 (mu.mass : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto mu.mass).comp hconv.mass
  have hscale (nu : FiniteMeasure X) :
      (nu : Measure X) U = (nu.mass : ℝ≥0∞) * (nu.normalize : Measure X) U := by
    have h := congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞)) (nu.self_eq_mass_mul_normalize U)
    simpa only [ENNReal.coe_mul, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using h
  rw [hscale mu]
  calc
    (mu.mass : ℝ≥0∞) * (mu.normalize : Measure X) U ≤
        (mu.mass : ℝ≥0∞) * liminf (fun n => ((muN n).normalize : Measure X) U) atTop :=
      mul_le_mul_right hnorm _
    _ = liminf (fun n => ((muN n).mass : ℝ≥0∞)) atTop *
        liminf (fun n => ((muN n).normalize : Measure X) U) atTop := by rw [hmass.liminf_eq]
    _ ≤ liminf (fun n => ((muN n).mass : ℝ≥0∞) *
        ((muN n).normalize : Measure X) U) atTop := ENNReal.le_liminf_mul
    _ = liminf (fun n => (muN n : Measure X) U) atTop := by simp_rw [← hscale]

/-- Weak convergence on one event supplies all open test-set lower bounds
used in the growth passage, including an uncountable family of balls. -/
theorem exists_measure_growth_of_weak_convergence
    {Ω X T : Type*} [MeasurableSpace Ω] [Nonempty X] [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (P : Measure Ω) (muN : ℕ → Ω → FiniteMeasure X) (mu : Ω → FiniteMeasure X)
    (tests : T → Set X) (hopen : ∀ t, IsOpen (tests t)) (scale : T → ℝ≥0)
    (f : ℕ → Ω → ℝ) (p C : ℝ≥0) (hp : p ≠ 0)
    (hf : ∀ n, Measurable (f n)) (hb : ∀ n, eLpNorm (f n) p P ≤ C)
    (hconv : ∀ᵐ om ∂P, Tendsto (fun n => muN n om) atTop (𝓝 (mu om)))
    (hgrowth : ∀ᵐ om ∂P, ∀ n t,
      (muN n om : Measure X) (tests t) ≤ (scale t : ℝ≥0∞) * ‖f n om‖ₑ) :
    ∃ K : Ω → ℝ, Measurable K ∧ (∀ om, 0 ≤ K om) ∧ eLpNorm K p P ≤ C ∧
      ∀ᵐ om ∂P, ∀ t,
        (mu om : Measure X) (tests t) ≤ ENNReal.ofReal (K om) * (scale t : ℝ≥0∞) := by
  apply exists_measure_growth_of_liminf P (fun n om => (muN n om : Measure X))
    (fun om => (mu om : Measure X)) tests scale f p C hp hf hb ?_ hgrowth
  filter_upwards [hconv] with om hom t
  exact finiteMeasure_le_liminf_open hom (hopen t)

end SubdiffusiveProcess


