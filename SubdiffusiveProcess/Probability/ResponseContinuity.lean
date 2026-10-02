import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

/-!
# Potential comparison and response continuity

Source: E043 and Lemma 32, `lem:conditional-compact`. The original response
comparison, positive ball masses and a uniform L1 bound give pointwise
bounds and equicontinuity. The comparison itself must be proved for the
actual variational responses in its separate model consumer.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace SubdiffusiveProcess

/-- Multiplicatively close nonnegative responses have a quantitative additive bound. -/
theorem abs_sub_le_of_multiplicative_comparison {a b E : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hE : 1 ≤ E) (hab : a ≤ E * b) (hba : b ≤ E * a) :
    |a - b| ≤ (E - 1) * (a + b) := by
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hE) ha,
    mul_nonneg (sub_nonneg.mpr hE) hb]

/-- The potential comparison and pointwise bounds imply equicontinuity on a metric space. -/
theorem equicontinuous_of_exp_comparison {X ι : Type*} [PseudoMetricSpace X]
    {f : ι → X → ℝ} {C : ℝ} (hC : 0 ≤ C) (hn : ∀ i x, 0 ≤ f i x)
    (hcmp : ∀ i x y, f i x ≤ Real.exp (C * dist x y) * f i y)
    (hb : ∀ x, ∃ M : ℝ, ∀ i, f i x ≤ M) : Equicontinuous f := by
  intro x
  obtain ⟨M, hM⟩ := hb x
  let b : X → ℝ := fun y =>
    (Real.exp (C * dist y x) - 1) * ((1 + Real.exp (C * dist y x)) * M)
  refine Metric.equicontinuousAt_of_continuity_modulus b ?_ f ?_
  · have hc : Continuous b := by dsimp [b]; fun_prop
    simpa only [b, dist_self, mul_zero, Real.exp_zero, sub_self, zero_mul] using hc.tendsto x
  · apply Eventually.of_forall
    intro y i
    have hE : 1 ≤ Real.exp (C * dist y x) :=
      Real.one_le_exp (mul_nonneg hC dist_nonneg)
    have hxy := hcmp i x y
    rw [dist_comm x y] at hxy
    have hyx := hcmp i y x
    calc
      dist (f i x) (f i y) = |f i x - f i y| := Real.dist_eq _ _
      _ ≤ (Real.exp (C * dist y x) - 1) * (f i x + f i y) :=
        abs_sub_le_of_multiplicative_comparison (hn i x) (hn i y) hE hxy hyx
      _ ≤ b y := by
        apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hE)
        calc
          f i x + f i y ≤ M + Real.exp (C * dist y x) * M :=
            add_le_add (hM i) (hyx.trans (mul_le_mul_of_nonneg_left (hM i) (Real.exp_pos _).le))
          _ = (1 + Real.exp (C * dist y x)) * M := by ring

/-- A nonzero ball and the L1 bound control a response at its center. -/
theorem pointwise_bound_of_exp_comparison {X ι : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {f : ι → X → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hn : ∀ i x, 0 ≤ f i x)
    (hcmp : ∀ i x y, f i x ≤ Real.exp (C * dist x y) * f i y)
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hb : ∀ i, eLpNorm (f i) 1 μ ≤ K) :
    ∀ x, ∃ M : ℝ, ∀ i, f i x ≤ M := by
  intro x
  let B := Metric.ball x 1
  have hB0 : μ B ≠ 0 := (Metric.measure_ball_pos μ x (by norm_num : (0 : ℝ) < 1)).ne'
  have hBt : μ B ≠ ∞ := measure_ne_top _ _
  have hdiv : ENNReal.ofReal (Real.exp C) * K / μ B ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK) hB0
  refine ⟨(ENNReal.ofReal (Real.exp C) * K / μ B).toReal, fun i => ?_⟩
  apply (ENNReal.ofReal_le_iff_le_toReal hdiv).mp
  rw [ENNReal.le_div_iff_mul_le (Or.inl hB0) (Or.inl hBt)]
  calc
    ENNReal.ofReal (f i x) * μ B = ∫⁻ y, ENNReal.ofReal (f i x) ∂μ.restrict B := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (f i y) ∂μ.restrict B := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
      rw [← ENNReal.ofReal_mul (Real.exp_pos C).le]
      apply ENNReal.ofReal_le_ofReal
      apply (hcmp i x y).trans
      apply mul_le_mul_of_nonneg_right _ (hn i y)
      apply Real.exp_le_exp.mpr
      have hdist : dist x y < 1 := by simpa only [B, Metric.mem_ball, dist_comm] using hy
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdist.le hC
    _ = ENNReal.ofReal (Real.exp C) * ∫⁻ y, ENNReal.ofReal (f i y) ∂μ.restrict B :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp C) * K := by
      apply mul_le_mul_right
      calc
        (∫⁻ y, ENNReal.ofReal (f i y) ∂μ.restrict B) ≤
            ∫⁻ y, ENNReal.ofReal (f i y) ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl
        _ = eLpNorm (f i) 1 μ := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          apply lintegral_congr
          intro y
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hn i y)]
        _ ≤ K := hb i

end SubdiffusiveProcess
