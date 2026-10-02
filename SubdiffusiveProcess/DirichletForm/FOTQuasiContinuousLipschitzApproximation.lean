import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousLipschitzPrimitives
import Mathlib.Analysis.Calculus.Deriv.Slope

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section
namespace DirichletForm.FOTConstruction

/-- Steklov averages preserve the Lipschitz constant, converge pointwise,
and their derivatives converge at every differentiability point. -/
theorem lipschitz_c1_approximation (T : ℝ → ℝ) {L : ℝ≥0}
    (hT : LipschitzWith L T) (hT0 : T 0 = 0) :
    ∃ Φ : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ 1 (Φ n)) ∧ (∀ n, LipschitzWith L (Φ n)) ∧
      (∀ n, Φ n 0 = 0) ∧
      (∀ s, Tendsto (fun n => Φ n s) atTop (𝓝 (T s))) ∧
      (∀ s a, HasDerivAt T a s → Tendsto (fun n => deriv (Φ n) s) atTop (𝓝 a)) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := fun n => by dsimp only [ε]; positivity
  have hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => hεpos n⟩
  let A : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, T t
  have hAderiv : ∀ s, HasDerivAt A (T s) s := fun s =>
    hT.continuous.integral_hasStrictDerivAt 0 s |>.hasDerivAt
  have hA0 : A 0 = 0 := intervalIntegral.integral_same
  let Φ : ℕ → ℝ → ℝ := fun n s =>
    (A (s + ε n) - A s - A (ε n)) / ε n
  have hΦderiv : ∀ n s, HasDerivAt (Φ n) ((T (s + ε n) - T s) / ε n) s := by
    intro n s
    simpa only [Φ, Function.comp_def, Pi.sub_apply, id_eq, mul_one] using
      (((hAderiv (s + ε n)).comp s ((hasDerivAt_id s).add_const (ε n))).sub
        (hAderiv s) |>.sub_const (A (ε n))).div_const (ε n)
  have hΦderiv_eq : ∀ n s, deriv (Φ n) s = (T (s + ε n) - T s) / ε n :=
    fun n s => (hΦderiv n s).deriv
  have hΦdiff : ∀ n, Differentiable ℝ (Φ n) := fun n s =>
    (hΦderiv n s).differentiableAt
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [contDiff_one_iff_deriv]
    refine ⟨hΦdiff n, ?_⟩
    rw [funext (hΦderiv_eq n)]
    exact ((hT.continuous.comp (continuous_id.add continuous_const)).sub hT.continuous).div_const _
  · intro n
    apply lipschitzWith_of_nnnorm_deriv_le (hΦdiff n)
    intro s
    rw [← NNReal.coe_le_coe, coe_nnnorm, hΦderiv_eq n, norm_div,
      Real.norm_eq_abs (ε n), abs_of_pos (hεpos n)]
    apply (div_le_iff₀ (hεpos n)).mpr
    have h := hT.dist_le_mul (s + ε n) s
    simpa only [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs (ε n),
      abs_of_pos (hεpos n)] using h
  · intro n
    dsimp only [Φ]
    rw [zero_add, hA0, sub_zero, sub_self, zero_div]
  · intro s
    have hslope := (hAderiv s).tendsto_slope_zero_right.comp hε
    have hzero := (hAderiv 0).tendsto_slope_zero_right.comp hε
    have hsub := hslope.sub hzero
    simpa only [hT0, sub_zero, A, Φ, div_eq_mul_inv, sub_mul, zero_add,
      intervalIntegral.integral_same, smul_eq_mul, mul_sub, mul_comm] using hsub
  · intro s a ha
    have hslope := ha.tendsto_slope_zero_right.comp hε
    simpa only [hΦderiv_eq, div_eq_mul_inv, smul_eq_mul, mul_comm] using hslope

end DirichletForm.FOTConstruction
