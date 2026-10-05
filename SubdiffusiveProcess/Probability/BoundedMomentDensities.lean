module

public import SubdiffusiveProcess.Probability.BoundedMoments
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
@[expose] public section

open MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction

namespace SubdiffusiveProcess
/-- Bounded continuous signed densities are determined pointwise by their separating-coordinate moments. -/
theorem boundedContinuous_eq_of_monomial_integrals
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {k : ℕ}
    (coord : Fin k → (X →ᵇ ℝ))
    (hsep : ∀ x y : X, x ≠ y → ∃ i : Fin k, coord i x ≠ coord i y)
    (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (F G : X →ᵇ ℝ)
    (hm : ∀ m : Fin k → ℕ,
      (∫ x, F x * ∏ i : Fin k, (coord i x) ^ (m i) ∂μ) =
        ∫ x, G x * ∏ i : Fin k, (coord i x) ^ (m i) ∂μ) :
    F = G := by
  let C : ℝ := ‖F‖ + ‖G‖
  let f : X → ℝ := fun x => C + F x
  let g : X → ℝ := fun x => C + G x
  have hf0 : ∀ x, 0 ≤ f x := by
    intro x
    dsimp [f, C]
    have hF := F.norm_coe_le_norm x
    have hG : 0 ≤ ‖G‖ := norm_nonneg G
    linarith [le_trans (neg_le_abs (F x)) hF]
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    dsimp [g, C]
    have hG := G.norm_coe_le_norm x
    have hF : 0 ≤ ‖F‖ := norm_nonneg F
    linarith [le_trans (neg_le_abs (G x)) hG]
  have hf_int : Integrable f μ := by
    exact (integrable_const (‖F‖ + ‖G‖)).add (F.integrable μ)
  have hg_int : Integrable g μ := by
    exact (integrable_const (‖F‖ + ‖G‖)).add (G.integrable μ)
  let μF : Measure X := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let μG : Measure X := μ.withDensity (fun x => ENNReal.ofReal (g x))
  have : IsFiniteMeasure μF := by
    dsimp [μF]
    exact isFiniteMeasure_withDensity_ofReal hf_int.2
  have : IsFiniteMeasure μG := by
    dsimp [μG]
    exact isFiniteMeasure_withDensity_ofReal hg_int.2
  have hmeas : μF = μG := by
    apply measure_eq_of_bounded_monomial_integrals coord hsep
    intro m
    let p : X → ℝ := fun x => ∏ i : Fin k, (coord i x) ^ (m i)
    let P : X →ᵇ ℝ := ∏ i : Fin k, (coord i) ^ (m i)
    have hp : (⇑P : X → ℝ) = p := by
      funext x
      simp only [P, p, BoundedContinuousFunction.prod_apply,
        BoundedContinuousFunction.pow_apply]
    have hp_int : Integrable p μ := by
      rw [← hp]
      exact P.integrable μ
    have hFp_int : Integrable (fun x => F x * p x) μ := by
      rw [← hp]
      exact (F * P).integrable μ
    have hGp_int : Integrable (fun x => G x * p x) μ := by
      rw [← hp]
      exact (G * P).integrable μ
    change (∫ x, p x ∂μF) = ∫ x, p x ∂μG
    have hFdens : (∫ x, p x ∂μF) = ∫ x, f x * p x ∂μ := by
      rw [show μF = μ.withDensity (fun x => ENNReal.ofReal (f x)) by rfl,
        integral_withDensity_eq_integral_toReal_smul]
      · simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]
      · exact (continuous_const.add F.continuous).measurable.ennreal_ofReal
      · filter_upwards with x
        exact ENNReal.ofReal_lt_top
    have hGdens : (∫ x, p x ∂μG) = ∫ x, g x * p x ∂μ := by
      rw [show μG = μ.withDensity (fun x => ENNReal.ofReal (g x)) by rfl,
        integral_withDensity_eq_integral_toReal_smul]
      · simp only [ENNReal.toReal_ofReal (hg0 _), smul_eq_mul]
      · exact (continuous_const.add G.continuous).measurable.ennreal_ofReal
      · filter_upwards with x
        exact ENNReal.ofReal_lt_top
    rw [hFdens, hGdens]
    rw [show (fun x => f x * p x) = fun x => C * p x + F x * p x by
      funext x; simp only [f, add_mul],
      show (fun x => g x * p x) = fun x => C * p x + G x * p x by
        funext x; simp only [g, add_mul],
      integral_add (hp_int.const_mul C) hFp_int,
      integral_add (hp_int.const_mul C) hGp_int]
    exact congrArg (fun z => (∫ x, C * p x ∂μ) + z) (hm m)
  have hof : (fun x => ENNReal.ofReal (f x)) =ᵐ[μ]
      (fun x => ENNReal.ofReal (g x)) := by
    apply (withDensity_eq_iff_of_sigmaFinite
      (continuous_const.add F.continuous).aemeasurable.ennreal_ofReal
      (continuous_const.add G.continuous).aemeasurable.ennreal_ofReal).mp
    exact hmeas
  have hfg : f =ᵐ[μ] g := hof.fun_comp ENNReal.toReal |>.mono fun x hx => by
    simpa only [Function.comp_apply, ENNReal.toReal_ofReal (hf0 x),
      ENNReal.toReal_ofReal (hg0 x)] using hx
  have hFG : (fun x => F x) =ᵐ[μ] (fun x => G x) := hfg.mono fun x hx => by
    dsimp [f, g] at hx
    linarith
  apply BoundedContinuousFunction.ext
  intro x
  exact congrFun (Measure.eq_of_ae_eq hFG F.continuous G.continuous) x

end SubdiffusiveProcess
