import SubdiffusiveProcess.Section10.TorsionExitDynkinMartingale
import MarkovProcess.Path.OptionalStopping
import MarkovProcess.Trajectory.DynkinStopping

/-! Existing bounded optional stopping applied to the actual supplied law.
No Kolmogorov/tightness or stochastic-calculus construction is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty
namespace SubdiffusiveProcess.Section10
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]

/-- Bounded optional stopping for the actual full-FDD Feller realization. -/
theorem integral_dynkinProcess_stoppingTime_realization
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hF : P.IsFellerKernelSemigroup) (Q : Kernel alpha (ContinuousPath alpha))
    [IsMarkovKernel Q] (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (f : hF.c0Semigroup.generatorDomain) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun w ↦ (T w : WithTop NNReal)))
    {t : NNReal} (hTt : ∀ w, T w ≤ t) (x : alpha) :
    (∫ w, hF.dynkinProcess f (T w) w ∂Q x) = (f : C₀(alpha, ℝ)) x := by
  have hbound : ∀ v : NNReal, ∃ C : ℝ, ∀ u ≤ v, ∀ w : ContinuousPath alpha,
      ‖hF.dynkinProcess f u w‖ ≤ C := by
    intro v
    refine ⟨‖(f : C₀(alpha, ℝ))‖ + (v : ℝ) * ‖hF.c0Semigroup.generator f‖,
      fun u hu w ↦ (hF.norm_dynkinProcess_le f u w).trans ?_⟩
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hu : (u : ℝ) ≤ (v : ℝ)) (norm_nonneg (hF.c0Semigroup.generator f)))
  have h := integral_stoppedValue_eq_of_locallyBounded
    (martingale_dynkinProcess_realization P hP hF Q hfdd f x) hbound
    (fun w v ↦ (hF.continuous_dynkinProcess f w).continuousWithinAt) hT hTt
  exact h.trans (integral_dynkinProcess_realization P hP hF Q hfdd f 0 x)

/-- The expected test value at a bounded stopping time loses at most
`t * ‖L f‖` from its initial value, under the original supplied law. -/
theorem integral_eval_stoppingTime_ge_realization
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hF : P.IsFellerKernelSemigroup) (Q : Kernel alpha (ContinuousPath alpha))
    [IsMarkovKernel Q] (hfdd : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (f : hF.c0Semigroup.generatorDomain) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun w ↦ (T w : WithTop NNReal)))
    {t : NNReal} (hTt : ∀ w, T w ≤ t) (x : alpha) :
    (f : C₀(alpha, ℝ)) x - (t : ℝ) * ‖hF.c0Semigroup.generator f‖ ≤
      ∫ w, (f : C₀(alpha, ℝ)) (w (T w)) ∂Q x := by
  have hpos : Integrable (fun w : ContinuousPath alpha ↦
      (f : C₀(alpha, ℝ)) (w (T w))) (Q x) :=
    Integrable.of_bound
      (((f : C₀(alpha, ℝ)).continuous.measurable.comp
        (ContinuousPath.measurable_eval_stoppingTime_borel T hT)).aestronglyMeasurable)
      ‖(f : C₀(alpha, ℝ))‖ (Eventually.of_forall fun w ↦ norm_c0_apply_le _ _)
  have hdynkin : Integrable (fun w : ContinuousPath alpha ↦
      hF.dynkinProcess f (T w) w) (Q x) :=
    Integrable.of_bound
      (hF.measurable_dynkinProcess_stoppingTime f T hT).aestronglyMeasurable
      (‖(f : C₀(alpha, ℝ))‖ + (t : ℝ) * ‖hF.c0Semigroup.generator f‖)
      (Eventually.of_forall fun w ↦ (hF.norm_dynkinProcess_le f (T w) w).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (by exact_mod_cast hTt w : (T w : ℝ) ≤ (t : ℝ)) (norm_nonneg (hF.c0Semigroup.generator f)))))
  have hineq : ∀ w : ContinuousPath alpha,
      hF.dynkinProcess f (T w) w - (t : ℝ) * ‖hF.c0Semigroup.generator f‖ ≤
        (f : C₀(alpha, ℝ)) (w (T w)) := by
    intro w
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (T w : ℝ))
      (fun s _ ↦ norm_c0_apply_le (hF.c0Semigroup.generator f) (w (Real.toNNReal s)))
    rw [sub_zero, abs_of_nonneg (T w).coe_nonneg, mul_comm] at hint
    have hlo : -((t : ℝ) * ‖hF.c0Semigroup.generator f‖) ≤
        ∫ s in (0 : ℝ)..(T w : ℝ),
          (hF.c0Semigroup.generator f) (w (Real.toNNReal s)) := by
      have ht := mul_le_mul_of_nonneg_right (by exact_mod_cast hTt w : (T w : ℝ) ≤ (t : ℝ)) (norm_nonneg (hF.c0Semigroup.generator f))
      exact (neg_le_neg ht).trans (abs_le.mp hint).1
    rw [hF.dynkinProcess_apply]
    linarith only [hlo]
  have h := integral_mono (hdynkin.sub (integrable_const _)) hpos hineq
  change (∫ w, hF.dynkinProcess f (T w) w -
    (t : ℝ) * ‖hF.c0Semigroup.generator f‖ ∂Q x) ≤ _ at h
  rw [integral_sub hdynkin (integrable_const _), integral_const, probReal_univ,
    one_smul, integral_dynkinProcess_stoppingTime_realization P hP hF Q hfdd f T hT hTt x] at h
  exact h

end SubdiffusiveProcess.Section10
