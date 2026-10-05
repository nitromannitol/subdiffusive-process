module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeOccupationFormula
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeFiniteDimensionalReduction
public import MarkovProcess.Path.RandomShiftMeasurability

@[expose] public section

/-!
# The process-level occupation identity of the intrinsic time change

Integrating the pathwise change of variables of `TimeChangeOccupationFormula`
against the law of the input process gives the identity needed for the
martingale-problem step: the
Laplace transform in `t` of the one-dimensional marginals of the time-changed
process is the expected `a`-weighted occupation integral of the input process,

`∫₀^∞ e^{-μ t} E f(Y_t) dt = E ∫₀^∞ e^{-μ A_s} a(X_s)⁻¹ f(X_s) ds`.

The right-hand side is the quantity that the `(a,1)` resolvent datum must
reproduce; the left-hand side determines the one-dimensional marginals of the
time-changed process.  Nothing here assumes the producer.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory MarkovProcess Set
open _root_.SubdiffusiveProcess.Section7
open scoped ENNReal NNReal

noncomputable section

variable {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}

omit [MeasurableSpace Theta] in
/-- On the unbounded-clock event, the total continuous-path transform is the
inverse-clock reparameterization. -/
theorem measurableTimeChangedContinuousPath_eq_timeChangedPath
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) {omega : ContinuousPath (State d)}
    (homega : omega ∈ timeChangeUnboundedEvent a theta) :
    measurableTimeChangedContinuousPath a theta ha hapos default omega =
      timeChangedPath a theta ha hapos omega
        ((mem_timeChangeUnboundedEvent_iff ha hapos omega).mp homega) := by
  rw [measurableTimeChangedContinuousPath,
    measurableTimeChangedLifetimePath_eq_ofContinuousPath ha hapos omega homega,
    continuousPathOfLifetimePath_ofContinuousPath]

omit [MeasurableSpace Theta] in
/-- Joint measurability of the time-changed coordinate in the path and the
time. -/
theorem measurable_uncurry_measurableTimeChangedContinuousPath
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) :
    Measurable (fun p : ContinuousPath (State d) × ℝ ↦
      measurableTimeChangedContinuousPath a theta ha hapos default p.1
        (Real.toNNReal p.2)) := by
  have hpair : Measurable (fun p : ContinuousPath (State d) × ℝ ↦
      (measurableTimeChangedContinuousPath a theta ha hapos default p.1,
        Real.toNNReal p.2)) :=
    ((measurable_measurableTimeChangedContinuousPath (Theta := Theta) ha hapos
      default).comp measurable_fst).prodMk
      (continuous_real_toNNReal.measurable.comp measurable_snd)
  exact (ContinuousEval.continuous_eval
    (F := ContinuousPath (State d))).measurable.comp hpair

omit [MeasurableSpace Theta] in
/-- **The process-level occupation identity.**  For any law of the input
process under which the reciprocal clock is almost surely unbounded, the
`μ`-Laplace transform of the one-dimensional marginals of the time-changed
process is the expected reciprocal-weighted occupation integral along the
input process. -/
theorem lintegral_exp_timeChanged_marginal
    (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d))
    (P : Measure (ContinuousPath (State d))) [SFinite P]
    (hP : ∀ᵐ omega ∂P, omega ∈ timeChangeUnboundedEvent a theta)
    (mu : ℝ) {f : State d → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(mu * t))) *
        (∫⁻ omega, f (measurableTimeChangedContinuousPath a theta ha hapos
          default omega (Real.toNNReal t)) ∂P) =
      ∫⁻ omega, (∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (a theta (omega (Real.toNNReal s)))⁻¹ *
          (ENNReal.ofReal
              (Real.exp (-(mu * timeChangePathClock a theta omega s))) *
            f (omega (Real.toNNReal s)))) ∂P := by
  have hjointBase := measurable_uncurry_measurableTimeChangedContinuousPath
    ha hapos default
  have hfixed : ∀ t : ℝ, Measurable (fun omega : ContinuousPath (State d) ↦
      f (measurableTimeChangedContinuousPath a theta ha hapos default omega
        (Real.toNNReal t))) := by
    intro t
    exact hf.comp (hjointBase.comp (measurable_id.prodMk measurable_const))
  have hjoint : Measurable (Function.uncurry
      (fun (t : ℝ) (omega : ContinuousPath (State d)) ↦
        ENNReal.ofReal (Real.exp (-(mu * t))) *
          f (measurableTimeChangedContinuousPath a theta ha hapos default omega
            (Real.toNNReal t)))) := by
    apply Measurable.mul
    · exact ENNReal.measurable_ofReal.comp
        ((Real.continuous_exp.measurable).comp
          (measurable_const.mul measurable_fst).neg)
    · exact hf.comp (hjointBase.comp (measurable_snd.prodMk measurable_fst))
  calc
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(mu * t))) *
        (∫⁻ omega, f (measurableTimeChangedContinuousPath a theta ha hapos
          default omega (Real.toNNReal t)) ∂P)
        = ∫⁻ t in Ioi (0 : ℝ), (∫⁻ omega,
            ENNReal.ofReal (Real.exp (-(mu * t))) *
              f (measurableTimeChangedContinuousPath a theta ha hapos default
                omega (Real.toNNReal t)) ∂P) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun t _ ↦ ?_)
      rw [lintegral_const_mul _ (hfixed t)]
    _ = ∫⁻ omega, (∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (Real.exp (-(mu * t))) *
              f (measurableTimeChangedContinuousPath a theta ha hapos default
                omega (Real.toNNReal t))) ∂P := by
      exact lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ omega, (∫⁻ s in Ioi (0 : ℝ),
            ENNReal.ofReal (a theta (omega (Real.toNNReal s)))⁻¹ *
              (ENNReal.ofReal
                  (Real.exp (-(mu * timeChangePathClock a theta omega s))) *
                f (omega (Real.toNNReal s)))) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hP] with omega homega
      rw [funext fun t ↦ congrArg (fun z ↦ ENNReal.ofReal (Real.exp (-(mu * t))) * f z)
        (congrFun (congrArg _
          (measurableTimeChangedContinuousPath_eq_timeChangedPath ha hapos default
            homega)) (Real.toNNReal t))]
      exact lintegral_exp_timeChangedPath ha hapos omega
        ((mem_timeChangeUnboundedEvent_iff ha hapos omega).mp homega) mu f

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
