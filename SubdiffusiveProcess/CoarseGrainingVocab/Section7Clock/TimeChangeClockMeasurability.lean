module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangePathClock
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Measurability of the reciprocal additive clock

This file proves the first path-space measurability input for the intrinsic
time change: at every deterministic time,
the reciprocal-coefficient additive clock is a Borel measurable functional
of the continuous path.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory MarkovProcess
open SubdiffusiveProcess.Frozen.Section7

noncomputable section

variable {Theta : Type*} {d : ℕ}

/-- Joint measurability of the reciprocal coefficient sampled at a real time
and along a continuous path. -/
theorem stronglyMeasurable_timeChangePathIntegrand_uncurry
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x) :
    StronglyMeasurable
      (Function.uncurry fun (r : ℝ) (omega : ContinuousPath (State d)) ↦
        timeChangePathIntegrand a theta omega r) := by
  have heval : Continuous
      (fun p : ℝ × ContinuousPath (State d) ↦ p.2 (Real.toNNReal p.1)) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).comp
      (continuous_real_toNNReal.fst'.prodMk continuous_snd)
  have hsample : Continuous
      (fun p : ℝ × ContinuousPath (State d) ↦ a theta (p.2 (Real.toNNReal p.1))) :=
    ha.comp heval
  have hinv : Continuous
      (fun p : ℝ × ContinuousPath (State d) ↦
        (a theta (p.2 (Real.toNNReal p.1)))⁻¹) :=
    hsample.inv₀ (fun p ↦ ne_of_gt (hapos _))
  exact hinv.stronglyMeasurable

/-- At a deterministic real time, the pathwise additive clock is a Borel
measurable real-valued functional on continuous-path space. -/
theorem stronglyMeasurable_timeChangePathClock
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x) (s : ℝ) :
    StronglyMeasurable
      (fun omega : ContinuousPath (State d) ↦ timeChangePathClock a theta omega s) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (max s 0))
  have hprod : StronglyMeasurable
      (fun omega : ContinuousPath (State d) ↦
        ∫ r, timeChangePathIntegrand a theta omega r ∂ν) :=
    (stronglyMeasurable_timeChangePathIntegrand_uncurry ha hapos).integral_prod_left'
  have hclock : (fun omega : ContinuousPath (State d) ↦
        timeChangePathClock a theta omega s) =
      fun omega : ContinuousPath (State d) ↦
        ∫ r, timeChangePathIntegrand a theta omega r ∂ν := by
    funext omega
    rw [timeChangePathClock, timeChangeAdditiveClock,
      intervalIntegral.integral_of_le (le_max_right s 0)]
  rw [hclock]
  exact hprod

/-- Measurable rather than strongly measurable spelling of the deterministic
clock evaluation, for use in random-time and pushforward constructions. -/
theorem measurable_timeChangePathClock
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x) (s : ℝ) :
    Measurable
      (fun omega : ContinuousPath (State d) ↦ timeChangePathClock a theta omega s) :=
  (stronglyMeasurable_timeChangePathClock ha hapos s).measurable

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
