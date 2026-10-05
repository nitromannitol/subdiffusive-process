module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeMeasurableTransform
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

/-!
# The occupation-time change of variables for the intrinsic clock

The manuscript proof of the intrinsic time change
 uses, for every path, the change
of variables `t = A_s` between the clock of `X` and the running time of
`Y = X ∘ θ`.  In Revuz--Yor form it reads

`∫₀^∞ g(t, Y_t) dt = ∫₀^∞ g(A_s, X_s) a(X_s)⁻¹ ds`,

because `dA_s = a(X_s)⁻¹ ds`.  This file proves that identity for Lebesgue
integrals of arbitrary `ℝ≥0∞`-valued integrands, first for an abstract
additive clock and then along a continuous path.

It is the deterministic half of the resolvent route to the missing
probabilistic producer: applied to `g t y = e^{-μ t} f y` it turns the
`μ`-resolvent of the time-changed path into the `a`-weighted occupation
integral of the input path, which is the quantity the manuscript's
martingale-problem step evaluates.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory MarkovProcess Set
open SubdiffusiveProcess.Frozen.Section7
open scoped ENNReal NNReal

noncomputable section

section AbstractClock

variable {b : ℝ → ℝ}

/-- On positive time the additive clock is differentiable with derivative the
integrand. -/
theorem hasDerivWithinAt_timeChangeAdditiveClock (hb : Continuous b) {s : ℝ}
    (hs : 0 < s) :
    HasDerivWithinAt (timeChangeAdditiveClock b) (b s) (Ioi 0) s := by
  have hprim : HasDerivAt (fun u : ℝ ↦ ∫ r in (0 : ℝ)..u, b r) (b s) s :=
    intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable _ _)
      (hb.stronglyMeasurableAtFilter _ _) hb.continuousAt
  exact hprim.hasDerivWithinAt.congr
    (fun y hy ↦ timeChangeAdditiveClock_eq_integral (le_of_lt hy))
    (timeChangeAdditiveClock_eq_integral hs.le)

/-- A regular unbounded clock maps positive time onto positive time. -/
theorem image_Ioi_timeChangeAdditiveClock (hb : Continuous b)
    (hbpos : ∀ r, 0 < b r)
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < timeChangeAdditiveClock b s) :
    timeChangeAdditiveClock b '' Ioi 0 = Ioi 0 := by
  have hstrict := strictMonoOn_timeChangeAdditiveClock hb hbpos
  have hcont := continuous_timeChangeAdditiveClock hb
  apply Subset.antisymm
  · rintro t ⟨s, hs, rfl⟩
    have hlt := hstrict (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs.le) hs
    rw [timeChangeAdditiveClock_zero] at hlt
    exact hlt
  · intro t ht
    obtain ⟨S, hS, htS⟩ := hunbounded t
    have hmem : t ∈ Icc (timeChangeAdditiveClock b 0) (timeChangeAdditiveClock b S) := by
      rw [timeChangeAdditiveClock_zero]
      exact ⟨le_of_lt ht, htS.le⟩
    obtain ⟨r, hr, hAr⟩ := intermediate_value_Icc hS hcont.continuousOn hmem
    refine ⟨r, ?_, hAr⟩
    rcases eq_or_lt_of_le hr.1 with h | h
    · exfalso
      rw [← h, timeChangeAdditiveClock_zero] at hAr
      exact absurd hAr.symm (ne_of_gt ht)
    · exact h

/-- **Occupation-time change of variables for an additive clock.**  For a
continuous positive integrand with unbounded clock, integration in the clock
variable is integration in the original variable against the density `b`. -/
theorem lintegral_Ioi_eq_lintegral_comp_timeChangeAdditiveClock
    (hb : Continuous b) (hbpos : ∀ r, 0 < b r)
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < timeChangeAdditiveClock b s)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), g t =
      ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (b s) * g (timeChangeAdditiveClock b s) := by
  have hinj : InjOn (timeChangeAdditiveClock b) (Ioi 0) :=
    Set.InjOn.mono Ioi_subset_Ici_self
      (strictMonoOn_timeChangeAdditiveClock hb hbpos).injOn
  have hchange := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
    measurableSet_Ioi
    (fun s hs ↦ hasDerivWithinAt_timeChangeAdditiveClock hb hs) hinj g
  rw [image_Ioi_timeChangeAdditiveClock hb hbpos hunbounded] at hchange
  rw [hchange]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s _ ↦ ?_)
  rw [abs_of_pos (hbpos s)]

end AbstractClock

section Path

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The time-changed path, read at a clock value, is the input path read at
the corresponding original time. -/
theorem timeChangedContinuousPath_apply_clock
    (omega : ContinuousPath alpha) (A : ℝ → ℝ) (hA0 : A 0 = 0)
    (hA : Monotone A) (hstrict : StrictMonoOn A (Ici 0)) (hcont : Continuous A)
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < A s) {s : ℝ} (hs : 0 ≤ s) :
    timeChangedContinuousPath omega A hA0 hA hstrict hcont hunbounded
        (Real.toNNReal (A s)) = omega (Real.toNNReal s) := by
  have hAs : 0 ≤ A s := by
    rw [← hA0]
    exact hA hs
  change omega ((nonnegativeClockOrderIso A hA0 hA hstrict hcont hunbounded).symm
    (Real.toNNReal (A s))) = _
  congr 1
  apply (OrderIso.symm_apply_eq _).2
  apply NNReal.eq
  rw [coe_nonnegativeClockOrderIso_apply, Real.coe_toNNReal _ hAs,
    Real.coe_toNNReal _ hs]

end Path

section PathClock

variable {Theta : Type*} {d : ℕ} {a : Theta → State d → ℝ} {theta : Theta}

/-- The inverse-clock reparameterization of a continuous path, for a path
whose reciprocal clock is unbounded. -/
def timeChangedPath (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d))
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧
      B < timeChangePathClock a theta omega s) : ContinuousPath (State d) :=
  timeChangedContinuousPath omega (timeChangePathClock a theta omega)
    (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
    (timeChangePathClock_core_clauses ha hapos 0 omega).1
    (timeChangePathClock_regular ha hapos omega).2
    (timeChangePathClock_regular ha hapos omega).1 hunbounded

/-- The time-changed path is exactly the continuous path underlying the
measurable lifetime-path transform of `TimeChangeMeasurableTransform`. -/
theorem measurableTimeChangedLifetimePath_eq_ofContinuousPath
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d))
    (homega : omega ∈ timeChangeUnboundedEvent a theta) :
    measurableTimeChangedLifetimePath a theta ha hapos omega =
      LifetimePath.ofContinuousPath (timeChangedPath a theta ha hapos omega
        ((mem_timeChangeUnboundedEvent_iff ha hapos omega).mp homega)) := by
  rw [measurableTimeChangedLifetimePath, dite_eq_left homega]
  rfl

/-- **The pathwise occupation-time identity of the intrinsic time change.**
For every path whose reciprocal clock is unbounded, integrating any
`ℝ≥0∞`-valued weight along the time-changed path equals integrating it along
the original path against the Revuz density `a(X_s)⁻¹`.

This is the change of variables `t = A_s`, `dt = a(X_s)⁻¹ ds` used in the occupation identity. -/
theorem lintegral_timeChangedPath
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d))
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧
      B < timeChangePathClock a theta omega s)
    (g : ℝ → State d → ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ),
        g t (timeChangedPath a theta ha hapos omega hunbounded
          (Real.toNNReal t)) =
      ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (a theta (omega (Real.toNNReal s)))⁻¹ *
          g (timeChangePathClock a theta omega s) (omega (Real.toNNReal s)) := by
  have hb : Continuous (timeChangePathIntegrand a theta omega) :=
    continuous_timeChangePathIntegrand ha hapos omega
  have hbpos : ∀ r, 0 < timeChangePathIntegrand a theta omega r := fun r ↦
    inv_pos.mpr (hapos _)
  have hchange := lintegral_Ioi_eq_lintegral_comp_timeChangeAdditiveClock
    hb hbpos hunbounded
    (fun t ↦ g t (timeChangedPath a theta ha hapos omega hunbounded
      (Real.toNNReal t)))
  rw [hchange]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs ↦ ?_)
  have hclock : timeChangedPath a theta ha hapos omega hunbounded
      (Real.toNNReal
        (timeChangeAdditiveClock (timeChangePathIntegrand a theta omega) s)) =
      omega (Real.toNNReal s) :=
    timeChangedContinuousPath_apply_clock omega _ _ _ _ _ hunbounded (le_of_lt hs)
  rw [hclock]
  rfl

/-- **The time-changed resolvent as an `a`-weighted occupation integral.**
The `μ`-resolvent kernel of the time-changed path is the reciprocal-weighted
integral of `e^{-μ A_s}` along the original path.  This is the identity the
resolvent route to the resolvent identity has to evaluate against the
`(a,1)`-resolvent datum. -/
theorem lintegral_exp_timeChangedPath
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d))
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧
      B < timeChangePathClock a theta omega s)
    (mu : ℝ) (f : State d → ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(mu * t))) *
        f (timeChangedPath a theta ha hapos omega hunbounded
          (Real.toNNReal t)) =
      ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (a theta (omega (Real.toNNReal s)))⁻¹ *
          (ENNReal.ofReal
              (Real.exp (-(mu * timeChangePathClock a theta omega s))) *
            f (omega (Real.toNNReal s))) :=
  lintegral_timeChangedPath ha hapos omega hunbounded
    (fun t y ↦ ENNReal.ofReal (Real.exp (-(mu * t))) * f y)

end PathClock

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
