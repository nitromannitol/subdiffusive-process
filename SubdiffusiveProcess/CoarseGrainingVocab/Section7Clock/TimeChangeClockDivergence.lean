module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeMeasurableTransform

@[expose] public section

/-!
# Deterministic sufficient conditions for divergence of the reciprocal clock

The frozen time-change anchor needs the reciprocal
clock `A_s = ∫_0^s a(X_r)⁻¹ dr` to diverge almost surely.  This file records
exactly what the *deterministic* part of that statement gives: divergence holds
for every path along which the coefficient is bounded above, in particular for
every path with bounded range (by local boundedness of a continuous
coefficient).

That is the whole of the deterministic content, and it is not enough.  The
remaining case is a path that escapes to infinity along which `a` is unbounded,
and there divergence of the clock is a genuinely stochastic question about the
**target** family: `A_∞ = ∞` is precisely non-explosion of the `(a, 1)`
diffusion, not of the `(a, a)` diffusion.  In dimension one this is visible in
Feller's test.  For `a(x) = (1 + x²)^{3/2}` the two diffusions share the scale
function `s' = a⁻¹`, which has `s(±∞)` finite, while their speed measures are
`a dx` and `dx`.  The Feller integrals at `+∞` are

`∫^∞ (s(∞) - s(x)) a(x) dx ≍ ∫^∞ x dx = ∞` (so the `(a, a)` process does not
explode) and `∫^∞ (s(∞) - s(x)) dx ≍ ∫^∞ x⁻² dx < ∞` (so the `(a, 1)` process
does explode, i.e. `A_∞ < ∞`).

Consequently no argument from positivity and continuity of `a` together with
conservativity of the `(a, a)` family alone can prove the almost-sure
divergence; the hypothesis that must be consumed is conservativity of the
`(a, 1)` family, which is what fails in the example above.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MarkovProcess Set
open SubdiffusiveProcess.Frozen.Section7
open scoped NNReal

noncomputable section

variable {Theta : Type*} {d : ℕ} {a : Theta → State d → ℝ} {theta : Theta}

/-- **Clock divergence along a path with a bounded coefficient.**  If the
coefficient is bounded above along a path, the reciprocal clock of that path is
unbounded. -/
theorem mem_timeChangeUnboundedEvent_of_le_on_path
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d)) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ r : ℝ, 0 ≤ r → a theta (omega (Real.toNNReal r)) ≤ C) :
    omega ∈ timeChangeUnboundedEvent a theta := by
  refine (mem_timeChangeUnboundedEvent_iff ha hapos omega).mpr ?_
  refine timeChangeAdditiveClock_unbounded_of_lower_bound
    (continuous_timeChangePathIntegrand ha hapos omega) (inv_pos.mpr hC) ?_
  intro r hr
  exact (inv_le_inv₀ hC (hapos _)).mpr (hbound r hr)

/-- **Clock divergence along a path with bounded range.**  A continuous
coefficient is bounded on compacta, so the reciprocal clock diverges along every
path that stays in a bounded set. -/
theorem mem_timeChangeUnboundedEvent_of_isBounded_range
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d))
    (hb : Bornology.IsBounded (Set.range (omega : NNReal → State d))) :
    omega ∈ timeChangeUnboundedEvent a theta := by
  obtain ⟨xmax, hxmax, hmax⟩ := hb.isCompact_closure.exists_isMaxOn
    ⟨omega 0, subset_closure (Set.mem_range_self 0)⟩ ha.continuousOn
  refine mem_timeChangeUnboundedEvent_of_le_on_path ha hapos omega (hapos xmax) ?_
  intro r _
  exact hmax (subset_closure (Set.mem_range_self (Real.toNNReal r)))

/-- **Clock divergence for a globally bounded coefficient.**  If the coefficient
has a global upper bound then the reciprocal clock diverges along every path, so
the almost-sure divergence hypothesis of the frozen anchor is unconditional. -/
theorem timeChangeUnboundedEvent_eq_univ_of_bounded
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ x, a theta x ≤ C) :
    timeChangeUnboundedEvent a theta = Set.univ := by
  refine Set.eq_univ_of_forall fun omega ↦ ?_
  exact mem_timeChangeUnboundedEvent_of_le_on_path ha hapos omega hC
    (fun r _ ↦ hbound _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
