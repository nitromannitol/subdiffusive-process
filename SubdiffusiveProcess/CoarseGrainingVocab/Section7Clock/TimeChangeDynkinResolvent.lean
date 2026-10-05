module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeBoundedClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeMarginalIdentification
public import MarkovProcess.Trajectory.DynkinStopping

@[expose] public section

/-!
# The time-changed Dynkin step and the manuscript's resolvent identity

This file proves the manuscript's identity 

`E_x ∫₀^∞ e^{-mu A_s} a(X_s)⁻¹ f(X_s) ds = R^{(a,1)}_mu f (x)`

for a coefficient bounded above and below, i.e. the input `(R2a)` that the time-change resolvent argument
isolated as the single remaining producer of the frozen anchor

The printed proof applies Dynkin's formula to the multiplicative functional
`e^{-mu A_t} g(X_t)`.  No stochastic calculus for multiplicative functionals is
available in `MarkovProcess`, and none is needed here: under two-sided bounds on
`a` the inverse clock `θ_t` is a **bounded** stopping time
(`TimeChangeBoundedClock`), so optional stopping applies to the ordinary Dynkin
martingale at `θ_t` and gives the *time-changed* Dynkin formula

`E_x g(Y_t) − g(x) = E_x ∫₀ᵗ (a L_X g)(Y_u) du`,

`Y = X ∘ θ`.  With `L_X g = a⁻¹ (mu g − f)` — the generator identity proved in
`TimeChangeWeakGenerator` from the two weak elliptic characterizations — this is
a scalar linear ordinary differential equation for `t ↦ E_x g(Y_t)`, and
integrating `e^{-mu t}` against it produces the resolvent identity.  The
deterministic multiplicative functional `e^{-mu t}` replaces the pathwise one.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.Frozen.Section7
open scoped ENNReal NNReal ZeroAtInfty Topology

noncomputable section

variable {Theta : Type*} {d : ℕ} {a : Theta → State d → ℝ} {theta : Theta}

/-! ### The pathwise change of variables on a finite horizon -/

/-- **The occupation change of variables on a finite horizon.**  This is the
Revuz substitution `t = A_s`  on
`[0, s0]`, for Bochner integrals of a continuous integrand. -/
theorem intervalIntegral_timeChangePathIntegrand_mul
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) {omega : ContinuousPath (State d)}
    (homega : omega ∈ timeChangeUnboundedEvent a theta)
    (k : C₀(State d, ℝ)) {s0 : ℝ} (hs0 : 0 ≤ s0) :
    (∫ s in (0 : ℝ)..s0,
        timeChangePathIntegrand a theta omega s * k (omega (Real.toNNReal s))) =
      ∫ u in (0 : ℝ)..(timeChangePathClock a theta omega s0),
        k (measurableTimeChangedContinuousPath a theta ha hapos default omega
          (Real.toNNReal u)) := by
  classical
  have hunb := (mem_timeChangeUnboundedEvent_iff ha hapos omega).mp homega
  set A := timeChangePathClock a theta omega with hA
  set b := timeChangePathIntegrand a theta omega with hb
  have hbcont : Continuous b := continuous_timeChangePathIntegrand ha hapos omega
  have hAcont : Continuous A := (timeChangePathClock_regular ha hapos omega).1
  have hA0 : A 0 = 0 := (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
  set g : ℝ → ℝ := fun u ↦
    k (measurableTimeChangedContinuousPath a theta ha hapos default omega
      (Real.toNNReal u)) with hg
  have hgcont : Continuous g := by
    refine k.continuous.comp ?_
    exact (measurableTimeChangedContinuousPath a theta ha hapos default omega).continuous.comp
      continuous_real_toNNReal
  have hcompose : ∀ s : ℝ, 0 ≤ s → (g ∘ A) s = k (omega (Real.toNNReal s)) := by
    intro s hs
    have hpath : measurableTimeChangedContinuousPath a theta ha hapos default omega
        (Real.toNNReal (A s)) = omega (Real.toNNReal s) := by
      rw [measurableTimeChangedContinuousPath_eq_timeChangedPath ha hapos default homega]
      exact timeChangedContinuousPath_apply_clock omega A
        (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
        (timeChangePathClock_core_clauses ha hapos 0 omega).1
        (timeChangePathClock_regular ha hapos omega).2
        (timeChangePathClock_regular ha hapos omega).1 hunb hs
    simp only [Function.comp_apply, hg, hpath]
  have hcongr : (∫ s in (0 : ℝ)..s0, b s * k (omega (Real.toNNReal s))) =
      ∫ s in (0 : ℝ)..s0, b s • (g ∘ A) s := by
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [Set.uIcc_of_le hs0] at hs
    rw [smul_eq_mul, hcompose s hs.1]
  rw [hcongr]
  have hchange := intervalIntegral.integral_deriv_smul_comp'' (a := (0 : ℝ)) (b := s0)
    (f := A) (f' := b) (g := g) hAcont.continuousOn ?_ hbcont.continuousOn hgcont.continuousOn
  · rw [hchange, hA0]
  · intro x hx
    rw [min_eq_left hs0, max_eq_right hs0] at hx
    exact (hasDerivWithinAt_timeChangeAdditiveClock hbcont hx.1).mono
      (fun y hy ↦ lt_trans hx.1 hy)

/-- The occupation change of variables read at the inverse clock: the upper
limit is exactly `t`. -/
theorem intervalIntegral_timeChangePathIntegrand_mul_inverse
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) {omega : ContinuousPath (State d)}
    (homega : omega ∈ timeChangeUnboundedEvent a theta)
    (k : C₀(State d, ℝ)) (t : NNReal) :
    (∫ s in (0 : ℝ)..((timeChangeRationalInverseNNReal a theta t omega : NNReal) : ℝ),
        timeChangePathIntegrand a theta omega s * k (omega (Real.toNNReal s))) =
      ∫ u in (0 : ℝ)..(t : ℝ),
        k (measurableTimeChangedContinuousPath a theta ha hapos default omega
          (Real.toNNReal u)) := by
  rw [intervalIntegral_timeChangePathIntegrand_mul ha hapos default homega k
    (NNReal.coe_nonneg _),
    timeChangePathClock_timeChangeRationalInverseNNReal ha hapos homega t]

/-! ### The one-dimensional expectations of the time-changed process -/

/-- The expectation of a `C₀` test at time `u` under the time-changed process. -/
def timeChangedMarginal (P : SubMarkovKernelSemigroup (State d)) (hP : P.IsConservative)
    (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (k : C₀(State d, ℝ)) (y : State d) (u : ℝ) : ℝ :=
  ∫ eta, k (eta (Real.toNNReal u)) ∂(timeChangedProcess P hP a theta ha hapos default y)

variable {P : SubMarkovKernelSemigroup (State d)}

theorem timeChangedMarginal_eq_integral (hP : P.IsConservative)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (k : C₀(State d, ℝ)) (y : State d) (u : ℝ) :
    timeChangedMarginal P hP a theta ha hapos default k y u =
      ∫ omega, k (measurableTimeChangedContinuousPath a theta ha hapos default omega
          (Real.toNNReal u))
        ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP y) := by
  rw [timeChangedMarginal, timeChangedProcess_apply P hP ha hapos default y]
  exact integral_map
    (measurable_measurableTimeChangedContinuousPath ha hapos default).aemeasurable
    ((k.continuous.comp (ContinuousPath.continuous_coordinateProcess
      (Real.toNNReal u))).aestronglyMeasurable)

theorem continuous_timeChangedMarginal (hP : P.IsConservative)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (k : C₀(State d, ℝ)) (y : State d) :
    Continuous (timeChangedMarginal P hP a theta ha hapos default k y) := by
  have : IsProbabilityMeasure (timeChangedProcess P hP a theta ha hapos default y) :=
    IsMarkovKernel.isProbabilityMeasure y
  exact continuous_integral_coordinate k (timeChangedProcess P hP a theta ha hapos default y)

theorem abs_timeChangedMarginal_le (hP : P.IsConservative)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (k : C₀(State d, ℝ)) (y : State d) (u : ℝ) :
    |timeChangedMarginal P hP a theta ha hapos default k y u| ≤ ‖k.toBCF‖ := by
  have : IsProbabilityMeasure (timeChangedProcess P hP a theta ha hapos default y) :=
    IsMarkovKernel.isProbabilityMeasure y
  exact abs_integral_coordinate_le k (timeChangedProcess P hP a theta ha hapos default y) u

theorem timeChangedMarginal_smul_sub (hP : P.IsConservative)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (r : ℝ) (k l : C₀(State d, ℝ))
    (y : State d) (u : ℝ) :
    timeChangedMarginal P hP a theta ha hapos default (r • k - l) y u =
      r * timeChangedMarginal P hP a theta ha hapos default k y u -
        timeChangedMarginal P hP a theta ha hapos default l y u := by
  have : IsProbabilityMeasure (timeChangedProcess P hP a theta ha hapos default y) :=
    IsMarkovKernel.isProbabilityMeasure y
  have hk : Integrable (fun eta : ContinuousPath (State d) ↦ k (eta (Real.toNNReal u)))
      (timeChangedProcess P hP a theta ha hapos default y) :=
    Integrable.of_bound ((k.continuous.comp
      (ContinuousPath.continuous_coordinateProcess (Real.toNNReal u))).aestronglyMeasurable)
      ‖k.toBCF‖ (Filter.Eventually.of_forall fun eta ↦ k.toBCF.norm_coe_le_norm _)
  have hl : Integrable (fun eta : ContinuousPath (State d) ↦ l (eta (Real.toNNReal u)))
      (timeChangedProcess P hP a theta ha hapos default y) :=
    Integrable.of_bound ((l.continuous.comp
      (ContinuousPath.continuous_coordinateProcess (Real.toNNReal u))).aestronglyMeasurable)
      ‖l.toBCF‖ (Filter.Eventually.of_forall fun eta ↦ l.toBCF.norm_coe_le_norm _)
  simp only [timeChangedMarginal, ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply,
    ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [integral_sub (hk.const_mul r) hl, integral_const_mul]

/-! ### Measurability of a stopped time integral -/

/-- The integral of a continuous function along a path, up to a Borel measurable
random time, is Borel measurable.

This replaces the library's `integrable_integral_generator_stoppingTime`, which
is available only for an element of the `C₀` generator domain; here the
integrand is an arbitrary continuous function and no domain membership is
assumed. -/
theorem measurable_intervalIntegral_randomTime {w : State d → ℝ} (hw : Continuous w)
    (T : ContinuousPath (State d) → NNReal) (hT : Measurable T) :
    Measurable (fun omega : ContinuousPath (State d) ↦
      ∫ s in (0 : ℝ)..((T omega : NNReal) : ℝ), w (omega (Real.toNNReal s))) := by
  classical
  set S : Set (ContinuousPath (State d) × ℝ) :=
    {p | p.2 ∈ Set.Ioc (0 : ℝ) ((T p.1 : NNReal) : ℝ)} with hS
  have hTreal : Measurable (fun p : ContinuousPath (State d) × ℝ ↦ ((T p.1 : NNReal) : ℝ)) :=
    (NNReal.continuous_coe.measurable.comp hT).comp measurable_fst
  have hSmeas : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd hTreal)
  have hval : Measurable (fun p : ContinuousPath (State d) × ℝ ↦ w (p.1 (Real.toNNReal p.2))) :=
    hw.measurable.comp
      ((ContinuousEval.continuous_eval (F := ContinuousPath (State d))).measurable.comp
        (measurable_fst.prodMk (continuous_real_toNNReal.measurable.comp measurable_snd)))
  have hind : Measurable (S.indicator
      (fun p : ContinuousPath (State d) × ℝ ↦ w (p.1 (Real.toNNReal p.2)))) :=
    hval.indicator hSmeas
  have heq : (fun omega : ContinuousPath (State d) ↦
        ∫ s in (0 : ℝ)..((T omega : NNReal) : ℝ), w (omega (Real.toNNReal s))) =
      fun omega : ContinuousPath (State d) ↦ ∫ s,
        S.indicator (fun p : ContinuousPath (State d) × ℝ ↦ w (p.1 (Real.toNNReal p.2)))
          (omega, s) := by
    funext omega
    rw [intervalIntegral.integral_of_le (T omega).coe_nonneg,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    rfl
  rw [heq]
  exact (hind.stronglyMeasurable.integral_prod_right').measurable

/-! ### The time-changed Dynkin formula from a stopped Dynkin identity -/

/-- **The time-changed Dynkin formula from a stopped Dynkin identity.**

This is `timeChanged_dynkin_of_divergence` with its only probabilistic input
isolated as a hypothesis: instead of asking that `g` lie in the `C₀` generator
domain of the input process — which is the generator-domain argument's obstruction `(C0)`, a decay
statement about `a⁻¹` at infinity — it asks only that Dynkin's formula

  `E_y g(X_T) − g(y) = E_y ∫₀^T (a⁻¹ kappa)(X_s) ds`

hold at every stopping time `T` bounded by a deterministic horizon.  That is
exactly the conclusion the **local** Dynkin formula delivers for a function
which lies in the generator domain only locally (the generator-domain argument's named missing library
theorem), and it carries no condition at infinity.

The `C₀` generator domain enters the library's optional stopping only through
this identity and through two measurability statements, both of which are
re-proved here for an arbitrary continuous integrand
(`measurable_intervalIntegral_randomTime`). -/
theorem timeChanged_dynkin_of_stoppedDynkin (hP : P.IsConservative)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d))
    (g kappa : C₀(State d, ℝ)) (y : State d)
    (hdynkin : ∀ T : ContinuousPath (State d) → NNReal,
      IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := State d))
        (fun omega ↦ ((T omega : NNReal) : WithTop NNReal)) →
      ∀ K : NNReal, (∀ omega, T omega ≤ K) →
        (∫ omega, g (omega (T omega))
            ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP y)) - g y =
          ∫ omega, (∫ s in (0 : ℝ)..((T omega : NNReal) : ℝ),
              (a theta (omega (Real.toNNReal s)))⁻¹ * kappa (omega (Real.toNNReal s)))
            ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP y))
    (hdiv : ∀ᵐ omega ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP y),
      omega ∈ timeChangeUnboundedEvent a theta)
    (t : NNReal) :
    timeChangedMarginal P hP a theta ha hapos default g y (t : ℝ) - g y =
      ∫ u in (0 : ℝ)..(t : ℝ), timeChangedMarginal P hP a theta ha hapos default kappa y u := by
  classical
  set Q := SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP y with hQ
  have : IsProbabilityMeasure Q := IsMarkovKernel.isProbabilityMeasure y
  set w : State d → ℝ := fun x ↦ (a theta x)⁻¹ * kappa x with hw
  have hwcont : Continuous w :=
    (ha.inv₀ fun x ↦ ne_of_gt (hapos x)).mul kappa.continuous
  set Tn : ℕ → ContinuousPath (State d) → NNReal :=
    fun n omega ↦ truncatedInverseClock a theta t n omega with hTn
  have hTstop : ∀ n : ℕ, IsStoppingTime
      (ContinuousPath.canonicalFiltration (alpha := State d))
      (fun omega ↦ ((Tn n omega : NNReal) : WithTop NNReal)) := fun n ↦
    isStoppingTime_truncatedInverseClock ha hapos default t n
  have hTK : ∀ (n : ℕ) (omega : ContinuousPath (State d)), Tn n omega ≤ (n : NNReal) :=
    fun n omega ↦ truncatedInverseClock_le a theta t n omega
  have hTmeas : ∀ n : ℕ, Measurable (Tn n) := fun n ↦
    ContinuousPath.measurable_of_isStoppingTime (Tn n) (hTstop n)
  -- Dynkin at every truncation level
  have hdyn : ∀ n : ℕ,
      (∫ omega, g (omega (Tn n omega)) ∂Q) - g y =
        ∫ omega, (∫ s in (0 : ℝ)..((Tn n omega : NNReal) : ℝ),
          w (omega (Real.toNNReal s))) ∂Q := fun n ↦
    hdynkin (Tn n) (hTstop n) (n : NNReal) (hTK n)
  -- the Dynkin correction, after the Revuz substitution
  have hcorr : ∀ (n : ℕ) {omega : ContinuousPath (State d)},
      omega ∈ timeChangeUnboundedEvent a theta →
      (∫ s in (0 : ℝ)..((Tn n omega : NNReal) : ℝ), w (omega (Real.toNNReal s))) =
        ∫ u in (0 : ℝ)..(timeChangePathClock a theta omega ((Tn n omega : NNReal) : ℝ)),
          kappa (measurableTimeChangedContinuousPath a theta ha hapos default omega
            (Real.toNNReal u)) := by
    intro n omega homega
    rw [← intervalIntegral_timeChangePathIntegrand_mul ha hapos default homega kappa
      (NNReal.coe_nonneg _)]
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    rfl
  -- the horizon after which the truncation is inactive
  have hstab : ∀ {omega : ContinuousPath (State d)},
      omega ∈ timeChangeUnboundedEvent a theta →
      ∀ n : ℕ, ⌈timeChangeRationalInverseNNReal a theta t omega⌉₊ ≤ n →
        Tn n omega = timeChangeRationalInverseNNReal a theta t omega := by
    intro omega homega n hn
    refine truncatedInverseClock_eq_of_le ha hapos homega t ?_
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  -- convergence of the stopped values
  have hF : Tendsto (fun n : ℕ ↦ ∫ omega, g (omega (Tn n omega)) ∂Q) atTop
      (𝓝 (∫ omega, g (measurableTimeChangedContinuousPath a theta ha hapos default omega
        (Real.toNNReal (t : ℝ))) ∂Q)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ ‖g.toBCF‖)
      (fun n ↦ ?_) (integrable_const _) (fun n ↦ ?_) ?_
    · exact (g.continuous.measurable.comp
        (ContinuousPath.measurable_eval_stoppingTime_borel (Tn n)
          (hTstop n))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun omega ↦ g.toBCF.norm_coe_le_norm _
    · filter_upwards [hdiv] with omega homega
      refine tendsto_atTop_of_eventually_const
        (i₀ := ⌈timeChangeRationalInverseNNReal a theta t omega⌉₊) fun n hn ↦ ?_
      rw [hstab homega n hn, Real.toNNReal_coe,
        measurableTimeChangedContinuousPath_eq_apply_inverse ha hapos default homega t]
  -- convergence of the Dynkin correction
  have hG : Tendsto (fun n : ℕ ↦ ∫ omega, (∫ s in (0 : ℝ)..((Tn n omega : NNReal) : ℝ),
        w (omega (Real.toNNReal s))) ∂Q) atTop
      (𝓝 (∫ omega, (∫ u in (0 : ℝ)..(t : ℝ),
        kappa (measurableTimeChangedContinuousPath a theta ha hapos default omega
          (Real.toNNReal u))) ∂Q)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ ‖kappa.toBCF‖ * (t : ℝ))
      (fun n ↦ ?_) (integrable_const _) (fun n ↦ ?_) ?_
    · exact (measurable_intervalIntegral_randomTime hwcont (Tn n)
        (hTmeas n)).aestronglyMeasurable
    · filter_upwards [hdiv] with omega homega
      rw [hcorr n homega]
      have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := timeChangePathClock a theta omega ((Tn n omega : NNReal) : ℝ))
        (C := ‖kappa.toBCF‖)
        (f := fun u : ℝ ↦ kappa (measurableTimeChangedContinuousPath a theta ha hapos default
          omega (Real.toNNReal u)))
        (fun u _ ↦ kappa.toBCF.norm_coe_le_norm _)
      refine hbnd.trans ?_
      rw [sub_zero, abs_of_nonneg
        (timeChangePathClock_truncatedInverseClock_nonneg ha hapos omega t n)]
      exact mul_le_mul_of_nonneg_left
        (timeChangePathClock_truncatedInverseClock_le ha hapos homega t n) (norm_nonneg _)
    · filter_upwards [hdiv] with omega homega
      refine tendsto_atTop_of_eventually_const
        (i₀ := ⌈timeChangeRationalInverseNNReal a theta t omega⌉₊) fun n hn ↦ ?_
      rw [hcorr n homega, hstab homega n hn,
        timeChangePathClock_timeChangeRationalInverseNNReal ha hapos homega t]
  have hlim : (∫ omega, g (measurableTimeChangedContinuousPath a theta ha hapos default omega
        (Real.toNNReal (t : ℝ))) ∂Q) - g y =
      ∫ omega, (∫ u in (0 : ℝ)..(t : ℝ),
        kappa (measurableTimeChangedContinuousPath a theta ha hapos default omega
          (Real.toNNReal u))) ∂Q := by
    refine tendsto_nhds_unique (hF.sub_const (g y)) ?_
    exact hG.congr fun n ↦ (hdyn n).symm
  rw [timeChangedMarginal_eq_integral hP ha hapos default g y (t : ℝ), hlim]
  -- Fubini
  have hle : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
  simp only [intervalIntegral.integral_of_le hle]
  have hmeas : Measurable (Function.uncurry
      (fun (omega : ContinuousPath (State d)) (u : ℝ) ↦
        kappa (measurableTimeChangedContinuousPath a theta ha hapos default omega
          (Real.toNNReal u)))) :=
    kappa.continuous.measurable.comp
      (measurable_uncurry_measurableTimeChangedContinuousPath ha hapos default)
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) := by
    constructor
    simp
  have hint : Integrable (Function.uncurry
      (fun (omega : ContinuousPath (State d)) (u : ℝ) ↦
        kappa (measurableTimeChangedContinuousPath a theta ha hapos default omega
          (Real.toNNReal u))))
      (Q.prod (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ)))) :=
    Integrable.of_bound hmeas.aestronglyMeasurable ‖kappa.toBCF‖
      (Filter.Eventually.of_forall fun p ↦ kappa.toBCF.norm_coe_le_norm _)
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ ↦ ?_
  rw [timeChangedMarginal_eq_integral hP ha hapos default kappa y u]

/-! ### The time-changed Dynkin formula under clock divergence alone -/

/-- **The time-changed Dynkin formula from almost-sure clock divergence.**
Optional stopping at the *truncated* inverse clock `θ_t ∧ n` needs no bound on
the coefficient; the truncation is a bounded stopping time for every `n`, and on
the divergence event it equals `θ_t` for all large `n`, so dominated convergence
removes the truncation.  The dominating bound on the Dynkin correction is the
Revuz change of variables itself: after substitution the correction is an
integral over `[0, A(θ_t ∧ n)] ⊆ [0, t]`. -/
theorem timeChanged_dynkin_of_divergence (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d))
    (g : C₀(State d, ℝ)) (hmem : g ∈ hFeller.c0Semigroup.generatorDomain)
    (kappa : C₀(State d, ℝ))
    (hgen : ∀ x, hFeller.c0Semigroup.generator ⟨g, hmem⟩ x = (a theta x)⁻¹ * kappa x)
    (y : State d)
    (hdiv : ∀ᵐ omega ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP y),
      omega ∈ timeChangeUnboundedEvent a theta)
    (t : NNReal) :
    timeChangedMarginal P hP a theta ha hapos default g y (t : ℝ) - g y =
      ∫ u in (0 : ℝ)..(t : ℝ), timeChangedMarginal P hP a theta ha hapos default kappa y u := by
  refine timeChanged_dynkin_of_stoppedDynkin hP ha hapos default g kappa y ?_ hdiv t
  intro T hT K hTK
  have hcoe : ((⟨g, hmem⟩ : hFeller.c0Semigroup.generatorDomain) : C₀(State d, ℝ)) = g := rfl
  have h := hFeller.integral_eval_stoppingTime_sub_eq_integral_integral_generator
    hP hK ⟨g, hmem⟩ T hT hTK y
  rw [hcoe] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega ↦ ?_)
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  exact hgen _

/-! ### The resolvent identity -/

/-- **The manuscript's resolvent identity from the time-changed Dynkin
formula.**  This is the purely scalar half of
`timeChanged_resolvent_identity_of_divergence`: the ordinary differential
equation `m' = mu m − E_y f(Y_t)` produced by the time-changed Dynkin identity
`hid`, integrated against `e^{-mu t}` on the half line.  No generator domain and
no clock divergence enter here; both are used only to produce `hid`. -/
theorem timeChanged_resolvent_identity_of_dynkinIdentity (hP : P.IsConservative)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) {mu : ℝ} (hmu : 0 < mu)
    (g f : C₀(State d, ℝ)) (y : State d)
    (hid : ∀ t : ℝ, 0 ≤ t →
      timeChangedMarginal P hP a theta ha hapos default g y t - g y =
        ∫ u in (0 : ℝ)..t,
          timeChangedMarginal P hP a theta ha hapos default (mu • g - f) y u) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(mu * t)) *
        (∫ omega, f (measurableTimeChangedContinuousPath a theta ha hapos default omega
            (Real.toNNReal t))
          ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP y))) = g y := by
  classical
  set kappa : C₀(State d, ℝ) := mu • g - f with hkappa
  have hkappa_apply : ∀ x, kappa x = mu * g x - f x := by
    intro x
    simp [hkappa]
  set mg := timeChangedMarginal P hP a theta ha hapos default g y with hmg
  set mf := timeChangedMarginal P hP a theta ha hapos default f y with hmf
  set mk := timeChangedMarginal P hP a theta ha hapos default kappa y with hmkdef
  have hmk : ∀ u : ℝ, mk u = mu * mg u - mf u := fun u ↦
    timeChangedMarginal_smul_sub hP ha hapos default mu g f y u
  have hmkcont : Continuous mk := continuous_timeChangedMarginal hP ha hapos default kappa y
  have hmfcont : Continuous mf := continuous_timeChangedMarginal hP ha hapos default f y
  -- the primitive
  set M : ℝ → ℝ := fun t ↦ g y + ∫ u in (0 : ℝ)..t, mk u with hMdef
  have hMg : ∀ t : ℝ, 0 ≤ t → M t = mg t := by
    intro t ht
    have := hid t ht
    simp only [hMdef]
    linarith
  have hMderiv : ∀ t : ℝ, HasDerivAt M (mk t) t := by
    intro t
    have hprim : HasDerivAt (fun u : ℝ ↦ ∫ r in (0 : ℝ)..u, mk r) (mk t) t :=
      intervalIntegral.integral_hasDerivAt_right (hmkcont.intervalIntegrable _ _)
        (hmkcont.stronglyMeasurableAtFilter _ _) hmkcont.continuousAt
    simpa only [hMdef] using hprim.const_add (g y)
  have hMcont : Continuous M := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    exact (hMderiv t).continuousAt
  -- the exponentially damped primitive
  have hexp : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ Real.exp (-(mu * s)))
      (-mu * Real.exp (-(mu * t))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ ↦ -(mu * s)) (-mu) t := by
      simpa using! ((hasDerivAt_id t).const_mul mu).neg
    simpa [mul_comm] using h1.exp
  set N : ℝ → ℝ := fun t ↦ Real.exp (-(mu * t)) * M t with hNdef
  have hNderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt N (-(Real.exp (-(mu * x)) * mf x)) x := by
    intro x hx
    have hd := (hexp x).mul (hMderiv x)
    have heq : (-mu * Real.exp (-(mu * x))) * M x + Real.exp (-(mu * x)) * mk x =
        -(Real.exp (-(mu * x)) * mf x) := by
      rw [hmk x, ← hMg x (le_of_lt hx)]
      ring
    rw [heq] at hd
    exact hd
  have hNcont : Continuous N := (Real.continuous_exp.comp
    ((continuous_const.mul continuous_id).neg)).mul hMcont
  -- the derivative is integrable on the half line
  have hfint : IntegrableOn (fun t : ℝ ↦ -(Real.exp (-(mu * t)) * mf t)) (Ioi (0 : ℝ)) := by
    refine Integrable.neg ?_
    refine Integrable.mono' ((exp_neg_integrableOn_Ioi (0 : ℝ) hmu).const_mul ‖f.toBCF‖)
      (((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).mul
        hmfcont).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun t ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul,
      mul_comm ‖f.toBCF‖ (Real.exp (-(mu * t)))]
    exact mul_le_mul_of_nonneg_left (abs_timeChangedMarginal_le hP ha hapos default f y t)
      (Real.exp_pos _).le
  -- the boundary term vanishes
  have hNlim : Tendsto N atTop (𝓝 0) := by
    have hbound : ∀ᶠ t : ℝ in atTop, ‖N t‖ ≤ Real.exp (-(mu * t)) * ‖g.toBCF‖ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [hNdef]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [hMg t ht]
      exact abs_timeChangedMarginal_le hP ha hapos default g y t
    have hmul : Tendsto (fun t : ℝ ↦ mu * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hmu Filter.tendsto_id
    have h1 : Tendsto (fun t : ℝ ↦ -(mu * t)) atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp hmul
    have hexpTend : Tendsto (fun t : ℝ ↦ Real.exp (-(mu * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    refine squeeze_zero_norm' hbound ?_
    simpa using hexpTend.mul_const ‖g.toBCF‖
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := N) (f' := fun t ↦ -(Real.exp (-(mu * t)) * mf t)) (a := (0 : ℝ)) (m := (0 : ℝ))
    hNcont.continuousWithinAt hNderiv hfint hNlim
  have hN0 : N 0 = g y := by simp [hNdef, hMdef]
  rw [hN0] at hmain
  have hneg : (∫ t in Ioi (0 : ℝ), -(Real.exp (-(mu * t)) * mf t)) =
      -∫ t in Ioi (0 : ℝ), Real.exp (-(mu * t)) * mf t := by
    simp [integral_neg]
  rw [hneg] at hmain
  have hfinal : (∫ t in Ioi (0 : ℝ), Real.exp (-(mu * t)) * mf t) = g y := by linarith
  rw [← hfinal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [hmf, timeChangedMarginal_eq_integral hP ha hapos default f y t]

/-- **The manuscript's resolvent identity.**
If `g` lies in the domain of the `(a,a)` generator with
`L_X g = a⁻¹ (mu g − f)`, then the `mu`-Laplace transform of the one-dimensional
marginals of the time-changed process, evaluated at `f`, is `g` itself. -/
theorem timeChanged_resolvent_identity_of_divergence (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) {mu : ℝ} (hmu : 0 < mu)
    (g f : C₀(State d, ℝ)) (hmem : g ∈ hFeller.c0Semigroup.generatorDomain)
    (hgen : ∀ x, hFeller.c0Semigroup.generator ⟨g, hmem⟩ x =
      (a theta x)⁻¹ * (mu * g x - f x))
    (y : State d)
    (hdiv : ∀ᵐ omega ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP y),
      omega ∈ timeChangeUnboundedEvent a theta) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(mu * t)) *
        (∫ omega, f (measurableTimeChangedContinuousPath a theta ha hapos default omega
            (Real.toNNReal t))
          ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP y))) = g y := by
  refine timeChanged_resolvent_identity_of_dynkinIdentity hP ha hapos default hmu g f y ?_
  intro t ht
  have h := timeChanged_dynkin_of_divergence hP hFeller hK ha hapos default g hmem
    ((mu : ℝ) • g - f) (fun x ↦ by rw [hgen x]; simp) y hdiv (Real.toNNReal t)
  rwa [Real.coe_toNNReal t ht] at h


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
