module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeFiniteMarginals
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeLaplaceUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeClockDivergence
public import MarkovProcess.Trajectory.Dynkin
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

@[expose] public section

/-!
# The one-dimensional marginals from the resolvent identity

`TimeChangeFiniteMarginals` reduces the frozen time-change anchor
to almost-sure divergence of the clock
together with the **one-dimensional** marginals of the time-changed process.
`TimeChangeProcessOccupation` computes the Laplace transform of exactly those
marginals as an occupation integral of the input process.  What separates the
two is the passage from equality of Laplace transforms to equality of the
transformed functions, and from equality of `C₀` integrals to equality of
measures.

This file supplies both, so that the residual becomes the manuscript's scalar
identity  and nothing else:

* `continuous_integral_coordinate` — the one-dimensional expectations of a
  continuous-path law are continuous in time (dominated convergence along the
  paths), so Laplace-transform uniqueness applies to them;
* `timeChangedProcess_map_eval_of_laplace` — equality of the two Laplace
  transforms for every `C₀` test function forces the one-dimensional marginals
  of the time-changed process to be the transition kernels of the target
  semigroup.

Nothing here assumes the missing analytic producer; the producer is exactly the
hypothesis `hlaplace`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.Frozen.Section7
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {Theta : Type*} {d : ℕ} {a : Theta → State d → ℝ} {theta : Theta}

/-! ### Time continuity of the one-dimensional expectations -/

/-- The expectation of a `C₀` function of the position at time `t` under a fixed
continuous-path law is continuous in `t`. -/
theorem continuous_integral_coordinate (f : C₀(State d, ℝ))
    (mu : Measure (ContinuousPath (State d))) [IsFiniteMeasure mu] :
    Continuous (fun t : ℝ ↦ ∫ omega, f (omega (Real.toNNReal t)) ∂mu) := by
  refine continuous_of_dominated (bound := fun _ ↦ ‖f.toBCF‖) (fun t ↦ ?_) (fun t ↦ ?_)
    (integrable_const _) ?_
  · exact (f.continuous.comp
      (ContinuousPath.continuous_coordinateProcess (Real.toNNReal t))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega ↦
      f.toBCF.norm_coe_le_norm (omega (Real.toNNReal t))
  · refine Filter.Eventually.of_forall fun omega ↦ ?_
    exact f.continuous.comp (omega.continuous.comp continuous_real_toNNReal)

/-- The one-dimensional expectations of a `C₀` function under a probability law
on paths are bounded by the sup norm of the function. -/
theorem abs_integral_coordinate_le (f : C₀(State d, ℝ))
    (mu : Measure (ContinuousPath (State d))) [IsProbabilityMeasure mu] (t : ℝ) :
    |∫ omega, f (omega (Real.toNNReal t)) ∂mu| ≤ ‖f.toBCF‖ := by
  have h := norm_integral_le_of_norm_le_const (μ := mu)
    (f := fun omega : ContinuousPath (State d) ↦ f (omega (Real.toNNReal t)))
    (C := ‖f.toBCF‖)
    (Filter.Eventually.of_forall fun omega ↦ f.toBCF.norm_coe_le_norm _)
  simpa using h

/-! ### From the Laplace identity to the one-dimensional marginals -/

/-- **The one-dimensional marginals of the time-changed process from the
resolvent identity.**  If for every `C₀` test function and every positive `mu`
the `mu`-Laplace transform of the one-dimensional expectations of the
time-changed process is the `mu`-Laplace transform of the transition semigroup
`PY`, then the one-dimensional marginals of the time-changed process are the
transition kernels of `PY`.

The two ingredients are Laplace-transform uniqueness for bounded continuous
functions on the half line (`eq_of_forall_integral_exp_neg_mul_eq`, proved in
`TimeChangeLaplaceUniqueness`, absent from Mathlib) and the Riesz–Markov
determination of a regular measure by its integrals against compactly supported
continuous functions. -/
theorem timeChangedProcess_map_eval_of_laplace
    (P : SubMarkovKernelSemigroup (State d)) (hP : P.IsConservative)
    (PY : SubMarkovKernelSemigroup (State d)) (hPY : PY.IsConservative)
    (hFellerY : PY.IsFellerKernelSemigroup) (hKY : PY.KolmogorovRegular hPY)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d))
    (hlaplace : ∀ (f : C₀(State d, ℝ)) (mu : ℝ), 0 < mu → ∀ y : State d,
      ∫ t in Ioi (0:ℝ), Real.exp (-(mu * t)) *
          (∫ omega, f (measurableTimeChangedContinuousPath a theta ha hapos default omega
              (Real.toNNReal t))
            ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP y)) =
        ∫ t in Ioi (0:ℝ), Real.exp (-(mu * t)) *
          kernelIntegral (PY (Real.toNNReal t)) (fun z ↦ f z) y)
    (y : State d) (s : NNReal) :
    (timeChangedProcess P hP a theta ha hapos default y).map
        (fun eta : ContinuousPath (State d) ↦ eta s) = PY s y := by
  set QY := SubMarkovKernelSemigroup.IsConservative.continuousProcess PY hPY with hQY
  have hPsiMeas : Measurable (measurableTimeChangedContinuousPath a theta ha hapos default) :=
    measurable_measurableTimeChangedContinuousPath ha hapos default
  -- the two one-dimensional expectation functions
  have hkey : ∀ f : C₀(State d, ℝ),
      ∫ z, f z ∂((timeChangedProcess P hP a theta ha hapos default y).map
          (fun eta : ContinuousPath (State d) ↦ eta s)) =
        ∫ z, f z ∂(PY s y) := by
    intro f
    -- the time-changed side
    have hFdef : ∀ t : ℝ,
        (∫ eta, f (eta (Real.toNNReal t))
            ∂(timeChangedProcess P hP a theta ha hapos default y)) =
          ∫ omega, f (measurableTimeChangedContinuousPath a theta ha hapos default omega
              (Real.toNNReal t))
            ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP y) := by
      intro t
      rw [timeChangedProcess_apply]
      exact integral_map (f := fun eta : ContinuousPath (State d) ↦ f (eta (Real.toNNReal t)))
        hPsiMeas.aemeasurable
        (f.continuous.comp
          (ContinuousPath.continuous_coordinateProcess (Real.toNNReal t))).aestronglyMeasurable
    -- the target side
    have hGdef : ∀ t : ℝ, (∫ eta, f (eta (Real.toNNReal t)) ∂(QY y)) =
        kernelIntegral (PY (Real.toNNReal t)) (fun z ↦ f z) y := by
      intro t
      exact hFellerY.integral_eval_continuousProcess PY hPY hKY (Real.toNNReal t) y f
    -- Laplace-transform uniqueness
    have hcontF : Continuous (fun t : ℝ ↦
        ∫ eta, f (eta (Real.toNNReal t))
          ∂(timeChangedProcess P hP a theta ha hapos default y)) :=
      continuous_integral_coordinate f _
    have hcontG : Continuous (fun t : ℝ ↦ ∫ eta, f (eta (Real.toNNReal t)) ∂(QY y)) :=
      continuous_integral_coordinate f _
    have hlap' : ∀ mu : ℝ, 0 < mu →
        ∫ t in Ioi (0:ℝ), Real.exp (-(mu * t)) *
            (∫ eta, f (eta (Real.toNNReal t))
              ∂(timeChangedProcess P hP a theta ha hapos default y)) =
          ∫ t in Ioi (0:ℝ), Real.exp (-(mu * t)) *
            (∫ eta, f (eta (Real.toNNReal t)) ∂(QY y)) := by
      intro mu hmu
      rw [setIntegral_congr_fun measurableSet_Ioi
          (fun t _ ↦ congrArg (fun z ↦ Real.exp (-(mu * t)) * z) (hFdef t)),
        setIntegral_congr_fun measurableSet_Ioi
          (fun t _ ↦ congrArg (fun z ↦ Real.exp (-(mu * t)) * z) (hGdef t))]
      exact hlaplace f mu hmu y
    have heq := eq_of_forall_integral_exp_neg_mul_eq hcontF hcontG
      (fun t ↦ abs_integral_coordinate_le f _ t)
      (fun t ↦ abs_integral_coordinate_le f _ t) hlap' (s : ℝ) s.coe_nonneg
    have hmapint : ∫ z, f z ∂((timeChangedProcess P hP a theta ha hapos default y).map
        (fun eta : ContinuousPath (State d) ↦ eta s)) =
          ∫ eta, f (eta s) ∂(timeChangedProcess P hP a theta ha hapos default y) :=
      integral_map (f := fun z : State d ↦ f z)
        (ContinuousPath.measurable_coordinateProcess s).aemeasurable
        f.continuous.aestronglyMeasurable
    calc ∫ z, f z ∂((timeChangedProcess P hP a theta ha hapos default y).map
            (fun eta : ContinuousPath (State d) ↦ eta s))
        = ∫ eta, f (eta s) ∂(timeChangedProcess P hP a theta ha hapos default y) := hmapint
      _ = ∫ eta, f (eta (Real.toNNReal (s : ℝ)))
            ∂(timeChangedProcess P hP a theta ha hapos default y) := by
          rw [Real.toNNReal_coe]
      _ = ∫ eta, f (eta (Real.toNNReal (s : ℝ))) ∂(QY y) := heq
      _ = kernelIntegral (PY (Real.toNNReal (s : ℝ))) (fun z ↦ f z) y := hGdef (s : ℝ)
      _ = ∫ z, f z ∂(PY s y) := by rw [Real.toNNReal_coe]; rfl
  -- Riesz–Markov determination
  have : IsProbabilityMeasure ((timeChangedProcess P hP a theta ha hapos default y).map
      (fun eta : ContinuousPath (State d) ↦ eta s)) :=
    inferInstance
  have : IsMarkovKernel (PY s) := hPY.isMarkovKernel s
  have : IsProbabilityMeasure (PY s y) := IsMarkovKernel.isProbabilityMeasure y
  refine Measure.ext_of_integral_eq_on_compactlySupported fun g ↦ ?_
  exact hkey ⟨⟨fun z ↦ g z, map_continuous g⟩, zero_at_infty g⟩


/-! ### The frozen anchor from the clock divergence and the resolvent identity -/



theorem isIntrinsicTimeChange_of_clockDivergence_of_resolventIdentity [MeasurableSpace Theta]
    (a : Theta → State d → ℝ)
    (ha_pos : ∀ theta x, 0 < a theta x)
    (ha_cont : ∀ theta, Continuous (a theta))
    {DXDatum DYDatum : Theta →
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}
    (DX : GeneratedDiffusionFamily Theta d a a DXDatum)
    (DY : GeneratedDiffusionFamily Theta d a (fun _ _ ↦ 1) DYDatum)
    (PX : CemeteryDiffusion d DX) (PY : CemeteryDiffusion d DY)
    (default : Theta → ContinuousPath (State d))
    (hunbounded : ∀ theta y, ∀ᵐ omega ∂
      ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
        DX.semigroup DX.conservative (theta, y),
      omega ∈ timeChangeUnboundedEvent a theta)
    (hresolvent : ∀ (theta : Theta) (f : C₀(State d, ℝ))
        (mu : MarkovProcess.Semigroup.PositiveShift) (y : State d),
      ∫ t in Ioi (0:ℝ), Real.exp (-(mu : ℝ) * t) *
          (∫ omega, f (measurableTimeChangedContinuousPath a theta (ha_cont theta)
              (ha_pos theta) (default theta) omega (Real.toNNReal t))
            ∂(ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
                DX.semigroup DX.conservative (theta, y))) =
        (DYDatum theta).solution mu f y) :
    IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel PX.law)
      (Kernel.toLifetimePathKernel PY.law) := by
  refine isIntrinsicTimeChange_of_oneDimensional_marginals a ha_pos ha_cont DX DY PX PY
    default hunbounded ?_
  intro theta y t
  have hFellerY : (DY.semigroup.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup := by
    rw [DY.semigroup_eq theta]
    exact (DYDatum theta).isFellerKernelSemigroup_fellerKernelSemigroup (DY.denseRange theta)
  obtain ⟨p, q, M, hmom⟩ := DY.displacementMoments
  have hKY := ParameterizedSubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments
    DY.semigroup DY.conservative hmom theta
  refine timeChangedProcess_map_eval_of_laplace _ (DX.conservative theta) _
    (DY.conservative theta) hFellerY hKY (ha_cont theta) (ha_pos theta) (default theta) ?_ y t
  intro f mu hmu z
  have hres := hresolvent theta f ⟨mu, hmu⟩ z
  rw [(DYDatum theta).solution_eq_laplace (DY.denseRange theta) ⟨mu, hmu⟩ f z] at hres
  rw [← ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_apply
    DX.semigroup DX.conservative theta z]
  simp only [neg_mul] at hres
  refine hres.trans ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ ↦ ?_
  rw [DY.semigroup_eq theta]

/-- **The frozen v3 anchor for a globally bounded coefficient, from the
resolvent identity alone.**  When `a` is bounded above the reciprocal clock
diverges along every path (`timeChangeUnboundedEvent_eq_univ_of_bounded`), so
the only remaining input is the manuscript's resolvent identity. -/
theorem isIntrinsicTimeChange_of_resolventIdentity_of_bounded [MeasurableSpace Theta]
    (a : Theta → State d → ℝ)
    (ha_pos : ∀ theta x, 0 < a theta x)
    (ha_cont : ∀ theta, Continuous (a theta))
    {DXDatum DYDatum : Theta →
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}
    (DX : GeneratedDiffusionFamily Theta d a a DXDatum)
    (DY : GeneratedDiffusionFamily Theta d a (fun _ _ ↦ 1) DYDatum)
    (PX : CemeteryDiffusion d DX) (PY : CemeteryDiffusion d DY)
    (default : Theta → ContinuousPath (State d))
    (hbounded : ∀ theta, ∃ C : ℝ, 0 < C ∧ ∀ x, a theta x ≤ C)
    (hresolvent : ∀ (theta : Theta) (f : C₀(State d, ℝ))
        (mu : MarkovProcess.Semigroup.PositiveShift) (y : State d),
      ∫ t in Ioi (0:ℝ), Real.exp (-(mu : ℝ) * t) *
          (∫ omega, f (measurableTimeChangedContinuousPath a theta (ha_cont theta)
              (ha_pos theta) (default theta) omega (Real.toNNReal t))
            ∂(ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
                DX.semigroup DX.conservative (theta, y))) =
        (DYDatum theta).solution mu f y) :
    IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel PX.law)
      (Kernel.toLifetimePathKernel PY.law) := by
  refine isIntrinsicTimeChange_of_clockDivergence_of_resolventIdentity a ha_pos ha_cont
    DX DY PX PY default (fun theta y ↦ ?_) hresolvent
  obtain ⟨C, hC, hb⟩ := hbounded theta
  rw [timeChangeUnboundedEvent_eq_univ_of_bounded (ha_cont theta) (ha_pos theta) hC hb]
  exact Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
