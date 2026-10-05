module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeStoppingTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeShiftCocycle
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeProcessOccupation
public import MarkovProcess.Trajectory.StoppingLtTop

@[expose] public section

/-!
# The time-changed process is a Markov process

The manuscript's time change `Y_t = X_{θ_t}` 
is an inverse-additive-functional reparameterization, so the strong Markov
property of `X` at the stopping time `θ_t`, together with the shift cocycle of
the clock, makes `Y` a Markov process in restart form.

This file proves that.  The two inputs are

* `isStoppingTime_timeChangeRationalInverse` — the inverse clock is a
  stopping time of the canonical filtration, possibly infinite;
* `shift_timeChangedPath` — the time change intertwines the shift by `t` on
  the output with the shift by `θ_t` on the input;

and the library's strong Markov property at a possibly infinite stopping time,
`IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top`.

The conclusion, in event-restricted form, is that after restricting the input
law to an event of the stopped sigma-algebra of `θ_t`, the law of the
time-changed path shifted by `t` is the mixture of the time-changed laws over
the state at that time, which is `Y_t`.  Taking the event to be everything
gives the unrestricted Markov property.

Two things are still needed to turn this into the finite-dimensional
marginals of `Y`: the inclusion of the canonical filtration of `Y` at time `t`
in the stopped sigma-algebra of `θ_t` (so that the restricted form is a
genuine conditioning on the past of `Y`), and the identification of the
one-dimensional marginals of `Y` with the transition kernels of the `(a,1)`
semigroup.  The latter is the analytic producer that the frozen v3 anchor
still lacks; see `TimeChangeProcessOccupation` for its resolvent form.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess Set
open _root_.SubdiffusiveProcess.Section7
open scoped ENNReal NNReal

noncomputable section

variable {Theta : Type*} {d : ℕ} {a : Theta → State d → ℝ} {theta : Theta}

/-! ### Two elementary kernel-composition identities -/

/-- Composing with a comapped kernel is composing with the kernel after
pushing the measure forward. -/
theorem comap_comp_eq_comp_map {alpha beta gamma : Type*} [MeasurableSpace alpha]
    [MeasurableSpace beta] [MeasurableSpace gamma]
    (kappa : Kernel alpha beta) {f : gamma → alpha} (hf : Measurable f)
    (mu : Measure gamma) :
    (Kernel.comap kappa f hf) ∘ₘ mu = kappa ∘ₘ (mu.map f) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (kappa.measurable_coe hs) hf]
  simp only [Kernel.comap_apply]

/-- Mapping a comapped kernel is comapping the mapped kernel. -/
theorem map_comap_eq_comap_map {alpha beta gamma delta : Type*}
    [MeasurableSpace alpha] [MeasurableSpace beta] [MeasurableSpace gamma]
    [MeasurableSpace delta]
    (kappa : Kernel alpha beta) {f : gamma → alpha} (hf : Measurable f)
    {g : beta → delta} (hg : Measurable g) :
    (Kernel.comap kappa f hf).map g = Kernel.comap (kappa.map g) f hf := by
  refine Kernel.ext fun c ↦ ?_
  rw [Kernel.map_apply _ hg, Kernel.comap_apply, Kernel.comap_apply,
    Kernel.map_apply _ hg]

/-! ### The Markov property of the time-changed process -/

/-- **The time-changed process restarts.**  Under almost-sure divergence of
the reciprocal clock, the law of the time-changed process shifted by `t` is
the mixture of the time-changed laws over the law of the time-changed process
at time `t`.  This is the Markov property of `Y = X ∘ θ` in the restart form
used by `MarkovProcess`. -/
theorem timeChanged_restrict_map_shift
    (P : SubMarkovKernelSemigroup (State d)) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (x : State d) (t : NNReal)
    (hunb : ∀ᵐ omega ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP x),
      omega ∈ timeChangeUnboundedEvent a theta)
    (A : Set (ContinuousPath (State d)))
    (hA : MeasurableSet[(isStoppingTime_timeChangeRationalInverse
      (a := a) (theta := theta) ha hapos default t).measurableSpace] A) :
    (((SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP x).restrict A).map
        (measurableTimeChangedContinuousPath a theta ha hapos default)).map
        (ContinuousPath.shift t) =
      (Kernel.comap
          ((SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP).map
            (measurableTimeChangedContinuousPath a theta ha hapos default))
          (fun eta : ContinuousPath (State d) ↦ eta t)
          (ContinuousPath.measurable_coordinateProcess t)) ∘ₘ
        (((SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP x).restrict A).map
          (measurableTimeChangedContinuousPath a theta ha hapos default)) := by
  set Q := SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP with hQdef
  set Psi := measurableTimeChangedContinuousPath a theta ha hapos default with hPsidef
  have hPsiMeas : Measurable Psi :=
    measurable_measurableTimeChangedContinuousPath ha hapos default
  set tau := timeChangeRationalInverse a theta t with htaudef
  have htau : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := State d)) tau :=
    isStoppingTime_timeChangeRationalInverse ha hapos default t
  have huntop : ∀ z : ℝ≥0∞, z.untopD 0 = z.toNNReal := fun _ ↦ rfl
  have hshiftMeas : Measurable (ContinuousPath.shift (alpha := State d) t) :=
    (ContinuousPath.continuous_shift.comp
      (continuous_const.prodMk continuous_id)).measurable
  have hshiftTauMeas : Measurable (fun omega : ContinuousPath (State d) ↦
      ContinuousPath.shift ((tau omega).untopD 0) omega) :=
    ContinuousPath.measurable_shift_untopD_stoppingTime tau htau
  have hevalTauMeas : Measurable (fun omega : ContinuousPath (State d) ↦
      omega ((tau omega).untopD 0)) :=
    ContinuousPath.measurable_eval_untopD_stoppingTime tau htau
  -- the inverse clock is finite on the divergence event
  have hfin : ∀ omega ∈ timeChangeUnboundedEvent a theta, tau omega < ⊤ := by
    intro omega homega
    rw [htaudef, timeChangeRationalInverse_eq_orderIso_symm ha hapos omega
      ((mem_timeChangeUnboundedEvent_iff ha hapos omega).mp homega) t]
    exact ENNReal.coe_lt_top
  -- the strong Markov property at the inverse clock
  have hstrong0 := hFeller.continuousProcess_restrict_map_shift_stoppingTime_lt_top
    P hP hK x tau htau A hA
  have hrestrict : (Q x).restrict (A ∩ {omega | tau omega < ⊤}) = (Q x).restrict A := by
    refine Measure.restrict_congr_set ?_
    filter_upwards [hunb] with omega homega
    simp only [eq_iff_iff]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hfin omega homega⟩⟩
  have hstrong :
      ((Q x).restrict (A ∩ {omega | tau omega < ∞})).map
        (fun omega => ContinuousPath.shift ((tau omega).untopD 0) omega) =
      (Q.comap (fun omega => omega ((tau omega).untopD 0)) hevalTauMeas) ∘ₘ
        (Q x).restrict (A ∩ {omega | tau omega < ∞}) := by
    simpa only [hQdef] using! hstrong0
  rw [hrestrict] at hstrong
  set mu := (Q x).restrict A with hmudef
  have hunbmu : ∀ᵐ omega ∂mu, omega ∈ timeChangeUnboundedEvent a theta :=
    ae_restrict_of_ae hunb
  -- the two pathwise identities on the divergence event
  have hcoord : ∀ omega ∈ timeChangeUnboundedEvent a theta,
      Psi omega t = omega ((tau omega).untopD 0) := by
    intro omega homega
    have hunbomega := (mem_timeChangeUnboundedEvent_iff ha hapos omega).mp homega
    have hNN : (timeChangeRationalInverse a theta t omega).toNNReal =
        timeChangeRationalInverseNNReal a theta t omega := rfl
    rw [hPsidef, measurableTimeChangedContinuousPath_eq_timeChangedPath ha hapos
      default homega, htaudef, huntop, hNN,
      timeChangeRationalInverseNNReal_eq_orderIso_symm ha hapos omega hunbomega t]
    rfl
  have hintertwine : ∀ omega ∈ timeChangeUnboundedEvent a theta,
      Psi (ContinuousPath.shift ((tau omega).untopD 0) omega) =
        ContinuousPath.shift t (Psi omega) := by
    intro omega homega
    have hunbomega := (mem_timeChangeUnboundedEvent_iff ha hapos omega).mp homega
    have hS : (tau omega).untopD 0 =
        (nonnegativeClockOrderIso (timeChangePathClock a theta omega)
          (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
          (timeChangePathClock_core_clauses ha hapos 0 omega).1
          (timeChangePathClock_regular ha hapos omega).2
          (timeChangePathClock_regular ha hapos omega).1 hunbomega).symm t := by
      have hNN : (timeChangeRationalInverse a theta t omega).toNNReal =
          timeChangeRationalInverseNNReal a theta t omega := rfl
      rw [htaudef, huntop, hNN,
        timeChangeRationalInverseNNReal_eq_orderIso_symm ha hapos omega hunbomega t]
    rw [hS]
    have hshifted : ContinuousPath.shift
        ((nonnegativeClockOrderIso (timeChangePathClock a theta omega)
          (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
          (timeChangePathClock_core_clauses ha hapos 0 omega).1
          (timeChangePathClock_regular ha hapos omega).2
          (timeChangePathClock_regular ha hapos omega).1 hunbomega).symm t) omega ∈
        timeChangeUnboundedEvent a theta :=
      (mem_timeChangeUnboundedEvent_iff ha hapos _).mpr
        (timeChangePathClock_shift_unbounded ha hapos omega _ hunbomega)
    rw [hPsidef, measurableTimeChangedContinuousPath_eq_timeChangedPath ha hapos
      default hshifted, measurableTimeChangedContinuousPath_eq_timeChangedPath
      ha hapos default homega,
      shift_timeChangedPath ha hapos omega hunbomega t]
  -- the chain of measure identities
  calc
    (mu.map Psi).map (ContinuousPath.shift t)
        = mu.map (fun omega ↦ ContinuousPath.shift t (Psi omega)) := by
      rw [Measure.map_map hshiftMeas hPsiMeas]
      rfl
    _ = mu.map (fun omega ↦
          Psi (ContinuousPath.shift ((tau omega).untopD 0) omega)) := by
      refine Measure.map_congr ?_
      filter_upwards [hunbmu] with omega homega
      exact (hintertwine omega homega).symm
    _ = (mu.map (fun omega ↦
          ContinuousPath.shift ((tau omega).untopD 0) omega)).map Psi := by
      rw [Measure.map_map hPsiMeas hshiftTauMeas]
      rfl
    _ = ((Kernel.comap Q (fun omega ↦ omega ((tau omega).untopD 0))
          hevalTauMeas) ∘ₘ mu).map Psi := by rw [hstrong]
    _ = ((Kernel.comap Q (fun omega ↦ omega ((tau omega).untopD 0))
          hevalTauMeas).map Psi) ∘ₘ mu := Measure.map_comp _ _ hPsiMeas
    _ = (Kernel.comap (Q.map Psi) (fun omega ↦ omega ((tau omega).untopD 0))
          hevalTauMeas) ∘ₘ mu := by
      rw [map_comap_eq_comap_map Q hevalTauMeas hPsiMeas]
    _ = (Q.map Psi) ∘ₘ (mu.map
          (fun omega ↦ omega ((tau omega).untopD 0))) :=
      comap_comp_eq_comp_map _ hevalTauMeas _
    _ = (Q.map Psi) ∘ₘ (mu.map (fun omega ↦ Psi omega t)) := by
      have hmapeq : mu.map (fun omega ↦ omega ((tau omega).untopD 0)) =
          mu.map (fun omega ↦ Psi omega t) := by
        refine Measure.map_congr ?_
        filter_upwards [hunbmu] with omega homega
        exact (hcoord omega homega).symm
      rw [hmapeq]
    _ = (Q.map Psi) ∘ₘ ((mu.map Psi).map
          (fun eta : ContinuousPath (State d) ↦ eta t)) := by
      have hmapeq : (mu.map Psi).map (fun eta : ContinuousPath (State d) ↦ eta t) =
          mu.map (fun omega ↦ Psi omega t) := by
        have hev : Measurable (fun eta : ContinuousPath (State d) ↦ eta t) :=
          ContinuousPath.measurable_coordinateProcess t
        rw [Measure.map_map hev hPsiMeas]
        rfl
      rw [hmapeq]
    _ = (Kernel.comap (Q.map Psi) (fun eta : ContinuousPath (State d) ↦ eta t)
          (ContinuousPath.measurable_coordinateProcess t)) ∘ₘ (mu.map Psi) :=
      (comap_comp_eq_comp_map _ (ContinuousPath.measurable_coordinateProcess t) _).symm

/-- **The time-changed process is a Markov process.**  The unrestricted form
of the previous theorem: the law of the time-changed process shifted by `t` is
the mixture of the time-changed laws over the law of the time-changed process
at time `t`. -/
theorem timeChanged_map_shift
    (P : SubMarkovKernelSemigroup (State d)) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (x : State d) (t : NNReal)
    (hunb : ∀ᵐ omega ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP x),
      omega ∈ timeChangeUnboundedEvent a theta) :
    ((SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP x).map
        (measurableTimeChangedContinuousPath a theta ha hapos default)).map
        (ContinuousPath.shift t) =
      (Kernel.comap
          ((SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP).map
            (measurableTimeChangedContinuousPath a theta ha hapos default))
          (fun eta : ContinuousPath (State d) ↦ eta t)
          (ContinuousPath.measurable_coordinateProcess t)) ∘ₘ
        ((SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP x).map
          (measurableTimeChangedContinuousPath a theta ha hapos default)) := by
  have h := timeChanged_restrict_map_shift P hP hFeller hK ha hapos default x t hunb
    Set.univ MeasurableSet.univ
  rwa [Measure.restrict_univ] at h

/-- **The Markov property of the time-changed canonical process of a generated
diffusion family.**  The Feller and Kolmogorov inputs of the previous theorem
are supplied by the frozen record's own fields. -/
theorem timeChanged_map_shift_generatedDiffusionFamily [MeasurableSpace Theta]
    {coefficient weight : Theta → State d → ℝ}
    {datum : Theta →
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}
    (D : GeneratedDiffusionFamily Theta d coefficient weight datum)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (x : State d) (t : NNReal)
    (hunb : ∀ᵐ omega ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess
        (D.semigroup.toSubMarkovKernelSemigroup theta) (D.conservative theta) x),
      omega ∈ timeChangeUnboundedEvent a theta) :
    ((SubMarkovKernelSemigroup.IsConservative.continuousProcess
        (D.semigroup.toSubMarkovKernelSemigroup theta) (D.conservative theta) x).map
        (measurableTimeChangedContinuousPath a theta ha hapos default)).map
        (ContinuousPath.shift t) =
      (Kernel.comap
          ((SubMarkovKernelSemigroup.IsConservative.continuousProcess
              (D.semigroup.toSubMarkovKernelSemigroup theta)
              (D.conservative theta)).map
            (measurableTimeChangedContinuousPath a theta ha hapos default))
          (fun eta : ContinuousPath (State d) ↦ eta t)
          (ContinuousPath.measurable_coordinateProcess t)) ∘ₘ
        ((SubMarkovKernelSemigroup.IsConservative.continuousProcess
          (D.semigroup.toSubMarkovKernelSemigroup theta) (D.conservative theta) x).map
          (measurableTimeChangedContinuousPath a theta ha hapos default)) := by
  have hFeller : (D.semigroup.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup := by
    rw [D.semigroup_eq theta]
    exact (datum theta).isFellerKernelSemigroup_fellerKernelSemigroup (D.denseRange theta)
  obtain ⟨p, q, M, hmom⟩ := D.displacementMoments
  have hK := ParameterizedSubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments
    D.semigroup D.conservative hmom theta
  exact timeChanged_map_shift _ (D.conservative theta) hFeller hK ha hapos default x t hunb

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
