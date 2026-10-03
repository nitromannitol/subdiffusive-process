module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeDynkinResolvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeWeakGenerator

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.Frozen.Section7
open scoped ENNReal NNReal ZeroAtInfty Topology

noncomputable section



theorem isIntrinsicTimeChange_of_clockDivergence_of_c0Residual
    {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}
    (a : Theta → State d → ℝ)
    (ha_pos : ∀ theta x, 0 < a theta x) (ha_cont : ∀ theta, Continuous (a theta))
    {DXDatum DYDatum : Theta →
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}
    (DX : GeneratedDiffusionFamily Theta d a a DXDatum)
    (DY : GeneratedDiffusionFamily Theta d a (fun _ _ ↦ 1) DYDatum)
    (PX : CemeteryDiffusion d DX) (PY : CemeteryDiffusion d DY)
    (default : Theta → ContinuousPath (State d))
    (hresidual : ∀ (theta : Theta) (mu : MarkovProcess.Semigroup.PositiveShift)
      (f : C₀(State d, ℝ)), ∃ k : C₀(State d, ℝ), ∀ x,
        k x = (a theta x)⁻¹ * ((mu : ℝ) * (DYDatum theta).solution mu f x - f x))
    (hunbounded : ∀ theta y, ∀ᵐ omega ∂
      ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
        DX.semigroup DX.conservative (theta, y),
      omega ∈ timeChangeUnboundedEvent a theta) :
    IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel PX.law)
      (Kernel.toLifetimePathKernel PY.law) := by
  refine isIntrinsicTimeChange_of_clockDivergence_of_resolventIdentity a ha_pos ha_cont
    DX DY PX PY default hunbounded ?_
  intro theta f mu y
  obtain ⟨k, hk⟩ := hresidual theta mu f
  set P := DX.semigroup.toSubMarkovKernelSemigroup theta with hPdef
  have hPeq : P = (DXDatum theta).fellerKernelSemigroup (DX.denseRange theta) :=
    DX.semigroup_eq theta
  have hFeller : P.IsFellerKernelSemigroup := by
    rw [hPeq]
    exact (DXDatum theta).isFellerKernelSemigroup_fellerKernelSemigroup (DX.denseRange theta)
  obtain ⟨p, q, M, hmom⟩ := DX.displacementMoments
  have hK := ParameterizedSubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments
    DX.semigroup DX.conservative hmom theta
  have hmem : (DYDatum theta).solution mu f ∈ hFeller.c0Semigroup.generatorDomain :=
    mem_generatorDomain_solution_divergence_of_c0 (ha_cont theta) (ha_pos theta)
      (DX.denseRange theta) (DX.weakResolvent theta) (DY.weakResolvent theta) hFeller hPeq
      mu f k hk
  have hgen := generator_solution_divergence_of_c0 (ha_cont theta) (ha_pos theta)
    (DX.denseRange theta) (DX.weakResolvent theta) (DY.weakResolvent theta) hFeller hPeq
    mu f k hk hmem
  have hdiv : ∀ᵐ omega ∂(SubMarkovKernelSemigroup.IsConservative.continuousProcess P
      (DX.conservative theta) y), omega ∈ timeChangeUnboundedEvent a theta := by
    have h := hunbounded theta y
    rwa [ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_apply
      DX.semigroup DX.conservative theta y] at h
  have hmain := timeChanged_resolvent_identity_of_divergence (a := a) (theta := theta)
    (DX.conservative theta) hFeller hK (ha_cont theta) (ha_pos theta) (default theta)
    mu.property ((DYDatum theta).solution mu f) f hmem hgen y hdiv
  rw [← ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_apply
    DX.semigroup DX.conservative theta y] at hmain
  simpa only [neg_mul] using hmain

/-- **The frozen anchor from clock divergence and a coefficient bounded
below.**  A positive lower bound on `a` makes the reciprocal-weighted residual
a `C₀` function outright. -/
theorem isIntrinsicTimeChange_of_clockDivergence_of_lowerBound
    {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}
    (a : Theta → State d → ℝ)
    (ha_pos : ∀ theta x, 0 < a theta x) (ha_cont : ∀ theta, Continuous (a theta))
    {DXDatum DYDatum : Theta →
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}
    (DX : GeneratedDiffusionFamily Theta d a a DXDatum)
    (DY : GeneratedDiffusionFamily Theta d a (fun _ _ ↦ 1) DYDatum)
    (PX : CemeteryDiffusion d DX) (PY : CemeteryDiffusion d DY)
    (default : Theta → ContinuousPath (State d))
    (hlower : ∀ theta, ∃ eps : ℝ, 0 < eps ∧ ∀ x, eps ≤ a theta x)
    (hunbounded : ∀ theta y, ∀ᵐ omega ∂
      ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
        DX.semigroup DX.conservative (theta, y),
      omega ∈ timeChangeUnboundedEvent a theta) :
    IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel PX.law)
      (Kernel.toLifetimePathKernel PY.law) := by
  refine isIntrinsicTimeChange_of_clockDivergence_of_c0Residual a ha_pos ha_cont DX DY PX PY
    default (fun theta mu f ↦ ?_) hunbounded
  obtain ⟨eps, heps, hle⟩ := hlower theta
  exact exists_c0_residual_of_lowerBound (ha_cont theta) heps hle mu f _

/-- **The frozen anchor for a coefficient bounded above and below.**  The upper
bound discharges the clock divergence `(R1)`
(`timeChangeUnboundedEvent_eq_univ_of_bounded`), the lower bound discharges the
`C₀` obstruction of the generator identification. -/
theorem isIntrinsicTimeChange_of_boundedCoefficient
    {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}
    (a : Theta → State d → ℝ)
    (ha_pos : ∀ theta x, 0 < a theta x) (ha_cont : ∀ theta, Continuous (a theta))
    {DXDatum DYDatum : Theta →
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}
    (DX : GeneratedDiffusionFamily Theta d a a DXDatum)
    (DY : GeneratedDiffusionFamily Theta d a (fun _ _ ↦ 1) DYDatum)
    (PX : CemeteryDiffusion d DX) (PY : CemeteryDiffusion d DY)
    (default : Theta → ContinuousPath (State d))
    (hupper : ∀ theta, ∃ C : ℝ, 0 < C ∧ ∀ x, a theta x ≤ C)
    (hlower : ∀ theta, ∃ eps : ℝ, 0 < eps ∧ ∀ x, eps ≤ a theta x) :
    IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel PX.law)
      (Kernel.toLifetimePathKernel PY.law) := by
  refine isIntrinsicTimeChange_of_clockDivergence_of_lowerBound a ha_pos ha_cont DX DY PX PY
    default hlower fun theta y ↦ ?_
  obtain ⟨C, hC, hb⟩ := hupper theta
  rw [timeChangeUnboundedEvent_eq_univ_of_bounded (ha_cont theta) (ha_pos theta) hC hb]
  exact Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
