module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeDynkinResolvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeWeakGenerator

@[expose] public section

/-!
# The anchor from clock divergence and a coefficient bounded below

This file assembles the two halves proved in this argument:

* `generator_solution_divergence` (`TimeChangeWeakGenerator`) — the `(a,1)`
  resolvent lies in the domain of the `(a,a)` generator, with
  `L_X g = a⁻¹ (mu g − f)`; this needs `a` bounded **below** by a positive
  constant, so that the corrected datum `mu g − a⁻¹ (mu g − f)` is again a `C₀`
  function and the two resolvent operators can be composed at all.  That is the
  exact form of the obstruction the reciprocal-clock obstruction and the time-change resolvent argument recorded;
* `timeChanged_resolvent_identity_of_divergence` (`TimeChangeDynkinResolvent`) —
  the manuscript's resolvent identity proved by optional stopping at the truncated inverse clock, which needs only
  the almost-sure clock divergence `(R1)`,

and feeds them into the time-change resolvent argument's
`isIntrinsicTimeChange_of_clockDivergence_of_resolventIdentity`.

The consequence is that the anchor 
now rests on exactly **two** hypotheses beyond the ones:

* `(R1)` almost-sure divergence of the reciprocal clock under the `(a,a)`
  process — the time-change resolvent argument's author item, not derivable from `DX` alone;
* `(L)` `a` bounded away from `0`.

For a coefficient bounded above and below both are discharged, and the
conclusion follows outright (`isIntrinsicTimeChange_of_boundedCoefficient`).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open _root_.SubdiffusiveProcess.Section7
open scoped ENNReal NNReal ZeroAtInfty Topology

noncomputable section

/-- **The anchor from clock divergence and the `C₀` residual.**  This is
the sharpest form this argument reaches: beyond the hypotheses it consumes

* `hunbounded` — almost-sure divergence of the reciprocal clock, the time-change resolvent argument's
  irreducible probabilistic input `(R1)`;
* `hresidual` — for every `theta`, `mu`, `f` the reciprocal-weighted residual
  `a⁻¹ (mu R^{(a,1)}_mu f − f)` vanishes at infinity.

The second hypothesis is exactly the assertion `R^{(a,1)}_mu f ∈ D(L_X)` that
the manuscript uses implicitly when it applies Dynkin's formula to the
`(a,1)`-resolvent along the `(a,a)` process
it is a decay statement about the
resolvent, i.e. Section 8 material, not Section 7 material. -/
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

/-- **The anchor from clock divergence and a coefficient bounded
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

/-- **The anchor for a coefficient bounded above and below.**  The upper
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
