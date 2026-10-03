module

public import SubdiffusiveProcess.Frozen.Section7.Defs.CemeteryDiffusion
public import SubdiffusiveProcess.Frozen.Section7.Defs.IsIntrinsicTimeChange
public import MarkovProcess.Parameterized.ContinuousProcessProperties

@[expose] public section

/-!
# Reduction of the intrinsic time change to the canonical process laws

The v2 `CemeteryDiffusion` record is determined by its finite-dimensional
laws.  Consequently, the v3 time-change anchor reduces to the single
additive-functional assertion for the canonical continuous processes of the
two generated semigroups.  This file proves that reduction without importing
the frozen theorem file.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess
open SubdiffusiveProcess.Frozen.Section7

noncomputable section

variable {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}
  {coefficient weight : Theta → State d → ℝ}
  {datum : Theta →
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}

/-- A v2 cemetery-diffusion law is the canonical conservative continuous
process of its generated semigroup.  This is the finite-dimensional-law
uniqueness step needed after an additive-functional construction. -/
theorem cemeteryDiffusion_law_eq_continuousProcess
    {D : GeneratedDiffusionFamily Theta d coefficient weight datum}
    (P : CemeteryDiffusion d D) :
    P.law = ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
      D.semigroup D.conservative := by
  let Q := ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
    D.semigroup D.conservative
  letI : IsMarkovKernel P.law := P.isMarkov
  apply Kernel.eq_of_map_denseFiniteEvaluation_eq P.law Q
  intro I
  apply Kernel.ext
  rintro ⟨theta, x⟩
  rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _),
    Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _)]
  rw [P.finiteDimensionalLaw theta x _]
  symm
  have hFeller : ∀ theta,
      (D.semigroup.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup := by
    intro theta
    rw [D.semigroup_eq theta]
    exact (datum theta).isFellerKernelSemigroup_fellerKernelSemigroup
      (D.denseRange theta)
  obtain ⟨p, q, M, hmom⟩ := D.displacementMoments
  have hK : D.semigroup.KolmogorovRegular D.conservative :=
    ParameterizedSubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments
      D.semigroup D.conservative hmom
  exact ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_map_finiteEvaluation
    D.semigroup D.conservative hFeller hK theta x _

/-- Once the canonical `(a,a)` process has been pushed forward to the
canonical `(a,1)` process by the reciprocal additive clock, finite-dimensional
law uniqueness transports the result to every pair of v2
`CemeteryDiffusion` records.  Thus the hypothesis below is exactly the sole
probabilistic producer still needed for the v3 frozen anchor. -/
theorem isIntrinsicTimeChange_of_continuousProcesses
    (a : Theta → State d → ℝ)
    (_ha_pos : ∀ theta x, 0 < a theta x)
    (_ha_cont : ∀ theta, Continuous (a theta))
    {DXDatum DYDatum : Theta →
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}
    (DX : GeneratedDiffusionFamily Theta d a a DXDatum)
    (DY : GeneratedDiffusionFamily Theta d a (fun _ _ ↦ 1) DYDatum)
    (PX : CemeteryDiffusion d DX) (PY : CemeteryDiffusion d DY)
    (hcanonical : IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel
        (ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
          DX.semigroup DX.conservative))
      (Kernel.toLifetimePathKernel
        (ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
          DY.semigroup DY.conservative))) :
    IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel PX.law)
      (Kernel.toLifetimePathKernel PY.law) := by
  rw [cemeteryDiffusion_law_eq_continuousProcess PX,
    cemeteryDiffusion_law_eq_continuousProcess PY]
  exact hcanonical

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
