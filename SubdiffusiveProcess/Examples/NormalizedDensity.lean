module

public import SubdiffusiveProcess.Examples.ClockLaplace
public import SubdiffusiveProcess.Examples.ClockKilledDensity
public import SubdiffusiveProcess.Section10.TorsionExitBassActual

@[expose] public section

/-! # Densities for the supplied normalized, constant-ratio diffusion -/

open MeasureTheory ProbabilityTheory MarkovProcess MarkovProcess.Semigroup Set
open MarkovProcess.SubMarkovKernelSemigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ZeroAtInfty NNReal

namespace SubdiffusiveProcess.Examples
noncomputable section

/-- Consume the proved reversible density supplier through an explicitly identified clock.
The output concerns the original kernel at every starting point and every bounded open set. -/
theorem normalized_continuousKilledDensities {d : ℕ} (hd : 2 ≤ d)
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess)
    (rho : (Fin d → ℝ) → ℝ) (hrpos : ∀ x, 0 < rho x)
    (hr : SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 rho)
    (k : ℝ) (hk : 0 < k)
    (P : SubMarkovKernelSemigroup (Fin d → ℝ)) (hP : P.IsConservative)
    (D : C0ResolventDatum (Fin d → ℝ)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hweak : IsWeakEllipticResolvent (fun x => k * rho x) rho D)
    (hlaplace : ∀ (mu : PositiveShift) (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ),
      D.solution mu f x = ∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) f x)
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (hfdd : ∀ I, K.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) :
    SubdiffusiveProcess.Probability.Diffusion.Input.ContinuousKilledDensities rho
      (K.map LifetimePath.ofContinuousPath) := by
  let c := inverseClock k hk
  have hc : 0 < c := inverseClock_pos k hk
  let D' := clockResolvent D k hk
  let dense' := clockResolvent_denseRange D hdense k hk
  let P' := clockSemigroup P c
  let K' := clockKernel K c
  letI : IsMarkovKernel K' := Kernel.IsMarkovKernel.map _ (ContinuousPath.measurable_rescale _ _)
  have hPfdd := clockKernel_fdd P hP K hfdd c hc
  have hPcons : P'.IsConservative := fun t => hP (c * t)
  have heq : P' = D'.fellerKernelSemigroup dense' :=
    (SubdiffusiveProcess.E7.isFeller_of_realization_and_datum P' D' dense'
      (clockResolvent_laplace P D hlaplace k hk) K'
      (fun I x => congrArg (fun J : Kernel (Fin d → ℝ) (I → (Fin d → ℝ)) => J x)
        (hPfdd I))).1
  have hD' := SubdiffusiveProcess.Section10.smoothReversibleKilledDensitySupplier hFOT
    d hd rho hrpos hr D' dense' (clockResolvent_weak rho D k hk hweak)
    (heq ▸ hPcons) K' (by infer_instance)
    (fun I x => by rw [← heq]; exact congrArg (fun J => J x) (hPfdd I))
  let b : NNReal := ⟨k, hk.le⟩
  have hb : 0 < b := hk
  have hcb : c * b = 1 := by
    apply NNReal.coe_injective
    change k⁻¹ * k = 1
    exact inv_mul_cancel₀ hk.ne'
  have hback : clockKernel K' b = K := by
    rw [show K' = clockKernel K c from rfl, clockKernel_clockKernel, hcb, clockKernel_one]
  have hDensity := clockKernel_continuousKilledDensities rho K' hD' b hb
  rwa [hback] at hDensity

end
end SubdiffusiveProcess.Examples
