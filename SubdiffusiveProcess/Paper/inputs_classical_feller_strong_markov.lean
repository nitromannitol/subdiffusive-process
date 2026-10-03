module

public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput
public import MarkovProcess.Main
public import SubdiffusiveProcess.Processes.FellerRealizationInfinite
public import SubdiffusiveProcess.Processes.FellerLifetimeRestart

@[expose] public section

/-! Restart of a supplied continuous-path conservative Feller realization.
The proof uses finite-dimensional semigroup factorization, dyadic stopping-time
approximation and transport through the infinite-lifetime path embedding. -/
open MeasureTheory ProbabilityTheory MarkovProcess
open SubdiffusiveProcess.Probability.Diffusion.Input
noncomputable section
namespace Paper

/-- A conservative Feller semigroup with a continuous-path realization: the path law restarts at
every stopping time of the canonical filtration. -/
theorem inputs_classical_feller_strong_markov
    (d : ℕ) (P : SubMarkovKernelSemigroup (Fin d → ℝ)) (hP : P.IsConservative)
    (hF : P.IsFellerKernelSemigroup)
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) (hK : IsMarkovKernel K)
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) :
    Restart (K.map LifetimePath.ofContinuousPath) := by
  letI : IsMarkovKernel K := hK
  have hfdd' : ∀ I : Finset NNReal,
      K.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel P I := by
    intro I
    ext x B hB
    exact congrArg (fun μ : Measure (I → (Fin d → ℝ)) ↦ μ B) (hfdd I x)
  have hzero : ∀ x, ∀ᵐ path ∂K x, path (0 : NNReal) = x := by
    intro x
    let evalZero : ContinuousPath (Fin d → ℝ) → (Fin d → ℝ) := fun path ↦ path 0
    have hEvalZero : Measurable evalZero := ContinuousPath.measurable_coordinateProcess 0
    have hmap : Measure.map evalZero (K x) = Measure.dirac x := by
      have h := congrArg (fun Q : Kernel (Fin d → ℝ) (Fin d → ℝ) ↦ Q x)
        (SubMarkovKernelSemigroup.IsConservative.realization_map_eval_zero P hP K hfdd')
      change (K.map evalZero) x = Kernel.id x at h
      rw [Kernel.id_apply, Kernel.map_apply K hEvalZero x] at h
      exact h
    apply (mem_ae_iff_prob_eq_one (hEvalZero (MeasurableSet.singleton x))).mpr
    rw [← Measure.map_apply hEvalZero (MeasurableSet.singleton x), hmap]
    simp only [Measure.dirac_apply' x (MeasurableSet.singleton x),
      Set.indicator_of_mem (show x ∈ ({x} : Set (Fin d → ℝ)) from rfl)]
    rfl
  exact SubdiffusiveProcess.FellerRealization.restart_map_ofContinuousPath d K hzero
    (hF.realization_restrict_map_shift_stoppingTime_lt_top P hP
      (ContinuousMap.const NNReal (0 : Fin d → ℝ)) K hfdd')

end Paper
