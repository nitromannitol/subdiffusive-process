import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
import MarkovProcess.Lifetime.Basic
import MarkovProcess.FiniteTime.ProjectiveFamily
import MarkovProcess.Main
import SubdiffusiveProcess.Processes.E7.E7Main
import SubdiffusiveProcess.Paper.inputs_classical_feller_strong_markov
import SubdiffusiveProcess.Paper.inputs_classical_fot_part_process

open MeasureTheory ProbabilityTheory MarkovProcess Topology
open SubdiffusiveProcess.Probability.Diffusion.Input
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal

noncomputable section
namespace Paper



theorem inputs_classical_e7
    (d : ℕ) (c rho : (Fin d → ℝ) → ℝ)
    (hcpos : ∀ x, 0 < c x) (hrhopos : ∀ x, 0 < rho x)
    (hc : LocallyC11 c) (hrho : LocallyC11 rho)
    (P : SubMarkovKernelSemigroup (Fin d → ℝ))
    (hP : P.IsConservative)
    (D : C0ResolventDatum (Fin d → ℝ))
    (hdense : ∀ mu, DenseRange (D.operator mu))
    (hweak : IsWeakEllipticResolvent c rho D)
    (hlaplace : ∀ (mu : Semigroup.PositiveShift)
      (f : ZeroAtInftyContinuousMap (Fin d → ℝ) ℝ) (x : Fin d → ℝ),
      D.solution mu f x = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) f x)
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    (hK : IsMarkovKernel K)
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) :
    Restart (K.map LifetimePath.ofContinuousPath) ∧
      KilledGenerator c rho (K.map LifetimePath.ofContinuousPath) := by
  exact SubdiffusiveProcess.E7.e7_of_leaves
    (fun d P hP hF K hK hfdd => inputs_classical_feller_strong_markov d P hP hF K hK hfdd)
    (fun d m hm hpos E hE P hP hF K hK hfdd hassoc U hU =>
      inputs_classical_fot_part_process d m hm hpos E hE P hP hF K hK hfdd hassoc U hU)
    d c rho hcpos hrhopos hc hrho P hP D hdense hweak hlaplace K hK hfdd

end Paper
