module

public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import MarkovProcess.Lifetime.Basic
public import MarkovProcess.FiniteTime.ProjectiveFamily
public import MarkovProcess.Main
public import SubdiffusiveProcess.Processes.E7.E7Main
public import SubdiffusiveProcess.Paper.inputs_classical_feller_strong_markov
public import SubdiffusiveProcess.Paper.inputs_classical_fot_part_process

@[expose] public section

open MeasureTheory ProbabilityTheory MarkovProcess Topology
open SubdiffusiveProcess.Probability.Diffusion.Input
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Identification of a conservative diffusion attached to a weak elliptic C0 resolvent.
Its conclusions are the lifetime restart law and the raw stopped generator identity with the
zero-boundary approximation required for every L2 datum. No GMC-model package is assumed.
PROVED from two frozen classical leaves (`inputs_classical_feller_strong_markov`: Feller ⇒ strong
Markov; `inputs_classical_fot_part_process`: FOT §4.4 part of a Hunt diffusion) by the library glue
`SubdiffusiveProcess.E7.e7_of_leaves`: the semigroup is Feller (Laplace uniqueness), the resolvent
datum is the resolvent of the closure of the smooth weighted gradient form (Galerkin/Céa and a
truncation maximum principle), and the part-form resolvent is `H¹₀`-approximable with the weak
equation. The statement is unchanged. -/
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

end SubdiffusiveProcess.Paper
