module

public import MarkovProcess.Main
public import MarkovProcess.Lifetime.Law
public import MarkovProcess.Parameterized.ContinuousProcess
public import MarkovProcess.Parameterized.Semigroup
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.State
@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ZeroAtInfty
noncomputable section
open _root_.SubdiffusiveProcess.Section7

structure SubdiffusiveProcess.Section7.GeneratedDiffusionFamily (Theta : Type*) [MeasurableSpace Theta] (d : ℕ)
    (coefficient weight : Theta → State d → ℝ)
    (datum : Theta → SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)) where
  denseRange : ∀ theta mu, DenseRange ((datum theta).operator mu)
  weakResolvent : ∀ theta,
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
      (coefficient theta) (weight theta) (datum theta)
  semigroup : MarkovProcess.ParameterizedSubMarkovKernelSemigroup Theta (State d)
  semigroup_eq : ∀ theta,
    semigroup.toSubMarkovKernelSemigroup theta =
      (datum theta).fellerKernelSemigroup (denseRange theta)
  conservative : semigroup.IsConservative
  displacementMoments : ∃ p q : ℝ, ∃ M : ℝ≥0,
    semigroup.HasKolmogorovMoments p q M
