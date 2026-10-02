import MarkovProcess.Main
import MarkovProcess.Lifetime.Law
import MarkovProcess.Parameterized.ContinuousProcess
import MarkovProcess.Parameterized.Semigroup
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.State
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ZeroAtInfty
noncomputable section
open SubdiffusiveProcess.Frozen.Section7


structure SubdiffusiveProcess.Frozen.Section7.GeneratedDiffusionFamily (Theta : Type*) [MeasurableSpace Theta] (d : ℕ)
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

