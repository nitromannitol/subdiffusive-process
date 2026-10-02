import MarkovProcess.Main
import MarkovProcess.Lifetime.Law
import MarkovProcess.Parameterized.Semigroup
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.State
import SubdiffusiveProcess.Frozen.Section7.Defs.LifetimeValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ZeroAtInfty
noncomputable section
open SubdiffusiveProcess.Frozen.Section7


def SubdiffusiveProcess.Frozen.Section7.PerStartKolmogorovRegular {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}
    (K : Kernel (Theta × State d) (MarkovProcess.LifetimePath (State d))) : Prop :=
  ∀ theta x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
    IsKolmogorovProcess (fun t path => lifetimeValue x t path) (K (theta, x)) p q M ∧
      0 < gamma ∧ gamma < (q - 1) / p


