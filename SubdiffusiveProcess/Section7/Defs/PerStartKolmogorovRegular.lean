module

public import MarkovProcess.Main
public import MarkovProcess.Lifetime.Law
public import MarkovProcess.Parameterized.Semigroup
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.State
public import SubdiffusiveProcess.Section7.Defs.LifetimeValue
@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ZeroAtInfty
noncomputable section
open _root_.SubdiffusiveProcess.Section7


def SubdiffusiveProcess.Section7.PerStartKolmogorovRegular {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}
    (K : Kernel (Theta × State d) (MarkovProcess.LifetimePath (State d))) : Prop :=
  ∀ theta x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
    IsKolmogorovProcess (fun t path => lifetimeValue x t path) (K (theta, x)) p q M ∧
      0 < gamma ∧ gamma < (q - 1) / p


