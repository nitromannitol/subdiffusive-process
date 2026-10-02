import MarkovProcess.Main
import MarkovProcess.Lifetime.Law
import MarkovProcess.Parameterized.Semigroup
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.State
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ZeroAtInfty
noncomputable section
open SubdiffusiveProcess.Frozen.Section7


def SubdiffusiveProcess.Frozen.Section7.lifetimeValue {d : ℕ} (x : State d) (t : NNReal)
    (path : MarkovProcess.LifetimePath (State d)) : State d :=
  match MarkovProcess.LifetimePath.coordinate t path with
  | .alive y => y
  | .delta => x


