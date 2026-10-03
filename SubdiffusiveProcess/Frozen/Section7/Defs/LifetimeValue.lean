module

public import MarkovProcess.Main
public import MarkovProcess.Lifetime.Law
public import MarkovProcess.Parameterized.Semigroup
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.State
@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ZeroAtInfty
noncomputable section
open SubdiffusiveProcess.Frozen.Section7


def SubdiffusiveProcess.Frozen.Section7.lifetimeValue {d : ℕ} (x : State d) (t : NNReal)
    (path : MarkovProcess.LifetimePath (State d)) : State d :=
  match MarkovProcess.LifetimePath.coordinate t path with
  | .alive y => y
  | .delta => x


