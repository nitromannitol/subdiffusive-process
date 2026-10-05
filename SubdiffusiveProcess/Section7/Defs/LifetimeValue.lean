module

public import MarkovProcess.Main
public import MarkovProcess.Lifetime.Law
public import MarkovProcess.Parameterized.Semigroup
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.State
@[expose] public section

/-!
# Evaluating a path with a cemetery state

`lifetimeValue x t path` returns the alive coordinate when one exists and
returns the starting point `x` at the cemetery state. The latter is a total
extension, not a statement that the killed process returns to its origin.
The intrinsic-clock integral is specified only for times before the lifetime,
where the alive-coordinate characterization applies.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ZeroAtInfty
noncomputable section
open _root_.SubdiffusiveProcess.Section7


def SubdiffusiveProcess.Section7.lifetimeValue {d : ℕ} (x : State d) (t : NNReal)
    (path : MarkovProcess.LifetimePath (State d)) : State d :=
  match MarkovProcess.LifetimePath.coordinate t path with
  | .alive y => y
  | .delta => x


