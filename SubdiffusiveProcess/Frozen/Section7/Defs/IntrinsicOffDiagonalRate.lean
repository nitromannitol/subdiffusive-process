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


def SubdiffusiveProcess.Frozen.Section7.intrinsicOffDiagonalRate (F : NNReal → NNReal)
    (_hF : ∀ s : NNReal, 0 < s → 0 < F s) (R t : NNReal) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal ''
    ((fun s : NNReal => max ((R : ℝ) / s - (t : ℝ) / F s) 0) '' Set.Ioc 0 R))


