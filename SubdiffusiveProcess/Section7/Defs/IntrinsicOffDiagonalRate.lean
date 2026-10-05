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
open _root_.SubdiffusiveProcess.Section7


def SubdiffusiveProcess.Section7.intrinsicOffDiagonalRate (F : NNReal → NNReal)
    (_hF : ∀ s : NNReal, 0 < s → 0 < F s) (R t : NNReal) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal ''
    ((fun s : NNReal => max ((R : ℝ) / s - (t : ℝ) / F s) 0) '' Set.Ioc 0 R))


