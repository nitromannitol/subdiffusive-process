import SubdiffusiveProcess.Frozen.Section8.IsFourierRepresentative
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FrozenNamespace

open MeasureTheory
open Homogenization
open scoped BigOperators

noncomputable section
open SubdiffusiveProcess.Frozen.Section8


def SubdiffusiveProcess.Frozen.Section8.massiveNegativeSobolevNormSq {d : ℕ} (R sigma : ℝ)
    (Fhat : Vec d → Fin d → ℂ) : ℝ :=
  ∫ xi : Vec d, (vecNormSq xi + R⁻¹ ^ 2) ^ (-sigma) *
    ∑ i, ‖Fhat xi i‖ ^ 2


