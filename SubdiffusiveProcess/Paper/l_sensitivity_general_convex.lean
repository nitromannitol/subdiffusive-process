module

public import SubdiffusiveProcess.Frozen.Section2.SensitivityGeneral

@[expose] public section

open Homogenization Homogenization.Book MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem l_sensitivity_general_convex {d : ℕ} (hd : 2 ≤ d)
    (U : Ch02.Domain d) (a b : Vec d → ℝ)
    (ha : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (hb : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U b) :
    Ch02.matrixOperatorNorm
        (SubdiffusiveProcess.CoarseGrainingVocab.matrixInvSqrt
            (SubdiffusiveProcess.CoarseGrainingVocab.aStarMatrix U hb.toCoeffOn) *
          SubdiffusiveProcess.CoarseGrainingVocab.aStarMatrix U ha.toCoeffOn *
          SubdiffusiveProcess.CoarseGrainingVocab.matrixInvSqrt
            (SubdiffusiveProcess.CoarseGrainingVocab.aStarMatrix U hb.toCoeffOn) - (1 : Mat d)) ≤
      SubdiffusiveProcess.CoarseGrainingVocab.scalarSensitivityError U a b ∧
    Ch02.matrixOperatorNorm
        (SubdiffusiveProcess.CoarseGrainingVocab.matrixInvSqrt
            (SubdiffusiveProcess.CoarseGrainingVocab.aMatrix U hb.toCoeffOn) *
          SubdiffusiveProcess.CoarseGrainingVocab.aMatrix U ha.toCoeffOn *
          SubdiffusiveProcess.CoarseGrainingVocab.matrixInvSqrt
            (SubdiffusiveProcess.CoarseGrainingVocab.aMatrix U hb.toCoeffOn) - (1 : Mat d)) ≤
      SubdiffusiveProcess.CoarseGrainingVocab.scalarSensitivityError U a b :=
  SubdiffusiveProcess.Frozen.Section2.sensitivity_general hd U a b ha hb

end SubdiffusiveProcess.Paper
