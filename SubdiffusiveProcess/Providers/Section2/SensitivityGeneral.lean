import SubdiffusiveProcess.CoarseGrainingVocab.Sensitivity
import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support




set_option autoImplicit false
open Homogenization Homogenization.Book MeasureTheory
noncomputable section


-- carries the manuscript's standing `d ≥ 2` convention.
set_option linter.unusedVariables false in

theorem SubdiffusiveProcess.Providers.Section2.sensitivity_general {d : ℕ} (hd : 2 ≤ d)
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
      SubdiffusiveProcess.CoarseGrainingVocab.scalarSensitivityError U a b

:= SubdiffusiveProcess.CoarseGrainingVocab.normalized_aStarMatrix_and_aMatrix_deviation_le ha hb
