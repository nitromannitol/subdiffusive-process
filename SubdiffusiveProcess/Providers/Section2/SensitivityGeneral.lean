module

public import SubdiffusiveProcess.CoarseGrainingVocab.Sensitivity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support

@[expose] public section

/-!
# Scalar coefficient sensitivity of the normalized coarse matrices

Provider for `l.sensitivity.general` v2
(paper label `l.sensitivity.general`).

The statement below is byte-identical to the block of
`SubdiffusiveProcess/Section2/SensitivityGeneral.lean` apart from the declaration name.
The proof is the proved
`SubdiffusiveProcess.CoarseGrainingVocab.normalized_aStarMatrix_and_aMatrix_deviation_le`.
-/

set_option autoImplicit false
open Homogenization Homogenization.Book MeasureTheory
noncomputable section

-- `hd` is inert in the proved proof; it is kept because the statement
-- carries the manuscript's standing `d ≥ 2` convention.
theorem SubdiffusiveProcess.Providers.Section2.sensitivity_general {d : ℕ} (_hd : 2 ≤ d)
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
