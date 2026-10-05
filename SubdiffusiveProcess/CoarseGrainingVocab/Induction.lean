module

public import SubdiffusiveProcess.Vocab.InductionHypothesis
public import SubdiffusiveProcess.Vocab.InductionHypothesisInfinity
public import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationErrorDefault

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization.Book
open scoped ENNReal

noncomputable section

/-- The normalized defect at cube scale `m` with cutoff scale `L`. -/
noncomputable def normalizedDefectAt {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  paperScalarProbeMax (Homogenization.originCube d (m : ℤ))
    (aCutoffFamily M L ω) (ahom M L)

/-- The paper `ℰ_{s,∞}` random variable. -/
noncomputable def homogenizationErrorRandom {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) (s : ℝ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  paperHomogenizationErrorDefault (Homogenization.originCube d (m : ℤ))
    (m : ℤ) s .infinity (aCutoffFamily M L ω) (ahom M L)

/-- Expected response on the centered scale-`m` cube. -/
noncomputable def expectedJ {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ) (p q : Vec d) : ℝ :=
  ∫ ω, J (Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))
    ((aCutoffFamily M L ω).coeffOn (Homogenization.originCube d (m : ℤ))) p q
    ∂M.P.toMeasure

/-- Literal expectation of the difference of two responses. -/
noncomputable def expectedJDifference {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ) (p q : Vec d) : ℝ :=
  ∫ ω,
    J (Ch02.cubeDomain (Homogenization.originCube d (n : ℤ)))
        ((aCutoffFamily M L ω).coeffOn (Homogenization.originCube d (n : ℤ))) p q -
      J (Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))
        ((aCutoffFamily M L ω).coeffOn (Homogenization.originCube d (m : ℤ))) p q
    ∂M.P.toMeasure

end

end SubdiffusiveProcess.CoarseGrainingVocab
