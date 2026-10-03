module

public import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationErrorDefault

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization.Book
open scoped ENNReal

noncomputable section

-- REUSE-CANDIDATE: Algsuperdiff/Section3/Cutoff/CoefficientFamily.lean
-- Adapted from Algsuperdiff/Section3/Cutoff/CoefficientFamily.lean
/-- The cutoff packaged cube by cube from one global scalar representative. -/
noncomputable def aCutoffTriadicData {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    ScalarTriadicCoeffData (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) where
  onCube Q := aCutoffCoeffOnData M L ω (Ch02.cubeDomain Q)

/-- The paper coefficient `a_L`, as a public triadic family. -/
noncomputable def aCutoffFamily {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : Ch02.TriadicCoeffFamily d :=
  (aCutoffTriadicData M L ω).toTriadicCoeffFamily

/-- The random finite-volume coarse matrix. -/
noncomputable def randomAMatrix {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (U : Ch02.Domain d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : Mat d :=
  aMatrix U (aCutoffCoeffOnData M m ω U).toCoeffOn

end

end SubdiffusiveProcess.CoarseGrainingVocab
