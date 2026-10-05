module

public import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationErrorDefault

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization.Book
open scoped ENNReal

noncomputable section


-- Adapted from Algsuperdiff/Section3/Cutoff/CoefficientFamily.lean
/-- The cutoff packaged cube by cube from one global scalar representative. -/
noncomputable def aCutoffTriadicData {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    ScalarTriadicCoeffData (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) where
  onCube Q := aCutoffCoeffOnData M L ω (Ch02.cubeDomain Q)

/-- The paper coefficient `a_L`, as a public triadic family. -/
noncomputable def aCutoffFamily {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Ch02.TriadicCoeffFamily d :=
  (aCutoffTriadicData M L ω).toTriadicCoeffFamily

/-- The random finite-volume coarse matrix. -/
noncomputable def randomAMatrix {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (U : Ch02.Domain d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Mat d :=
  aMatrix U (aCutoffCoeffOnData M m ω U).toCoeffOn

end

end SubdiffusiveProcess.CoarseGrainingVocab
