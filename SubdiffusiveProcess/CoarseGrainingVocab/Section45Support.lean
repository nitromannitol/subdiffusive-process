module

public import SubdiffusiveProcess.Frozen.Vocab.TailCoefficient

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization.Book
open scoped ENNReal

noncomputable section

/-- Normalized cube average of `b_{L,m}`. -/
noncomputable def tailCoefficientCubeAverage {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  Ch02.average (Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))
    (tailCoefficient M L m ω)

-- REUSE-CANDIDATE: Algsuperdiff/Assumptions/ShellField/SequenceLaw.lean
/-- Pull a potential sample back from a translated cube. -/
def translatePotentialSample {d : ℕ} (z : Vec d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
  fun k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z (ω k)

/-- Arbitrary real translation of a centered paper cube. -/
abbrev PaperCubeTranslate (d : ℕ) := Vec d

/-- Supremum over cutoffs and scale-`n` descendants. -/
noncomputable def ellipticityMomentObservable {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ) (s : ℝ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ≥0∞ :=
  ⨆ L : {L : ℕ // m ≤ L},
    ⨆ R : {R : TriadicCube d //
        R ∈ Homogenization.descendantsAtScale
          (Homogenization.originCube d (m : ℤ)) n},
      paperHomogenizationErrorDefault R n s .infinity (aCutoffFamily M L ω)
        (tailCoefficientCubeAverage M L m ω)

/-- Homogenization error on an arbitrary translated centered cube. -/
noncomputable def translatedHomogenizationErrorRandom {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L K : ℕ)
    (z : PaperCubeTranslate d) (s : ℝ) (r : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ≥0∞ :=
  paperHomogenizationError (Homogenization.originCube d (K : ℤ)) (K : ℤ)
    s .infinity (.finite (r : ℝ))
    (aCutoffFamily M L (translatePotentialSample z ω)) (ahom M L)

end

end SubdiffusiveProcess.CoarseGrainingVocab
