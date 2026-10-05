module

public import SubdiffusiveProcess.Vocab.NormalizedDefect

@[expose] public section

open scoped ENNReal

/-- The infinite induction hypothesis `ℰ(∞,ξ,δ₁)`. -/
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.inductionHypothesisInfinity {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (ξ δ1 : ℝ) : Prop :=
  1 ≤ ξ ∧ 0 < δ1 ∧ δ1 < 1 ∧
    (⨆ m : ℕ, SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm M.P.toMeasure ξ
      (SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect M m
        (Homogenization.Book.Ch02.cubeDomain
          (Homogenization.originCube d (m : ℤ))))) ≤ ENNReal.ofReal δ1
