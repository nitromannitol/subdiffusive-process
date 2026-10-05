module

public import SubdiffusiveProcess.Frozen.Vocab.NormalizedDefect

@[expose] public section

open scoped ENNReal

/-- The finite induction hypothesis `ℰ(m₀,ξ,δ₁)`. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.inductionHypothesis {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m0 : ℕ) (ξ δ1 : ℝ) : Prop :=
  1 ≤ ξ ∧ 0 < δ1 ∧ δ1 < 1 ∧
    (⨆ m : Fin (m0 + 1), SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm
      M.P.toMeasure ξ
      (SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect M m
        (Homogenization.Book.Ch02.cubeDomain
          (Homogenization.originCube d (m : ℤ))))) ≤ ENNReal.ofReal δ1

