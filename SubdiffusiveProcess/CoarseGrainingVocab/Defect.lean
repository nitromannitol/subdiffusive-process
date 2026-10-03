module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.Frozen.Vocab.Ahom

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization.Book
open scoped ENNReal

noncomputable section

/-- The sphere maximum on a public domain. -/
noncomputable def paperScalarProbeMaxOn {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (alpha : ℝ) : ℝ≥0∞ :=
  ⨆ e : {e : Vec d // Homogenization.vecNormSq e = 1},
    ENNReal.ofReal (J U a ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e))

/-- The `L^ξ` norm of a real random variable. -/
noncomputable def paperLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : ℝ) (X : Ω → ℝ) : ℝ≥0∞ :=
  SubdiffusiveProcess.RawLp.eLpNorm X (ENNReal.ofReal ξ) μ

/-- The paper's `L^ξ` moment for an `ENNReal` observable. -/
noncomputable def paperENNRealLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : ℝ) (X : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ ω, (X ω) ^ ξ ∂μ) ^ ξ⁻¹

end

end SubdiffusiveProcess.CoarseGrainingVocab
