module

public import SubdiffusiveProcess.Frozen.Section6.CutoffRegularityResponse

@[expose] public section

set_option autoImplicit false
open Homogenization Homogenization.Book MeasureTheory
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

namespace SubdiffusiveProcess.Paper

theorem l_cutoff_regularity_response {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ M : GMCModel d, ∀ p : ℝ,
      1 ≤ p → p ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
      ∀ L n : ℕ,
        paperENNRealLpNorm M.P.toMeasure p
          (normalizedDefect M (min n L) (Ch02.cubeDomain (originCube d (n : ℤ)))) ≤
        ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2) :=
  SubdiffusiveProcess.Frozen.Section6.cutoff_regularity_response

end SubdiffusiveProcess.Paper
