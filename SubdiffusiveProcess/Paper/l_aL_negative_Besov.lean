module

public import SubdiffusiveProcess.Section3.ALNegativeBesov

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem l_aL_negative_Besov {d : ℕ} :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s p : ℝ),
        0 < s → s ≤ 1 → 2 ≤ p →
        C * p * M.delta ^ 2 ≤ s →
        p * M.delta ^ 2 * Real.log (2 + p) ≤ c →
        ∀ (m : ℕ) (n : ℤ), -1 ≤ n → n < (m : ℤ) →
          ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
              paperENNRealLpNorm M.P.toMeasure p
                (cutoffRatioNegativeBesov M m n s p) ≤
            ENNReal.ofReal (C * s⁻¹ * M.delta * Real.sqrt p * Real.log p) ∧
          ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
              paperENNRealLpNorm M.P.toMeasure p
                (inverseCutoffRatioNegativeBesov M m n s p) ≤
            ENNReal.ofReal (C * s⁻¹ * M.delta * Real.sqrt p * Real.log p) :=
  _root_.SubdiffusiveProcess.Section3.a_l_negative_besov 

end SubdiffusiveProcess.Paper
