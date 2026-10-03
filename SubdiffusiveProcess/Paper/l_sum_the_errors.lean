module

public import SubdiffusiveProcess.Section6SumErrors.PaperAverage
public import SubdiffusiveProcess.Section6SumErrors.PaperConstant
public import SubdiffusiveProcess.Frozen.Section6.Defs.AccumulatedError
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper
open SubdiffusiveProcess.Section6SumErrors.Response

/-- Lemma `l.sum.the.errors`, with the manuscript expectation-form bounds. -/
theorem l_sum_the_errors
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s : ℝ, 0 < s → s ≤ 1 / 2 →
      C * M.delta ^ 2 * |Real.log M.delta| ≤ s →
      (∀ m n : ℕ, n ≤ m → ∀ z : Vec d,
        ∫⁻ ω, ENNReal.ofReal (Real.exp
          (((C * s ^ (-7 / 2 : ℝ) * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) *
                ((m : ℝ) - (n : ℝ) + 1) ^ (-1 / 2 : ℝ))⁻¹ *
              max ((∑ k ∈ Finset.Icc n m, accumulatedError M none k z s ω) /
                    ((m : ℝ) - (n : ℝ) + 1) -
                  C * s ^ (-7 / 2 : ℝ) * M.delta) 0) ^ (2 : ℕ))) ∂M.P.toMeasure ≤ 2) ∧
      (∀ lam : ℝ, 0 < lam →
        C * s ^ (-7 / 2 : ℝ) * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) ≤ lam →
        ∀ m : ℕ, ∃ Mrv : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℤ,
          Measurable Mrv ∧ (∀ ω, -1 ≤ Mrv ω ∧ Mrv ω ≤ (m : ℤ)) ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp
            ((C * s ^ (-7 : ℝ) * M.delta ^ 2 * |Real.log M.delta| * lam ^ (-2 : ℝ))⁻¹ *
              max ((m : ℝ) - (Mrv ω : ℝ) - 1) 0)) ∂M.P.toMeasure ≤ 2 ∧
          ∀ ω, ∀ n : ℕ, (n : ℤ) ≤ Mrv ω →
            ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
              ∑ j ∈ Finset.Icc n m, accumulatedError M none j z s ω ≤
                lam * ((m : ℝ) - (n : ℝ))) := by
  by_cases hdim : 2 ≤ d
  · haveI : NeZero d := ⟨by omega⟩
    obtain ⟨D, hD, hrows⟩ := exists_uniformRow_bounds (d := d)
    obtain ⟨hC, hbudgetCoeff, htwo, hbase, hsq⟩ := paperConstant_bounds d D
    refine ⟨paperConstant d D, hC, ?_⟩
    intro M s hs hsHalf hbudget
    have hs1 : s ≤ 1 := by linarith
    have hfloor := floor_le_cutoff M hs hs1 hD hbudgetCoeff hbudget
    obtain ⟨hrow, hmean⟩ := hrows s hs hs1 M hfloor
    constructor
    · intro m n hnm z
      exact average_bound s hs hs1 M hD htwo hrow hmean hnm z
    · intro lam hlam hthreshold m
      exact stopping_bound s hs hs1 M hD hbase hsq hrow hmean lam hlam hthreshold m
  · refine ⟨1, by norm_num, ?_⟩
    intro M
    exact (hdim M.shellPrefix.dimension).elim

end Paper
