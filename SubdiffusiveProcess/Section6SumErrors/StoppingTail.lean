module

public import SubdiffusiveProcess.Section6SumErrors.Analytic
public import SubdiffusiveProcess.Section6SumErrors.GeometricTail
@[expose] public section

/-!
# StoppingTail

Spatial and starting-scale unions give the precise exponential tail of the first-failure depth.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped ENNReal BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem stoppingDepth_tail {d : ℕ} [NeZero d]
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {C lam u : ℝ} (hC : 0 < C) (hu : 1 ≤ u)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (holderResponseRow s M j)
      (Real.exp 1 * holderResponseGammaScale s M C))
    (hmean : ∀ j : ℕ, ∫ ω, holderResponseRow s M j ω ∂M.P.toMeasure ≤
      rowMeanCoeff s d C * M.delta)
    (hlam : spatialCoeff s d C * M.delta * Real.sqrt |Real.log M.delta| * u ≤ lam)
    (q m : ℕ) (hq : 1 ≤ q) :
    M.P.toMeasure.real {ω | q < errorStoppingDepth M lam s m ω} ≤
      2 * Real.exp (-(u ^ 2 * (q : ℝ))) := by
  by_cases hqm : q ≤ m
  · have hsubset := errorStoppingDepth_tail_subset_iUnion M lam s q m (by omega)
    calc
      _ ≤ M.P.toMeasure.real (⋃ n ∈ Finset.range (m - q + 1),
        accumulatedErrorSpatialFailure M lam s n m) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
      _ ≤ ∑ n ∈ Finset.range (m - q + 1),
          M.P.toMeasure.real (accumulatedErrorSpatialFailure M lam s n m) :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ n ∈ Finset.range (m - q + 1),
          Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ)))) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnlt : n < m := by have := Finset.mem_range.mp hn; omega
        exact measureReal_accumulatedErrorSpatialFailure_le_exp s hs hs1 M hC hu hnlt hrow hmean hlam
      _ ≤ _ := sum_reverse_exp_le hu q m hqm
  · have hevent : {ω | q < errorStoppingDepth M lam s m ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_lt_of_ge ((errorStoppingDepth_le M lam s m ω).trans (by omega))
    rw [hevent]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    positivity

end
end SubdiffusiveProcess.Section6SumErrors.Response
