module

public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldEvenField

@[expose] public section

noncomputable section

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess
open scoped ENNReal

namespace Paper

theorem prefix_even_series_tsum_ne_top {d : ℕ} (M : GMCModel d)
    (s : ℝ) (hs : 0 < s) (q : ℕ) :
    (∑' j : ℕ, ENNReal.ofReal (prefix_even_series_bound M s q j)) ≠ ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (prefix_even_series_bound_nonneg M s q)
    (prefix_even_series_bound_summable M s hs q)]
  exact ENNReal.ofReal_ne_top


end Paper
