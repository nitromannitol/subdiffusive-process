import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

namespace Paper



def product_threshold_good_scale
    (d : ℕ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (B : ℝ)
    (cutoff : Option ℕ) (m : ℕ) (y : Vec d) (epsilon s : ℝ) :
    Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
  {omega | 0 < B ∧ 0 < s ∧ s ≤ 1 ∧ 0 < epsilon ∧ epsilon ≤ 1 ∧
    GoodFieldOne m y epsilon s omega ∧
    (∀ j : ℕ,
      (∀ x ∈ translatedCube d (m + 1 + j) y,
        Multipliable (fun i : ℕ =>
          if m + j ≤ i then Real.exp (4 * |omega i x - omega i y|) else 1)) ∧
      BddAbove ((fun x : Vec d =>
        |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |omega i x - omega i y|) else 1|) ''
        translatedCube d (m + 1 + j) y) ∧
      supNormOn (translatedCube d (m + 1 + j) y) (fun x ↦
        (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |omega i x - omega i y|) else 1) ≤
        B * (3 : ℝ) ^ ((s * (j : ℝ)) / 8)) ∧
    GoodResponse M cutoff m y epsilon s omega}

end Paper
