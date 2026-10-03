module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GoodTailCollapse

@[expose] public section

/-!
# Arithmetic of the Γ₁ exponent

The frozen Γ₁ right-hand side is

```text
  C · exp ( -((1-α)² · max (k - C) 0) / (C · δ² · |log δ|) ) .
```

Both landed stopping tails produce an exponential of the same *shape* but with
their own rate; turning each into a half of the frozen bound is the elementary
comparison `exp_bound_le` below plus one exponent inequality.  Isolating them
here keeps the main assembly readable.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The frozen Γ₁ right-hand side. -/
def gammaOneRHS (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C alpha : ℝ)
    (k : ℕ) : ℝ :=
  C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
    (C * M.delta ^ 2 * |Real.log M.delta|))

/-- A smaller prefactor and a larger rate give a smaller exponential bound. -/
theorem exp_bound_le {a b E1 E2 : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hE : E2 ≤ E1) :
    a * Real.exp (-E1) ≤ b * Real.exp (-E2) := by
  have hexp : Real.exp (-E1) ≤ Real.exp (-E2) := Real.exp_le_exp.mpr (by linarith)
  calc a * Real.exp (-E1) ≤ a * Real.exp (-E2) :=
        mul_le_mul_of_nonneg_left hexp ha
    _ ≤ b * Real.exp (-E2) := mul_le_mul_of_nonneg_right hab (Real.exp_nonneg _)

/-- The frozen exponent, rewritten with an explicit positive denominator. -/
theorem gammaOneRHS_eq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C alpha : ℝ)
    (k : ℕ) :
    gammaOneRHS M C alpha k =
      C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 /
        (C * (M.delta ^ 2 * |Real.log M.delta|)))) := by
  unfold gammaOneRHS
  congr 2
  rw [neg_div]
  ring_nf

/-- **The exponent comparison.**  If the competing rate is `(1-α)²·W/(B·D)` with
`W` at least the frozen shift and `B` at most the frozen constant, its exponent
dominates the frozen one. -/
theorem gammaOne_exponent_le {C B D W alpha : ℝ} {k : ℕ}
    (hC : 0 < C) (hB : 0 < B) (hD : 0 < D)
    (hBC : B ≤ C) (hW : max ((k : ℝ) - C) 0 ≤ W) :
    (1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 / (C * D) ≤
      (1 - alpha) ^ 2 * W / (B * D) := by
  have hsq : 0 ≤ (1 - alpha) ^ 2 := sq_nonneg _
  have hmax0 : 0 ≤ max ((k : ℝ) - C) 0 := le_max_right _ _
  have hnum : (1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 ≤ (1 - alpha) ^ 2 * W :=
    mul_le_mul_of_nonneg_left hW hsq
  have hden : 0 < B * D := mul_pos hB hD
  have hdenC : 0 < C * D := mul_pos hC hD
  have hdenle : B * D ≤ C * D := mul_le_mul_of_nonneg_right hBC hD.le
  calc (1 - alpha) ^ 2 * max ((k : ℝ) - C) 0 / (C * D)
      ≤ (1 - alpha) ^ 2 * W / (C * D) := by
        exact (div_le_div_iff_of_pos_right hdenC).mpr hnum
    _ ≤ (1 - alpha) ^ 2 * W / (B * D) := by
        apply div_le_div_of_nonneg_left _ hden hdenle
        exact le_trans (mul_nonneg hsq hmax0) hnum

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
