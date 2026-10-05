module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowThreeShort

@[expose] public section

/-!
# Row 3's long branch: the arithmetic

Row 3 differs from rows 1 and 2 in one decisive way: its statement carries the
**short-window hypothesis**

```text
  (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ ,
```

so `(1 - alpha) * (m - n) ≤ 1` and the ladder exponential
`3 ^ ((1 - alpha) * (m - n) / 4)` is bounded by the absolute constant `3 ^ (1/4)`.
There is therefore **no joint absorption to perform** on this row — the
gap-uniformity work is simply not needed here, and every constant
below is absolute or dimension-only.

The contraction converts to the printed decay by `theta ≤ 3 ^ (-1/4)`, which is
what `theta ^ k ∈ Ioo 0 (3/5)` and the choice of `k` deliver.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}

/-- The contraction converts to the printed decay rate. -/
theorem theta_pow_le_three_pow {theta : ℝ} (h0 : 0 ≤ theta)
    (hle : theta ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4)) (gap : ℕ) :
    theta ^ gap ≤ (3 : ℝ) ^ (-(gap : ℝ) / 4) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hstep : theta ^ gap ≤ ((3 : ℝ) ^ (-(1 : ℝ) / 4)) ^ gap :=
    pow_le_pow_left₀ h0 hle gap
  refine hstep.trans (le_of_eq ?_)
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 : ℝ) / 4)) gap, ← Real.rpow_mul h3.le]
  congr 1
  ring

/-- **The short-window hypothesis bounds the ladder exponential outright.**
This is why row 3 needs no joint absorption. -/
theorem shortWindow_exponential_le {alpha m n : ℝ}
    (halpha1 : alpha < 1) (hwindow : m - n ≤ (1 - alpha)⁻¹) :
    (3 : ℝ) ^ ((1 - alpha) * (m - n) / 4) ≤ (3 : ℝ) ^ ((1 : ℝ) / 4) := by
  have hpos : (0 : ℝ) < 1 - alpha := by linarith
  have hle : (1 - alpha) * (m - n) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hwindow hpos.le
    rwa [mul_inv_cancel₀ (ne_of_gt hpos)] at h
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  linarith

/-- The gap appearing in row 3's long branch is `ell - n - 2`, and the printed
coefficient is stated at `ell - n`; the conversion costs the absolute factor
`3 ^ (1/2)`. -/
theorem rowThree_gap_shift {gap : ℝ} :
    (3 : ℝ) ^ (-(gap - 2) / 4) = (3 : ℝ) ^ ((1 : ℝ) / 2) * (3 : ℝ) ^ (-gap / 4) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
