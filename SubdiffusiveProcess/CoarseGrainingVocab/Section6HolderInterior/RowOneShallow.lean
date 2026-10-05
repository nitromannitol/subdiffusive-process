module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneArithmetic

@[expose] public section

/-!
# Statement row 1: the shallow-gap branch

`interiorRowOne_arith` runs the Campanato iteration, which needs a genuine gap:
its top scale sits at `m - 5`, so it applies only when the base scale satisfies
`ell < m - 5`.

In the complementary range `m - 5 ≤ ell` the iteration is unnecessary — the
window is already comparable to the domain, and the proved top-window volume
transfer alone gives the frozen row, with the *same* dimension-only constant
`topWindowRatio d = 3^5·√((3^7)^d)` that the long-gap branch produces.

The reason both branches share that constant is not a coincidence: in each case
what is being paid is the volume ratio between a window at depth at most `5`
below the domain and the domain itself.

Like the long-gap passage this is stated on abstract reals, so the boundary argument
can reuse it verbatim.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- **Statement row 1 in the shallow-gap range** `m - 5 ≤ ell`, straight from the
top-window transfer. -/
theorem interiorRowOne_shallow {d : ℕ} {alpha ell n m oscEll global data : ℝ}
    (halpha : alpha ≤ 1)
    (hell : ell ≤ n) (hnm : n ≤ m) (hshallow : m - ell ≤ 5)
    (hglobal : 0 ≤ global) (hdata : 0 ≤ data)
    (htop : oscEll ≤ Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global) :
    (3 : ℝ) ^ (alpha * (n - ell)) * oscEll ≤
      topWindowRatio d * (3 : ℝ) ^ (-alpha * (m - n)) *
        (global + (3 : ℝ) ^ (3 * m / 2) * data) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hmell : 0 ≤ m - ell := by linarith
  have hsqrt0 : 0 ≤ Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) := Real.sqrt_nonneg _
  -- the scale factor is at most the shallow-depth constant
  have hscale : (3 : ℝ) ^ (alpha * (n - ell)) ≤
      (3 : ℝ) ^ (5 : ℕ) * (3 : ℝ) ^ (-alpha * (m - n)) := by
    have hsum : (3 : ℝ) ^ (5 : ℕ) * (3 : ℝ) ^ (-alpha * (m - n))
        = (3 : ℝ) ^ ((5 : ℝ) + -alpha * (m - n)) := by
      rw [← Real.rpow_natCast (3 : ℝ) 5, ← Real.rpow_add h3pos]
      norm_num
    rw [hsum]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hkey : alpha * (m - ell) ≤ 5 := by
      calc alpha * (m - ell) ≤ 1 * (m - ell) :=
            mul_le_mul_of_nonneg_right halpha hmell
        _ = m - ell := by ring
        _ ≤ 5 := hshallow
    nlinarith [hkey]
  -- assemble
  have hpow0 : (0 : ℝ) ≤ (3 : ℝ) ^ (alpha * (n - ell)) :=
    Real.rpow_nonneg h3pos.le _
  have hdataTerm : 0 ≤ (3 : ℝ) ^ (3 * m / 2) * data := by positivity
  have hfactor0 : (0 : ℝ) ≤ (3 : ℝ) ^ (5 : ℕ) * (3 : ℝ) ^ (-alpha * (m - n)) := by
    positivity
  calc (3 : ℝ) ^ (alpha * (n - ell)) * oscEll
      ≤ (3 : ℝ) ^ (alpha * (n - ell)) *
          (Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global) :=
        mul_le_mul_of_nonneg_left htop hpow0
    _ ≤ ((3 : ℝ) ^ (5 : ℕ) * (3 : ℝ) ^ (-alpha * (m - n))) *
          (Real.sqrt (((3 : ℝ) ^ (7 : ℕ)) ^ d) * global) := by
        apply mul_le_mul_of_nonneg_right hscale
        exact mul_nonneg hsqrt0 hglobal
    _ = topWindowRatio d * (3 : ℝ) ^ (-alpha * (m - n)) * global := by
        unfold topWindowRatio; ring
    _ ≤ topWindowRatio d * (3 : ℝ) ^ (-alpha * (m - n)) *
          (global + (3 : ℝ) ^ (3 * m / 2) * data) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        exact mul_nonneg (topWindowRatio_nonneg d) (Real.rpow_nonneg h3pos.le _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
