module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.InteriorBoundaryGate

@[expose] public section

/-!
# Hölder Step 5: Campanato exponent rebasing

This file isolates the deterministic exponent calculation which changes the
full-domain estimate at base scale `ell` into the frozen local Hölder weight.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

noncomputable section

/-- The scale coefficient in the full-domain Campanato row is no larger than
the frozen `3^{-alpha (m-n)}` coefficient after restoring the scale `3^ell`.
-/
theorem holderCampanato_scale_factor_le {alpha ell n m : ℝ}
    (halpha : alpha ≤ 1) (hellm : ell ≤ m) :
    (3 : ℝ) ^ ell * (3 : ℝ) ^ (alpha * (n - ell)) *
          (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
          (3 : ℝ) ^ (-m) ≤
      (3 : ℝ) ^ (-alpha * (m - n)) := by
  have hexponent :
      ell + alpha * (n - ell) + (1 - alpha) * (m - ell) / 2 - m ≤
        -alpha * (m - n) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr halpha) (sub_nonneg.mpr hellm)]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

/-- Abstract-real composition of the two full-domain data slots.  This is the
algebraic heart of the passage from `e.Campanato.full.domain` to
`e.Holder.estimate.boxes.local`; all quantities other than scale powers are
kept opaque. -/
theorem holderCampanato_rebase {alpha ell n m C osc global data : ℝ}
    (halpha : alpha ≤ 1) (hellm : ell ≤ m)
    (hC : 0 ≤ C) (hglobal : 0 ≤ global) (hdata : 0 ≤ data)
    (hfull : (3 : ℝ) ^ (-ell) * osc ≤
      C * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
        ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data)) :
    (3 : ℝ) ^ (alpha * (n - ell)) * osc ≤
      C * (3 : ℝ) ^ (-alpha * (m - n)) *
        (global + (3 : ℝ) ^ (3 * m / 2) * data) := by
  let S := (3 : ℝ) ^ ell * (3 : ℝ) ^ (alpha * (n - ell))
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hscaled := mul_le_mul_of_nonneg_left hfull hS
  have hcancel : S * ((3 : ℝ) ^ (-ell) * osc) =
      (3 : ℝ) ^ (alpha * (n - ell)) * osc := by
    dsimp only [S]
    calc
      ((3 : ℝ) ^ ell * (3 : ℝ) ^ (alpha * (n - ell))) *
          ((3 : ℝ) ^ (-ell) * osc) =
        ((3 : ℝ) ^ ell * (3 : ℝ) ^ (-ell)) *
          ((3 : ℝ) ^ (alpha * (n - ell)) * osc) := by ring
      _ = (3 : ℝ) ^ (alpha * (n - ell)) * osc := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        norm_num
  rw [hcancel] at hscaled
  have hfactor := holderCampanato_scale_factor_le (n := n) halpha hellm
  have hglobalTerm :
      S * (C * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
          ((3 : ℝ) ^ (-m) * global)) ≤
        C * (3 : ℝ) ^ (-alpha * (m - n)) * global := by
    have hmul := mul_le_mul_of_nonneg_right hfactor hglobal
    have hmulC := mul_le_mul_of_nonneg_left hmul hC
    dsimp only [S]
    convert hmulC using 1 <;> ring
  have hdataScale :
      (3 : ℝ) ^ ell * (3 : ℝ) ^ (alpha * (n - ell)) *
          (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
          (3 : ℝ) ^ (m / 2) ≤
        (3 : ℝ) ^ (-alpha * (m - n)) * (3 : ℝ) ^ (3 * m / 2) := by
    have hpositive : 0 ≤ (3 : ℝ) ^ (3 * m / 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hfactor hpositive
    have hpower : (3 : ℝ) ^ (-m) * (3 : ℝ) ^ (3 * m / 2) =
        (3 : ℝ) ^ (m / 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    calc
      (3 : ℝ) ^ ell * (3 : ℝ) ^ (alpha * (n - ell)) *
          (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
          (3 : ℝ) ^ (m / 2) =
          (3 : ℝ) ^ ell * (3 : ℝ) ^ (alpha * (n - ell)) *
          (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
          (3 : ℝ) ^ (-m) * (3 : ℝ) ^ (3 * m / 2) := by
        rw [← hpower]
        ring
      _ ≤ (3 : ℝ) ^ (-alpha * (m - n)) * (3 : ℝ) ^ (3 * m / 2) := hmul
  have hdataTerm :
      S * (C * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
          ((3 : ℝ) ^ (m / 2) * data)) ≤
        C * (3 : ℝ) ^ (-alpha * (m - n)) *
          ((3 : ℝ) ^ (3 * m / 2) * data) := by
    have hmul := mul_le_mul_of_nonneg_right hdataScale hdata
    have hmulC := mul_le_mul_of_nonneg_left hmul hC
    dsimp only [S]
    convert hmulC using 1 <;> ring
  calc
    (3 : ℝ) ^ (alpha * (n - ell)) * osc ≤
        S * (C * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
          ((3 : ℝ) ^ (-m) * global + (3 : ℝ) ^ (m / 2) * data)) := hscaled
    _ = S * (C * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
          ((3 : ℝ) ^ (-m) * global)) +
        S * (C * (3 : ℝ) ^ ((1 - alpha) * (m - ell) / 2) *
          ((3 : ℝ) ^ (m / 2) * data)) := by ring
    _ ≤ C * (3 : ℝ) ^ (-alpha * (m - n)) * global +
        C * (3 : ℝ) ^ (-alpha * (m - n)) *
          ((3 : ℝ) ^ (3 * m / 2) * data) := add_le_add hglobalTerm hdataTerm
    _ = C * (3 : ℝ) ^ (-alpha * (m - n)) *
        (global + (3 : ℝ) ^ (3 * m / 2) * data) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
