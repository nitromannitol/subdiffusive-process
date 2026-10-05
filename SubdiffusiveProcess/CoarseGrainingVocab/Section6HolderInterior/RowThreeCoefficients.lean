module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.IterationEpsilonBound

@[expose] public section

/-!
# Row 3's long branch: the coefficient comparisons, and the shape match

The excess conjunct of `exists_interiorHolderIterationApplied` at windows
`(n+1, ell-1)` has the shape

```text
  exN1 ≤ P * (thetaGap * exTop + R * 3 ^ (-top) * oscTop + (1 + R) * D)
```

and `hgrid` wants `exN1 ≤ A1 * exTop + A2 * oscTop + A3`.
`interiorRowThree_shapeMatch` is the recombination; the content is in the
coefficient comparisons, each of which is **constant arithmetic**, because row
3's short-window hypothesis bounds the prefactor `P` by an absolute constant
(`shortWindow_exponential_le`).  No gap-uniformity argument is needed on this
row.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}

/-- Recombining the iteration's excess row into `hgrid`'s shape. -/
theorem interiorRowThree_shapeMatch
    {exN1 P thetaGap R exTop oscTop D A1 A2 A3 top : ℝ}
    (hchain : exN1 ≤ P * (thetaGap * exTop + R * (3 : ℝ) ^ (-top) * oscTop +
      (1 + R) * D))
    (ha : P * thetaGap ≤ A1) (hb : P * (R * (3 : ℝ) ^ (-top)) ≤ A2)
    (hc : P * ((1 + R) * D) ≤ A3)
    (hexTop : 0 ≤ exTop) (hoscTop : 0 ≤ oscTop) :
    exN1 ≤ A1 * exTop + A2 * oscTop + A3 := by
  have hstep : P * (thetaGap * exTop + R * (3 : ℝ) ^ (-top) * oscTop +
      (1 + R) * D) =
      (P * thetaGap) * exTop + (P * (R * (3 : ℝ) ^ (-top))) * oscTop +
        P * ((1 + R) * D) := by ring
  rw [hstep] at hchain
  refine hchain.trans ?_
  have h1 : (P * thetaGap) * exTop ≤ A1 * exTop :=
    mul_le_mul_of_nonneg_right ha hexTop
  have h2 : (P * (R * (3 : ℝ) ^ (-top))) * oscTop ≤ A2 * oscTop :=
    mul_le_mul_of_nonneg_right hb hoscTop
  linarith

/-- The iteration's gap `ell - n - 2` in real form. -/
theorem rowThree_gap_cast {n ell : ℕ} (hell : n + 2 ≤ ell) :
    ((ell - n - 2 : ℕ) : ℝ) = (ell : ℝ) - (n : ℝ) - 2 := by
  have hrw : ell - n - 2 = ell - (n + 2) := by omega
  rw [hrw, Nat.cast_sub hell]
  push_cast
  ring

/-- **The contraction coefficient.**  The iteration contracts over the gap
`ell - n - 2` while the printed coefficient is stated at `ell - n`; the
conversion costs the absolute factor `3 ^ (1/2)`, which the constant absorbs. -/
theorem rowThree_firstCoeff_le {P Cpre theta outer C : ℝ} {n ell : ℕ}
    (hP : P ≤ Cpre) (hCpre : 0 ≤ Cpre)
    (htheta0 : 0 ≤ theta) (hthetale : theta ≤ (3 : ℝ) ^ (-(1 : ℝ) / 4))
    (houter : 0 < outer) (hell : n + 2 ≤ ell)
    (hC : Cpre * (3 : ℝ) ^ ((1 : ℝ) / 2) * outer ^ 2 ≤ C) :
    P * theta ^ (ell - n - 2) ≤
      C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) / outer ^ 2 := by
  have hpow0 : (0 : ℝ) ≤ theta ^ (ell - n - 2) := pow_nonneg htheta0 _
  -- the contraction converts to the printed decay
  have hcontract := theta_pow_le_three_pow htheta0 hthetale (ell - n - 2)
  rw [rowThree_gap_cast hell] at hcontract
  have hshift : (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ) - 2) / 4) =
      (3 : ℝ) ^ ((1 : ℝ) / 2) * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) :=
    rowThree_gap_shift
  rw [hshift] at hcontract
  have hdecay0 : (0 : ℝ) < (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hout2 : (0 : ℝ) < outer ^ 2 := by positivity
  -- assemble
  calc P * theta ^ (ell - n - 2)
      ≤ Cpre * theta ^ (ell - n - 2) :=
        mul_le_mul_of_nonneg_right hP hpow0
    _ ≤ Cpre * ((3 : ℝ) ^ ((1 : ℝ) / 2) *
          (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4)) :=
        mul_le_mul_of_nonneg_left hcontract hCpre
    _ = (Cpre * (3 : ℝ) ^ ((1 : ℝ) / 2)) *
          (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) := by ring
    _ ≤ (C / outer ^ 2) * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) := by
        refine mul_le_mul_of_nonneg_right ?_ hdecay0.le
        rw [le_div_iff₀ hout2]
        exact hC
    _ = C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) / outer ^ 2 := by ring

/-- **The oscillation coefficient.**  `R ≤ Keps * epsilon` and the manuscript's
`epsilon = C2⁻¹ sqrt (1 - alpha)` supply the `sqrt (1 - alpha)` that the
row-3 coefficient demands; the scale shift `3 ^ (-(ell-1)) = 3 * 3 ^ (-ell)`
costs the absolute factor `3`, which the constant absorbs. -/
theorem rowThree_oscCoeff_le {P Cpre R Keps C2 alpha outer osc C ellR : ℝ}
    (hP : P ≤ Cpre) (hCpre : 0 ≤ Cpre) (hR0 : 0 ≤ R)
    (hR : R ≤ Keps * (C2⁻¹ * Real.sqrt (1 - alpha)))
    (houter : 0 < outer) (hosc : 0 < osc)
    (hC : Cpre * Keps * C2⁻¹ * 3 * (outer * osc) ≤ C) :
    P * (R * (3 : ℝ) ^ (-(ellR - 1))) ≤
      C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-ellR) / (outer * osc) := by
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (1 - alpha) := Real.sqrt_nonneg _
  have hsplit : (3 : ℝ) ^ (-(ellR - 1)) = 3 * (3 : ℝ) ^ (-ellR) := by
    rw [show -(ellR - 1) = 1 + -ellR by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hz0 : (0 : ℝ) < (3 : ℝ) ^ (-ellR) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hprod : (0 : ℝ) < outer * osc := mul_pos houter hosc
  have hstep1 : P * (R * (3 : ℝ) ^ (-(ellR - 1))) ≤
      Cpre * ((Keps * (C2⁻¹ * Real.sqrt (1 - alpha))) *
        (3 * (3 : ℝ) ^ (-ellR))) := by
    rw [hsplit]
    refine mul_le_mul hP (mul_le_mul_of_nonneg_right hR (by positivity))
      (by positivity) hCpre
  have hstep2 : Cpre * ((Keps * (C2⁻¹ * Real.sqrt (1 - alpha))) *
      (3 * (3 : ℝ) ^ (-ellR))) =
      (Cpre * Keps * C2⁻¹ * 3) *
        (Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-ellR)) := by ring
  have hstep3 : (Cpre * Keps * C2⁻¹ * 3) *
      (Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-ellR)) ≤
      (C / (outer * osc)) * (Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-ellR)) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [le_div_iff₀ hprod]
    exact hC
  have hstep4 : (C / (outer * osc)) *
      (Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-ellR)) =
      C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-ellR) / (outer * osc) := by
    field_simp
  linarith [hstep1, hstep2.le, hstep2.ge, hstep3, hstep4.le, hstep4.ge]

/-- **The defect coefficient.**  `Section6Holder.sum_holderIterationDefect_le`
bounds the defect sum by `(5/2) * Kforce * 3^(-((m - l)/2)) * exponential *
topForcing` with `l = ell - 1` and `topForcing` carrying `3^(m/2)`, so the two
powers of `3` collapse to `3^((ell-1)/2)`.  The remainder is stated at
`3^(ell/2)`, so the conversion gains the absolute factor `3^(-1/2) ≤ 1`.

The two boundary summands of `sum_holderIterationDefect_le` vanish identically on
the interior branch, where `BoundaryTouches` is false. -/
theorem rowThree_defectCoeff_le
    {P Cpre R Rmax Kforce exponential tailInv seminorm outer C D ellR : ℝ}
    (hP : P ≤ Cpre) (hCpre : 0 ≤ Cpre)
    (hR0 : 0 ≤ R) (hRmax : R ≤ Rmax) (htail : 0 ≤ tailInv)
    (hsem : 0 ≤ seminorm) (houter : 0 < outer) (hD0 : 0 ≤ D)
    (hD : D ≤ 5 / 2 * Kforce * exponential * tailInv *
      ((3 : ℝ) ^ ((ellR - 1) / 2) * seminorm))
    (hC : Cpre * (1 + Rmax) * (5 / 2 * Kforce * exponential) *
      (3 : ℝ) ^ (-(1 : ℝ) / 2) * outer ≤ C) :
    P * ((1 + R) * D) ≤
      C * tailInv * (3 : ℝ) ^ (ellR / 2) * seminorm / outer := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hsplit : (3 : ℝ) ^ ((ellR - 1) / 2) =
      (3 : ℝ) ^ (-(1 : ℝ) / 2) * (3 : ℝ) ^ (ellR / 2) := by
    rw [← Real.rpow_add h3]
    congr 1
    ring
  have hpow0 : (0 : ℝ) < (3 : ℝ) ^ (ellR / 2) := Real.rpow_pos_of_pos h3 _
  have hneg0 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos h3 _
  -- push `P` and `(1 + R)` up to their bounds
  have hstep1 : P * ((1 + R) * D) ≤ Cpre * ((1 + Rmax) *
      (5 / 2 * Kforce * exponential * tailInv *
        ((3 : ℝ) ^ ((ellR - 1) / 2) * seminorm))) := by
    refine mul_le_mul hP ?_ (by positivity) hCpre
    refine mul_le_mul (by linarith) hD hD0 (by linarith)
  rw [hsplit] at hstep1
  have hkey : Cpre * ((1 + Rmax) *
      (5 / 2 * Kforce * exponential * tailInv *
        ((3 : ℝ) ^ (-(1 : ℝ) / 2) * (3 : ℝ) ^ (ellR / 2) * seminorm))) =
      (Cpre * (1 + Rmax) * (5 / 2 * Kforce * exponential) *
          (3 : ℝ) ^ (-(1 : ℝ) / 2)) *
        (tailInv * (3 : ℝ) ^ (ellR / 2) * seminorm) := by ring
  have hfinal : (Cpre * (1 + Rmax) * (5 / 2 * Kforce * exponential) *
        (3 : ℝ) ^ (-(1 : ℝ) / 2)) *
      (tailInv * (3 : ℝ) ^ (ellR / 2) * seminorm) ≤
      (C / outer) * (tailInv * (3 : ℝ) ^ (ellR / 2) * seminorm) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [le_div_iff₀ houter]
    exact hC
  have hdiv : (C / outer) * (tailInv * (3 : ℝ) ^ (ellR / 2) * seminorm) =
      C * tailInv * (3 : ℝ) ^ (ellR / 2) * seminorm / outer := by
    field_simp
  linarith [hstep1, hkey.le, hkey.ge, hfinal, hdiv.le, hdiv.ge]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
