module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.CollapseArithmetic

@[expose] public section

/-!
# The four-leg scalar collapse of the boundary sharp-loop carrier

`Section6HarmonicInterior.ComparisonCollapse` collapses the real readout of
`flatComparatorSharpGoodEventLoopBound` into the *two* printed terms of the
interior anchor.  In the boundary regime the weighted-energy slot carries two
further legs — the affine boundary mean `|(∇h)_U|` and the fractional datum
seminorm `[∇h]_s` — so the first summand of the readout collapses into *four*
terms.

The three lemmas below are the pure scalar algebra of that collapse, written in
the polynomial variable `S1 = s^{-1/2}` exactly as in the interior file.  The
exponent trace, with `κ := 8 A Ct V Ck`:

* window oscillation `W`   : `κ S1⁴ Er W`                      → `C s^{-2} 𝓔 ‖u-(u)_U‖`
* boundary mean `AH`       : `κ S1⁴ Er N3 AH ≤ κ S1⁷ Er N3 AH` → `C s^{-2} 𝓔 · s^{-3/2} 3ⁿ |(∇h)_U|`
* force seminorm `G`       : `κ Cerr S1¹⁶ σ⁻¹ N3 T G`          → `C s^{-8} σ⁻¹ 3^{(1+s)n} [g]_s`
* datum seminorm `Hd`      : `κ Cerr S1⁸ N3 T Hd`              → `C s^{-4} 3^{(1+s)n} [∇h]_s`

Every leg lands strictly inside its slot: the boundary mean leg is paid
at `S1⁴` against a printed `S1⁷`, and the datum seminorm leg at `S1⁸` against a
printed `S1⁸`.  No new power of `s` is spent.

`bcollapse_term2` and `bcollapse_term3` are the additive-dual and direct-forcing
legs.  They are unchanged from the interior collapse (the datum does not enter
them) and are re-proved here under distinct names because the interior versions
are `private`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book

noncomputable section

/-- **The coarse-graining leg of the boundary collapse.**  Four printed terms,
one for each budget of `e.harmonic.approximation.energy`. -/
theorem bcollapse_term1
    {A cs sgi p1 Ct p2 R e3 E Sv V Er Ck S1 N3 T W G AH Hd : ℝ}
    (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hV : 0 ≤ V) (_hCk : 0 ≤ Ck)
    (hR : 0 < R) (hS1 : 0 ≤ S1) (hN3 : 0 < N3) (_hT : 0 ≤ T)
    (hEr : 0 ≤ Er) (_hW : 0 ≤ W) (_hG : 0 ≤ G) (_hAH : 0 ≤ AH) (_hHd : 0 ≤ Hd)
    (hcs : cs = N3 / 9) (hsgi : sgi = (R * R)⁻¹)
    (_hp10 : 0 ≤ p1) (hp1 : p1 ≤ 2 * S1)
    (hp2 : p2 = 2 * S1 ^ 2)
    (he30 : 0 ≤ e3) (he3 : e3 ≤ 3)
    (hE0 : 0 ≤ E) (hE : E ≤ V * 3 * Er)
    (hSv0 : 0 ≤ Sv)
    (hSv : Sv ≤ 2 * S1 * Ck * (R * N3⁻¹ * W + R * AH +
      S1 ^ 12 * R⁻¹ * T * G + S1 ^ 4 * R * T * Hd)) :
    A * cs * sgi * (p1 * (Ct * p2 * R * e3 * E * Sv)) ≤
      (8 * A * Ct * V * Ck) * S1 ^ 4 * Er * W +
        (8 * A * Ct * V * Ck) * S1 ^ 4 * Er * N3 * AH +
        (8 * A * Ct * V * Ck) * Er * S1 ^ 16 * (R * R)⁻¹ * N3 * T * G +
        (8 * A * Ct * V * Ck) * Er * S1 ^ 8 * N3 * T * Hd := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hNne : N3 ≠ 0 := ne_of_gt hN3
  subst hcs hsgi hp2
  have hstep : A * (N3 / 9) * (R * R)⁻¹ *
      (p1 * (Ct * (2 * S1 ^ 2) * R * e3 * E * Sv)) ≤
      A * (N3 / 9) * (R * R)⁻¹ *
        ((2 * S1) * (Ct * (2 * S1 ^ 2) * R * 3 * (V * 3 * Er) *
          (2 * S1 * Ck * (R * N3⁻¹ * W + R * AH +
            S1 ^ 12 * R⁻¹ * T * G + S1 ^ 4 * R * T * Hd)))) := by
    have hbase : 0 ≤ A * (N3 / 9) * (R * R)⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hbase
    have hinner : Ct * (2 * S1 ^ 2) * R * e3 * E * Sv ≤
        Ct * (2 * S1 ^ 2) * R * 3 * (V * 3 * Er) *
          (2 * S1 * Ck * (R * N3⁻¹ * W + R * AH +
            S1 ^ 12 * R⁻¹ * T * G + S1 ^ 4 * R * T * Hd)) := by
      have h1 : Ct * (2 * S1 ^ 2) * R * e3 ≤ Ct * (2 * S1 ^ 2) * R * 3 :=
        mul_le_mul_of_nonneg_left he3 (by positivity)
      have h2 : Ct * (2 * S1 ^ 2) * R * e3 * E ≤
          Ct * (2 * S1 ^ 2) * R * 3 * (V * 3 * Er) :=
        mul_le_mul h1 hE hE0 (by positivity)
      exact mul_le_mul h2 hSv hSv0 (by positivity)
    calc p1 * (Ct * (2 * S1 ^ 2) * R * e3 * E * Sv) ≤
          (2 * S1) * (Ct * (2 * S1 ^ 2) * R * e3 * E * Sv) :=
          mul_le_mul_of_nonneg_right hp1 (by positivity)
      _ ≤ (2 * S1) * (Ct * (2 * S1 ^ 2) * R * 3 * (V * 3 * Er) *
            (2 * S1 * Ck * (R * N3⁻¹ * W + R * AH +
              S1 ^ 12 * R⁻¹ * T * G + S1 ^ 4 * R * T * Hd))) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
  refine hstep.trans ?_
  have heq : A * (N3 / 9) * (R * R)⁻¹ *
      ((2 * S1) * (Ct * (2 * S1 ^ 2) * R * 3 * (V * 3 * Er) *
        (2 * S1 * Ck * (R * N3⁻¹ * W + R * AH +
          S1 ^ 12 * R⁻¹ * T * G + S1 ^ 4 * R * T * Hd)))) =
      (8 * A * Ct * V * Ck) * S1 ^ 4 * Er * W +
        (8 * A * Ct * V * Ck) * S1 ^ 4 * Er * N3 * AH +
        (8 * A * Ct * V * Ck) * Er * S1 ^ 16 * (R * R)⁻¹ * N3 * T * G +
        (8 * A * Ct * V * Ck) * Er * S1 ^ 8 * N3 * T * Hd := by
    field_simp
    ring
  exact le_of_eq heq

/-- The additive-dual leg.  Identical to the interior collapse. -/
theorem bcollapse_term2
    {A cs sgi p1 Ct p9 pinv q3 t3 Dv Cdc CY1 R S1 N3 T G : ℝ}
    (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hCdc : 0 ≤ Cdc) (hCY1 : 0 ≤ CY1)
    (hR : 0 < R) (hS1 : 1 ≤ S1) (hN3 : 0 < N3) (hT : 0 ≤ T) (hG : 0 ≤ G)
    (hcs : cs = N3 / 9) (hsgi : sgi = (R * R)⁻¹)
    (_hp10 : 0 ≤ p1) (hp1 : p1 ≤ 2 * S1)
    (hp90 : 0 ≤ p9) (hp9 : p9 ≤ 32 * S1 ^ 9)
    (hpinv : pinv = 2 * S1 ^ 2)
    (hq30 : 0 ≤ q3) (hq3 : q3 ≤ CY1)
    (ht30 : 0 ≤ t3) (ht3 : t3 ≤ T)
    (hDv : Dv = Cdc * S1 * G) :
    A * cs * sgi * (p1 * (Ct * p9 * pinv * q3 * t3 * Dv)) ≤
      ((128 / 9) * A * Ct * Cdc * CY1) * S1 ^ 16 * (R * R)⁻¹ * N3 * T * G := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hNne : N3 ≠ 0 := ne_of_gt hN3
  have hS10 : (0 : ℝ) ≤ S1 := le_trans zero_le_one hS1
  subst hcs hsgi hpinv hDv
  have hstep : A * (N3 / 9) * (R * R)⁻¹ *
        (p1 * (Ct * p9 * (2 * S1 ^ 2) * q3 * t3 * (Cdc * S1 * G))) ≤
      A * (N3 / 9) * (R * R)⁻¹ *
        ((2 * S1) * (Ct * (32 * S1 ^ 9) * (2 * S1 ^ 2) * CY1 * T *
          (Cdc * S1 * G))) := by
    have hbase : 0 ≤ A * (N3 / 9) * (R * R)⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hbase
    have hinner : Ct * p9 * (2 * S1 ^ 2) * q3 * t3 * (Cdc * S1 * G) ≤
        Ct * (32 * S1 ^ 9) * (2 * S1 ^ 2) * CY1 * T * (Cdc * S1 * G) := by
      have h1 : Ct * p9 ≤ Ct * (32 * S1 ^ 9) :=
        mul_le_mul_of_nonneg_left hp9 hCt
      have h2 : Ct * p9 * (2 * S1 ^ 2) ≤ Ct * (32 * S1 ^ 9) * (2 * S1 ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : Ct * p9 * (2 * S1 ^ 2) * q3 ≤
          Ct * (32 * S1 ^ 9) * (2 * S1 ^ 2) * CY1 :=
        mul_le_mul h2 hq3 hq30 (by positivity)
      have h4 : Ct * p9 * (2 * S1 ^ 2) * q3 * t3 ≤
          Ct * (32 * S1 ^ 9) * (2 * S1 ^ 2) * CY1 * T :=
        mul_le_mul h3 ht3 ht30 (by positivity)
      exact mul_le_mul_of_nonneg_right h4 (by positivity)
    calc p1 * (Ct * p9 * (2 * S1 ^ 2) * q3 * t3 * (Cdc * S1 * G)) ≤
          (2 * S1) * (Ct * p9 * (2 * S1 ^ 2) * q3 * t3 * (Cdc * S1 * G)) :=
          mul_le_mul_of_nonneg_right hp1 (by positivity)
      _ ≤ (2 * S1) * (Ct * (32 * S1 ^ 9) * (2 * S1 ^ 2) * CY1 * T *
            (Cdc * S1 * G)) := mul_le_mul_of_nonneg_left hinner (by positivity)
  refine hstep.trans ?_
  have heq : A * (N3 / 9) * (R * R)⁻¹ *
      ((2 * S1) * (Ct * (32 * S1 ^ 9) * (2 * S1 ^ 2) * CY1 * T *
        (Cdc * S1 * G))) =
      ((128 / 9) * A * Ct * Cdc * CY1) * S1 ^ 13 * (R * R)⁻¹ * N3 * T * G := by
    field_simp
    ring
  rw [heq]
  have hpow : S1 ^ 13 ≤ S1 ^ 16 := pow_le_pow_right₀ hS1 (by norm_num)
  have hbase : 0 ≤ ((128 / 9) * A * Ct * Cdc * CY1) := by positivity
  have hrest : 0 ≤ (R * R)⁻¹ * N3 * T * G := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hbase, hrest]

/-- The direct-forcing leg.  Identical to the interior collapse. -/
theorem bcollapse_term3
    {UD cs dd sgi SC Bv CB R S1 N3 T G : ℝ}
    (hUD : 0 ≤ UD) (hdd : 0 ≤ dd) (hSC : 0 ≤ SC) (hCB : 0 ≤ CB)
    (hR : 0 < R) (hS1 : 1 ≤ S1) (hN3 : 0 < N3) (hT : 0 ≤ T) (hG : 0 ≤ G)
    (hcs : cs = N3 / 9) (hsgi : sgi = (R * R)⁻¹)
    (_hBv0 : 0 ≤ Bv) (hBv : Bv ≤ CB * T * S1 * G) :
    UD * cs * dd * sgi * (SC * Bv) ≤
      ((1 / 9) * UD * dd * SC * CB) * S1 ^ 16 * (R * R)⁻¹ * N3 * T * G := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hNne : N3 ≠ 0 := ne_of_gt hN3
  have hS10 : (0 : ℝ) ≤ S1 := le_trans zero_le_one hS1
  subst hcs hsgi
  have hstep : UD * (N3 / 9) * dd * (R * R)⁻¹ * (SC * Bv) ≤
      UD * (N3 / 9) * dd * (R * R)⁻¹ * (SC * (CB * T * S1 * G)) := by
    have hbase : 0 ≤ UD * (N3 / 9) * dd * (R * R)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hBv hSC) hbase
  refine hstep.trans ?_
  have heq : UD * (N3 / 9) * dd * (R * R)⁻¹ * (SC * (CB * T * S1 * G)) =
      ((1 / 9) * UD * dd * SC * CB) * S1 ^ 1 * (R * R)⁻¹ * N3 * T * G := by
    field_simp
  rw [heq]
  have hpow : S1 ^ 1 ≤ S1 ^ 16 := pow_le_pow_right₀ hS1 (by norm_num)
  have hbase : 0 ≤ ((1 / 9) * UD * dd * SC * CB) := by positivity
  have hrest : 0 ≤ (R * R)⁻¹ * N3 * T * G := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hbase, hrest]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
