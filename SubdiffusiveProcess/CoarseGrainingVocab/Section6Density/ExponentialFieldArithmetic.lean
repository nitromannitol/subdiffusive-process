import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ExponentialFieldBlock

/-!
# Arithmetic for one exponential-field block

This module absorbs the shared spatial cover, the `2j+1` independent shell
mgfs, and the logarithmic threshold into the manuscript's Gaussian rate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open Homogenization.IndependentSums
open scoped BigOperators ENNReal

noncomputable section

/-- Denominator in the common Chernoff parameter `l=s/(D delta^2)`. -/
def expFieldMomentDenom : ℝ :=
  16 * (1 + gammaSigmaLargeMgfConst 2 * absoluteSmallShellConst ^ 2)

theorem expFieldMomentDenom_pos : 0 < expFieldMomentDenom := by
  unfold expFieldMomentDenom
  have hmgf := gammaSigmaLargeMgfConst_pos (by norm_num : (1 : ℝ) < 2)
  have hA := absoluteSmallShellConst_pos
  positivity

/-- A dimension-dependent smallness constant for the shared-cover block. -/
def expFieldBlockConst (d : ℕ) : ℝ :=
  1 + 24 * expFieldMomentDenom *
    (1 + shellCoverLogConst * (d : ℝ) + Real.log 2)

theorem expFieldBlockConst_pos (d : ℕ) : 0 < expFieldBlockConst d := by
  unfold expFieldBlockConst
  have hD := expFieldMomentDenom_pos
  have hcover := shellCoverLogConst_pos
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

def expFieldChernoff (s delta : ℝ) : ℝ :=
  s / (expFieldMomentDenom * delta ^ 2)

def expFieldBlockRate (s delta : ℝ) : ℝ :=
  s ^ 2 / (2 * expFieldMomentDenom * delta ^ 2)

theorem expFieldChernoff_nonneg {s delta : ℝ}
    (hs : 0 < s) (hdelta : 0 < delta) :
    0 ≤ expFieldChernoff s delta := by
  unfold expFieldChernoff
  exact (div_pos hs
    (mul_pos expFieldMomentDenom_pos (sq_pos_of_pos hdelta))).le

private theorem expField_threshold_ge {s : ℝ} {j : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) :
    s * ((j : ℝ) + 1) ≤ expFieldThreshold s j := by
  unfold expFieldThreshold
  have hlog := SubdiffusiveProcess.Concentration.log_three_gt_one
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith [mul_nonneg hs.le hj,
    mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hlog.le)]

private theorem expField_coverGap_pos (k j h : ℕ) (hh : 1 ≤ h) :
    0 < ((k + h + j : ℕ) : ℤ) - ((k - j : ℕ) : ℤ) := by
  omega

private theorem expField_coverGap_le (k j h : ℕ) :
    ((k + h + j : ℕ) : ℤ) - ((k - j : ℕ) : ℤ) ≤
      ((h + 2 * j : ℕ) : ℤ) := by
  omega

private theorem expField_ratio_ge_const_sq
    {d : ℕ} {s delta : ℝ}
    (hdelta : 0 < delta) (_hs : 0 < s)
    (hsmall : expFieldBlockConst d * delta ≤ s) :
    expFieldBlockConst d ^ 2 ≤ s ^ 2 / delta ^ 2 := by
  have hsquare := pow_le_pow_left₀
    (mul_nonneg (expFieldBlockConst_pos d).le hdelta.le) hsmall 2
  rw [mul_pow] at hsquare
  rw [le_div_iff₀ (sq_pos_of_pos hdelta)]
  nlinarith only [hsquare]

private theorem expField_ratio_ge_const_sq_mul_h
    {d h : ℕ} {s delta : ℝ}
    (hdelta : 0 < delta) (_hs : 0 < s)
    (hsmall : expFieldBlockConst d * delta * Real.sqrt (h : ℝ) ≤ s) :
    expFieldBlockConst d ^ 2 * (h : ℝ) ≤ s ^ 2 / delta ^ 2 := by
  have hleft0 : 0 ≤ expFieldBlockConst d * delta * Real.sqrt (h : ℝ) := by
    exact mul_nonneg
      (mul_nonneg (expFieldBlockConst_pos d).le hdelta.le)
      (Real.sqrt_nonneg _)
  have hsquare := pow_le_pow_left₀ hleft0 hsmall 2
  rw [le_div_iff₀ (sq_pos_of_pos hdelta)]
  have hsqrt : Real.sqrt (h : ℝ) ^ 2 = (h : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg h)
  calc
    expFieldBlockConst d ^ 2 * (h : ℝ) * delta ^ 2 =
        expFieldBlockConst d ^ 2 * delta ^ 2 * Real.sqrt (h : ℝ) ^ 2 := by
      rw [hsqrt]
      ring
    _ = (expFieldBlockConst d * delta * Real.sqrt (h : ℝ)) ^ 2 := by ring
    _ ≤ s ^ 2 := hsquare

/-- The complete one-block numerical absorption. -/
theorem expFieldBlock_numeric {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {k j h : ℕ} (hh : 1 ≤ h)
    (hsmall : expFieldBlockConst d * M.delta ≤ s)
    (hsmallh : expFieldBlockConst d * M.delta * Real.sqrt (h : ℝ) ≤ s) :
    Real.log ((shellCoverShifts d
        (((k + h + j : ℕ) : ℤ) - ((k - j : ℕ) : ℤ))).card : ℝ) +
      (-expFieldChernoff s M.delta * expFieldThreshold s j +
        ((Finset.Icc (k - j) (k + j)).card : ℝ) *
          (Real.log 2 + gammaSigmaLargeMgfConst 2 *
            ((absoluteSmallShellConst * M.delta) *
              expFieldChernoff s M.delta) ^ gammaExpConjExponent 2)) ≤
      -expFieldBlockRate s M.delta * ((j : ℝ) + 1) := by
  let D := expFieldMomentDenom
  let C := expFieldBlockConst d
  let q := s ^ 2 / (D * M.delta ^ 2)
  have hdelta := M.shellPrefix.delta_pos
  have hD : 0 < D := expFieldMomentDenom_pos
  have hC : 0 < C := expFieldBlockConst_pos d
  have hq : 0 < q := div_pos (sq_pos_of_pos hs)
    (mul_pos hD (sq_pos_of_pos hdelta))
  have hratio := expField_ratio_ge_const_sq hdelta hs hsmall
  have hratioH := expField_ratio_ge_const_sq_mul_h hdelta hs hsmallh
  have hthreshold := expField_threshold_ge hs hs1 (j := j)
  have hneg : -expFieldChernoff s M.delta * expFieldThreshold s j ≤
      -q * ((j : ℝ) + 1) := by
    have hl : 0 ≤ expFieldChernoff s M.delta :=
      expFieldChernoff_nonneg hs hdelta
    have hmul := mul_le_mul_of_nonneg_left hthreshold hl
    have heq : expFieldChernoff s M.delta * s = q := by
      unfold expFieldChernoff
      dsimp [q, D]
      field_simp [hdelta.ne', hD.ne']
    nlinarith only [hmul, heq]
  have hcardN := expFieldBlock_card_le k j
  have hN : (((Finset.Icc (k - j) (k + j)).card : ℕ) : ℝ) ≤
      2 * ((j : ℝ) + 1) := by
    exact_mod_cast (hcardN.trans (by omega : 2 * j + 1 ≤ 2 * (j + 1)))
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hCdef : 24 * D * (1 + shellCoverLogConst * (d : ℝ) + Real.log 2) ≤
      C ^ 2 := by
    have hone : (1 : ℝ) ≤ C := by
      unfold C expFieldBlockConst
      have hD0 := expFieldMomentDenom_pos.le
      have hinside : 0 ≤
          1 + shellCoverLogConst * (d : ℝ) + Real.log 2 := by
        exact add_nonneg
          (add_nonneg zero_le_one
            (mul_nonneg shellCoverLogConst_pos.le (Nat.cast_nonneg d)))
          (Real.log_nonneg (by norm_num))
      nlinarith
    have hpart : 24 * D *
        (1 + shellCoverLogConst * (d : ℝ) + Real.log 2) ≤ C := by
      unfold C expFieldBlockConst
      linarith
    nlinarith only [hpart, hone]
  have hqLog : 16 * Real.log 2 ≤ q := by
    have hpart : 16 * D * Real.log 2 ≤ C ^ 2 := by
      have hrest : 0 ≤ 1 + shellCoverLogConst * (d : ℝ) := by
        exact add_nonneg zero_le_one
          (mul_nonneg shellCoverLogConst_pos.le (Nat.cast_nonneg d))
      nlinarith only [hCdef, hD.le, hlogTwo, hrest]
    have hpart' : 16 * D * Real.log 2 ≤ s ^ 2 / M.delta ^ 2 :=
      hpart.trans hratio
    have hqeq : q = (s ^ 2 / M.delta ^ 2) / D := by
      dsimp [q]
      field_simp [hdelta.ne', hD.ne']
    rw [hqeq, le_div_iff₀ hD]
    nlinarith only [hpart']
  have hlogTerm :
      (((Finset.Icc (k - j) (k + j)).card : ℕ) : ℝ) * Real.log 2 ≤
        q / 8 * ((j : ℝ) + 1) := by
    calc
      _ ≤ 2 * ((j : ℝ) + 1) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hN hlogTwo
      _ ≤ q / 8 * ((j : ℝ) + 1) := by
        have hj0 : 0 ≤ (j : ℝ) + 1 := by positivity
        nlinarith only [hqLog, hj0, mul_nonneg hlogTwo hj0]
  have hmgfC := gammaSigmaLargeMgfConst_pos (by norm_num : (1 : ℝ) < 2)
  have hDmgf : 16 * gammaSigmaLargeMgfConst 2 * absoluteSmallShellConst ^ 2 ≤ D := by
    unfold D expFieldMomentDenom
    nlinarith only [hmgfC.le, sq_nonneg absoluteSmallShellConst]
  have hmgfTerm :
      (((Finset.Icc (k - j) (k + j)).card : ℕ) : ℝ) *
          (gammaSigmaLargeMgfConst 2 *
            ((absoluteSmallShellConst * M.delta) *
              expFieldChernoff s M.delta) ^ gammaExpConjExponent 2) ≤
        q / 8 * ((j : ℝ) + 1) := by
    rw [show gammaExpConjExponent 2 = 2 by norm_num [gammaExpConjExponent],
      Real.rpow_two]
    have hj0 : 0 ≤ (j : ℝ) + 1 := by positivity
    have hraw : 2 * gammaSigmaLargeMgfConst 2 * absoluteSmallShellConst ^ 2 / D ≤
        (1 / 8 : ℝ) := by
      rw [div_le_iff₀ hD]
      nlinarith only [hDmgf]
    calc
      _ ≤ 2 * ((j : ℝ) + 1) *
          (gammaSigmaLargeMgfConst 2 *
            ((absoluteSmallShellConst * M.delta) *
              expFieldChernoff s M.delta) ^ 2) :=
        mul_le_mul_of_nonneg_right hN
          (mul_nonneg hmgfC.le (sq_nonneg _))
      _ = (2 * gammaSigmaLargeMgfConst 2 * absoluteSmallShellConst ^ 2 / D) *
          q * ((j : ℝ) + 1) := by
        unfold expFieldChernoff
        dsimp [q, D]
        field_simp [hdelta.ne', hD.ne']
      _ ≤ (1 / 8 : ℝ) * q * ((j : ℝ) + 1) := by
        have hrawq := mul_le_mul_of_nonneg_right hraw hq.le
        exact mul_le_mul_of_nonneg_right hrawq hj0
      _ = q / 8 * ((j : ℝ) + 1) := by ring
  let r : ℤ := ((k + h + j : ℕ) : ℤ) - ((k - j : ℕ) : ℤ)
  have hr : 0 < r := expField_coverGap_pos k j h hh
  have hrle : r ≤ ((h + 2 * j : ℕ) : ℤ) := expField_coverGap_le k j h
  have hcoverRaw := three_mul_log_card_shellCoverShifts_le M hr
  have hcoverGeom : Real.log ((shellCoverShifts d r).card : ℝ) ≤
      shellCoverLogConst * (d : ℝ) * ((h : ℝ) + 2 * (j : ℝ)) := by
    have hrleR : (r : ℝ) ≤ (h : ℝ) + 2 * (j : ℝ) := by
      exact_mod_cast hrle
    have hcoef : 0 ≤ shellCoverLogConst * (d : ℝ) :=
      mul_nonneg shellCoverLogConst_pos.le (Nat.cast_nonneg d)
    have hscaled := mul_le_mul_of_nonneg_left hrleR hcoef
    have hright0 : 0 ≤ shellCoverLogConst * (d : ℝ) *
        ((h : ℝ) + 2 * (j : ℝ)) := by positivity
    nlinarith only [hcoverRaw, hscaled, hright0]
  have hqGeom : 8 * shellCoverLogConst * (d : ℝ) *
      ((h : ℝ) + 2) ≤ q := by
    have hgeomC : 24 * D * shellCoverLogConst * (d : ℝ) ≤ C ^ 2 := by
      have hrest : 0 ≤ 1 + Real.log 2 := by positivity
      nlinarith only [hCdef, hD.le, shellCoverLogConst_pos.le,
        (Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ)), hrest]
    have hsumRatio : C ^ 2 * ((h : ℝ) + 2) ≤
        3 * (s ^ 2 / M.delta ^ 2) := by
      nlinarith only [hratio, hratioH, sq_nonneg C]
    have hgeomRatio : 8 * D * shellCoverLogConst * (d : ℝ) *
        ((h : ℝ) + 2) ≤ s ^ 2 / M.delta ^ 2 := by
      nlinarith only [hgeomC, hsumRatio, hD]
    have hqeq : q = (s ^ 2 / M.delta ^ 2) / D := by
      dsimp [q]
      field_simp [hdelta.ne', hD.ne']
    rw [hqeq, le_div_iff₀ hD]
    nlinarith only [hgeomRatio]
  have hcoverTerm : Real.log ((shellCoverShifts d r).card : ℝ) ≤
      q / 8 * ((j : ℝ) + 1) := by
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hfactor : (h : ℝ) + 2 * (j : ℝ) ≤
        ((h : ℝ) + 2) * ((j : ℝ) + 1) := by
      have hhR : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
      nlinarith
    calc
      _ ≤ shellCoverLogConst * (d : ℝ) *
          ((h : ℝ) + 2 * (j : ℝ)) := hcoverGeom
      _ ≤ shellCoverLogConst * (d : ℝ) *
          (((h : ℝ) + 2) * ((j : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg shellCoverLogConst_pos.le (Nat.cast_nonneg d))
      _ ≤ q / 8 * ((j : ℝ) + 1) := by
        have hj1 : 0 ≤ (j : ℝ) + 1 := by positivity
        nlinarith only [hqGeom, hj1,
          mul_nonneg (mul_nonneg shellCoverLogConst_pos.le (Nat.cast_nonneg d))
            (by positivity : 0 ≤ (h : ℝ) + 2)]
  have hblockTerm :
      (((Finset.Icc (k - j) (k + j)).card : ℕ) : ℝ) *
        (Real.log 2 + gammaSigmaLargeMgfConst 2 *
          ((absoluteSmallShellConst * M.delta) *
            expFieldChernoff s M.delta) ^ gammaExpConjExponent 2) ≤
      q / 4 * ((j : ℝ) + 1) := by
    nlinarith only [hlogTerm, hmgfTerm]
  have hrate : expFieldBlockRate s M.delta = q / 2 := by
    unfold expFieldBlockRate
    dsimp [q, D]
    field_simp [hdelta.ne', hD.ne']
  change Real.log ((shellCoverShifts d r).card : ℝ) + _ ≤ _
  rw [hrate]
  have hjq : 0 ≤ q * ((j : ℝ) + 1) := by positivity
  nlinarith only [hneg, hcoverTerm, hblockTerm, hjq]

/-- Single-block tail in the exact linear-in-block-length form used by both
the large-radius sum and the packed fixed-configuration estimate. -/
theorem measureReal_expFieldBlockExceeds_le_exp {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {k j h : ℕ} (hh : 1 ≤ h)
    (hsmall : expFieldBlockConst d * M.delta ≤ s)
    (hsmallh : expFieldBlockConst d * M.delta * Real.sqrt (h : ℝ) ≤ s) :
    M.P.toMeasure.real (expFieldBlockExceeds (d := d) s k j h) ≤
      Real.exp (-expFieldBlockRate s M.delta * ((j : ℝ) + 1)) := by
  have hl := expFieldChernoff_nonneg hs M.shellPrefix.delta_pos
  have hraw := measureReal_expFieldBlockExceeds_le M s k j h
    (expFieldChernoff s M.delta) hl
  have hnum := expFieldBlock_numeric M hs hs1 (k := k) (j := j)
    (h := h) hh hsmall hsmallh
  have hcardPos : 0 < ((shellCoverShifts d
      (((k + h + j : ℕ) : ℤ) - ((k - j : ℕ) : ℤ))).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (shellCoverShifts_nonempty d _))
  calc
    M.P.toMeasure.real (expFieldBlockExceeds (d := d) s k j h) ≤ _ := hraw
    _ = Real.exp
        (Real.log ((shellCoverShifts d
          (((k + h + j : ℕ) : ℤ) - ((k - j : ℕ) : ℤ))).card : ℝ) +
          (-expFieldChernoff s M.delta * expFieldThreshold s j +
            ((Finset.Icc (k - j) (k + j)).card : ℝ) *
              (Real.log 2 + gammaSigmaLargeMgfConst 2 *
                ((absoluteSmallShellConst * M.delta) *
                  expFieldChernoff s M.delta) ^ gammaExpConjExponent 2))) := by
      let cardR : ℝ := ((shellCoverShifts d
        (((k + h + j : ℕ) : ℤ) - ((k - j : ℕ) : ℤ))).card : ℝ)
      let E : ℝ :=
        -expFieldChernoff s M.delta * expFieldThreshold s j +
          ((Finset.Icc (k - j) (k + j)).card : ℝ) *
            (Real.log 2 + gammaSigmaLargeMgfConst 2 *
              ((absoluteSmallShellConst * M.delta) *
                expFieldChernoff s M.delta) ^ gammaExpConjExponent 2)
      change cardR * Real.exp E = Real.exp (Real.log cardR + E)
      calc
        cardR * Real.exp E = Real.exp (Real.log cardR) * Real.exp E := by
          rw [Real.exp_log hcardPos]
        _ = Real.exp (Real.log cardR + E) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-expFieldBlockRate s M.delta * ((j : ℝ) + 1)) :=
      Real.exp_le_exp.mpr hnum

theorem measure_expFieldBlockExceeds_le_ofReal_exp {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {k j h : ℕ} (hh : 1 ≤ h)
    (hsmall : expFieldBlockConst d * M.delta ≤ s)
    (hsmallh : expFieldBlockConst d * M.delta * Real.sqrt (h : ℝ) ≤ s) :
    M.P.toMeasure (expFieldBlockExceeds (d := d) s k j h) ≤
      ENNReal.ofReal
        (Real.exp (-expFieldBlockRate s M.delta * ((j : ℝ) + 1))) := by
  exact (ENNReal.le_ofReal_iff_toReal_le
    (measure_ne_top M.P.toMeasure _) (Real.exp_pos _).le).2
      (measureReal_expFieldBlockExceeds_le_exp M hs hs1 hh hsmall hsmallh)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
