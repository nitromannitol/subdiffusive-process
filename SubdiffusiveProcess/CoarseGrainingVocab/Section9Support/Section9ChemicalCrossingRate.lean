module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingTail

@[expose] public section

/-!
# The scale sum is small at large `q`

The crossing estimate needs the *scale sum*

`π(q) = ∑_j ((Cbox+Cdep) 3^j + 1)^{2d} · (2 Cdep 3^j + 1)^d · max(1,Cprob) ·
        exp(-(cprob/2^d) q 3^{3j/2})`

to be small.  Because `3^{3j/2} ≥ 1 + j`, the polynomial entropy `3^{3dj}` is
beaten by the exponential as soon as `(cprob/2^d) q ≥ 3 d log 3 + 1`, and then

`π(q) ≤ 2 B exp(-(cprob/2^d) q)`,   `B = (Cbox+Cdep+1)^{2d} (2Cdep+1)^d max(1,Cprob)`,

which tends to `0`.  This is the only place where a threshold on `q` beyond the
manuscript's `q ≥ q_0(d)` is used, and the threshold depends on
`d, Cbox, Cdep, J, Cprob, cprob` only.

## Source

 (the entropy absorption).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem one_add_le_three_rpow (j : ℕ) :
    (1 : ℝ) + (j : ℝ) ≤ (3 : ℝ) ^ ((3 : ℝ) * j / 2) := by
  have h1 : (1 : ℝ) + (j : ℝ) ≤ (3 : ℝ) ^ (j : ℕ) := by
    have := one_add_mul_le_pow (a := (2 : ℝ)) (by norm_num) j
    calc (1 : ℝ) + (j : ℝ) ≤ 1 + 2 * (j : ℝ) := by
          have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
          linarith
      _ ≤ (1 + 2 : ℝ) ^ (j : ℕ) := by linarith [this]
      _ = (3 : ℝ) ^ (j : ℕ) := by norm_num
  refine h1.trans ?_
  rw [show ((3 : ℝ) ^ (j : ℕ)) = (3 : ℝ) ^ ((j : ℝ)) from (Real.rpow_natCast 3 j).symm]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  linarith

/-- The constant in the scale-sum bound. -/
def crossScaleConst (d Cbox Cdep : ℕ) (Cprob : ℝ) : ℝ :=
  (((Cbox + Cdep + 1) ^ (2 * d) * (2 * Cdep + 1) ^ d : ℕ) : ℝ) * max 1 Cprob

theorem crossScaleConst_pos (d Cbox Cdep : ℕ) (Cprob : ℝ) :
    0 < crossScaleConst d Cbox Cdep Cprob := by
  rw [crossScaleConst]
  have h1 : (0 : ℝ) < (((Cbox + Cdep + 1) ^ (2 * d) * (2 * Cdep + 1) ^ d : ℕ) : ℝ) := by
    have : 0 < (Cbox + Cdep + 1) ^ (2 * d) * (2 * Cdep + 1) ^ d := by positivity
    exact_mod_cast this
  have h2 : (0 : ℝ) < max 1 Cprob := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

private theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
  simpa using h

/-- The geometric sum used to control the scale sum. -/
theorem tsum_ofReal_exp_neg_le {C : ℝ} (hC : 0 ≤ C) :
    (∑' j : ℕ, ENNReal.ofReal (C * Real.exp (-(j : ℝ)))) ≤
      ENNReal.ofReal (2 * C) := by
  have hterm : ∀ j : ℕ, ENNReal.ofReal (C * Real.exp (-(j : ℝ))) =
      ENNReal.ofReal C * ENNReal.ofReal (Real.exp (-1)) ^ j := by
    intro j
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul hC]
    congr 1
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hr : ENNReal.ofReal (Real.exp (-1)) ≤ 2⁻¹ := by
    rw [show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
      simp]
    exact ENNReal.ofReal_le_ofReal exp_neg_one_le_half
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≤ 1 - ENNReal.ofReal (Real.exp (-1)) := by
    have hle : ENNReal.ofReal (Real.exp (-1)) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (le_of_lt (Real.exp_lt_one_iff.mpr (by norm_num)))
    have : (2 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (Real.exp (-1)) ≤ 1 := by
      calc (2 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (Real.exp (-1)) ≤ 2⁻¹ + 2⁻¹ :=
            add_le_add le_rfl hr
        _ = 1 := by
            rw [ENNReal.inv_two_add_inv_two]
    exact ENNReal.le_sub_of_add_le_right (by simp) this
  have hinv : (1 - ENNReal.ofReal (Real.exp (-1)))⁻¹ ≤ 2 := by
    calc (1 - ENNReal.ofReal (Real.exp (-1)))⁻¹ ≤ ((2 : ℝ≥0∞)⁻¹)⁻¹ :=
          ENNReal.inv_le_inv.mpr hhalf
      _ = 2 := by simp
  calc ENNReal.ofReal C * (1 - ENNReal.ofReal (Real.exp (-1)))⁻¹
      ≤ ENNReal.ofReal C * 2 := mul_le_mul' le_rfl hinv
    _ = ENNReal.ofReal (2 * C) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), mul_comm]
        congr 1
        simp

/-! ## The scale sum -/

theorem crossScaleSum_le (d Cbox Cdep : ℕ) {Cprob cprob q : ℝ}
    (halpha : 3 * (d : ℝ) * Real.log 3 + 1 ≤ cprob / 2 ^ d * q) :
    crossScaleSum d Cbox Cdep Cprob cprob q ≤
      ENNReal.ofReal (2 * (crossScaleConst d Cbox Cdep Cprob *
        Real.exp (-(cprob / 2 ^ d * q)))) := by
  set alpha : ℝ := cprob / 2 ^ d * q with halphadef
  have hlog3 : (0 : ℝ) ≤ 3 * (d : ℝ) * Real.log 3 := by
    have h1 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h2 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    positivity
  have halpha0 : (0 : ℝ) ≤ alpha := by linarith
  set B : ℝ := crossScaleConst d Cbox Cdep Cprob with hB
  have hBpos : 0 < B := crossScaleConst_pos d Cbox Cdep Cprob
  have hterm : ∀ j : ℕ,
      ((((Cbox + Cdep) * 3 ^ j + 1) ^ (2 * d) : ℕ) : ℝ≥0∞) *
        cellWeight d Cdep Cprob cprob q (Sum.inl (j, (0 : Lattice d))) ≤
      ENNReal.ofReal (B * Real.exp (-alpha) * Real.exp (-(j : ℝ))) := by
    intro j
    set N₁ : ℕ := ((Cbox + Cdep) * 3 ^ j + 1) ^ (2 * d) with hN₁
    set N₂ : ℕ := (2 * (Cdep * 3 ^ j) + 1) ^ d with hN₂
    set t : ℝ := (3 : ℝ) ^ ((3 : ℝ) * j / 2) with ht
    have hMax : (0 : ℝ) ≤ max 1 Cprob := le_trans zero_le_one (le_max_left _ _)
    have harg : -(cprob / 2 ^ d) * q * t = -alpha * t := by rw [halphadef]; ring
    have hcell : cellWeight d Cdep Cprob cprob q (Sum.inl (j, (0 : Lattice d))) =
        ENNReal.ofReal ((N₂ : ℝ) * max 1 Cprob * Real.exp (-alpha * t)) := by
      rw [← harg]
      rfl
    rw [hcell, ← ENNReal.ofReal_natCast N₁,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg N₁)]
    refine ENNReal.ofReal_le_ofReal ?_
    -- the entropy of the two influence-box counts
    have hcount : (N₁ : ℝ) * (N₂ : ℝ) ≤
        (((Cbox + Cdep + 1) ^ (2 * d) * (2 * Cdep + 1) ^ d : ℕ) : ℝ) *
          ((3 : ℝ) ^ (3 * d * j : ℕ)) := by
      have h3 : (1 : ℕ) ≤ 3 ^ j := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have h1 : N₁ ≤ (Cbox + Cdep + 1) ^ (2 * d) * (3 ^ j) ^ (2 * d) := by
        rw [hN₁, ← mul_pow]
        refine Nat.pow_le_pow_left ?_ _
        nlinarith
      have h2 : N₂ ≤ (2 * Cdep + 1) ^ d * (3 ^ j) ^ d := by
        rw [hN₂, ← mul_pow]
        refine Nat.pow_le_pow_left ?_ _
        nlinarith
      have hnat : N₁ * N₂ ≤
          ((Cbox + Cdep + 1) ^ (2 * d) * (2 * Cdep + 1) ^ d) * 3 ^ (3 * d * j) := by
        calc N₁ * N₂ ≤ ((Cbox + Cdep + 1) ^ (2 * d) * (3 ^ j) ^ (2 * d)) *
              ((2 * Cdep + 1) ^ d * (3 ^ j) ^ d) := Nat.mul_le_mul h1 h2
          _ = ((Cbox + Cdep + 1) ^ (2 * d) * (2 * Cdep + 1) ^ d) *
              ((3 ^ j) ^ (2 * d) * (3 ^ j) ^ d) := by ring
          _ = ((Cbox + Cdep + 1) ^ (2 * d) * (2 * Cdep + 1) ^ d) * 3 ^ (3 * d * j) := by
              have hpw : ((3 : ℕ) ^ j) ^ (2 * d) * ((3 : ℕ) ^ j) ^ d = 3 ^ (3 * d * j) := by
                rw [← pow_mul, ← pow_mul, ← pow_add]
                congr 1
                ring
              rw [← hpw]
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this ⊢
      linarith
    -- the exponential beats it
    have hexp : Real.exp (-alpha * t) ≤ Real.exp (-alpha * (1 + (j : ℝ))) := by
      refine Real.exp_le_exp.mpr ?_
      have := one_add_le_three_rpow j
      rw [← ht] at this
      nlinarith [this, halpha0]
    have hpow : ((3 : ℝ) ^ (3 * d * j : ℕ)) =
        Real.exp ((3 * (d : ℝ) * Real.log 3) * (j : ℝ)) := by
      rw [← Real.rpow_natCast (3 : ℝ) (3 * d * j),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      congr 1
      push_cast
      ring
    have hfinal : Real.exp ((3 * (d : ℝ) * Real.log 3) * (j : ℝ)) *
        Real.exp (-alpha * (1 + (j : ℝ))) ≤ Real.exp (-alpha) * Real.exp (-(j : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      have hle0 : 3 * (d : ℝ) * Real.log 3 + 1 - alpha ≤ 0 := by linarith
      have hkey : (j : ℝ) * (3 * (d : ℝ) * Real.log 3 + 1 - alpha) ≤ (j : ℝ) * 0 :=
        mul_le_mul_of_nonneg_left hle0 hj
      rw [mul_zero] at hkey
      nlinarith [hkey]
    have hN₁0 : (0 : ℝ) ≤ (N₁ : ℝ) := Nat.cast_nonneg _
    have hN₂0 : (0 : ℝ) ≤ (N₂ : ℝ) := Nat.cast_nonneg _
    have hexp0 : (0 : ℝ) < Real.exp (-alpha * t) := Real.exp_pos _
    calc (N₁ : ℝ) * ((N₂ : ℝ) * max 1 Cprob * Real.exp (-alpha * t))
        = ((N₁ : ℝ) * (N₂ : ℝ)) * max 1 Cprob * Real.exp (-alpha * t) := by ring
      _ ≤ ((((Cbox + Cdep + 1) ^ (2 * d) * (2 * Cdep + 1) ^ d : ℕ) : ℝ) *
            ((3 : ℝ) ^ (3 * d * j : ℕ))) * max 1 Cprob *
            Real.exp (-alpha * (1 + (j : ℝ))) := by
          have hpos : (0 : ℝ) ≤ (N₁ : ℝ) * (N₂ : ℝ) * max 1 Cprob := by
            have := mul_nonneg hN₁0 hN₂0
            exact mul_nonneg this hMax
          have step1 : (N₁ : ℝ) * (N₂ : ℝ) * max 1 Cprob ≤
              ((((Cbox + Cdep + 1) ^ (2 * d) * (2 * Cdep + 1) ^ d : ℕ) : ℝ) *
                ((3 : ℝ) ^ (3 * d * j : ℕ))) * max 1 Cprob :=
            mul_le_mul_of_nonneg_right hcount hMax
          calc (N₁ : ℝ) * (N₂ : ℝ) * max 1 Cprob * Real.exp (-alpha * t)
              ≤ (N₁ : ℝ) * (N₂ : ℝ) * max 1 Cprob *
                  Real.exp (-alpha * (1 + (j : ℝ))) :=
                mul_le_mul_of_nonneg_left hexp hpos
            _ ≤ ((((Cbox + Cdep + 1) ^ (2 * d) * (2 * Cdep + 1) ^ d : ℕ) : ℝ) *
                  ((3 : ℝ) ^ (3 * d * j : ℕ))) * max 1 Cprob *
                  Real.exp (-alpha * (1 + (j : ℝ))) :=
                mul_le_mul_of_nonneg_right step1 (Real.exp_pos _).le
      _ = B * (Real.exp ((3 * (d : ℝ) * Real.log 3) * (j : ℝ)) *
            Real.exp (-alpha * (1 + (j : ℝ)))) := by
          rw [hB, crossScaleConst, hpow]; ring
      _ ≤ B * (Real.exp (-alpha) * Real.exp (-(j : ℝ))) :=
          mul_le_mul_of_nonneg_left hfinal hBpos.le
      _ = B * Real.exp (-alpha) * Real.exp (-(j : ℝ)) := by ring
  calc crossScaleSum d Cbox Cdep Cprob cprob q
      ≤ ∑' j : ℕ, ENNReal.ofReal (B * Real.exp (-alpha) * Real.exp (-(j : ℝ))) :=
        ENNReal.tsum_le_tsum hterm
    _ ≤ ENNReal.ofReal (2 * (B * Real.exp (-alpha))) :=
        tsum_ofReal_exp_neg_le (by positivity)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
