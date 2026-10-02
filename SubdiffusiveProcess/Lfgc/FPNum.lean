import Mathlib

/-!
# Numerics of the pad-test tails

* The field-test threshold `3^{sj/8}/(2j+1)` and the tail-layer threshold
  `(3/2)^l (1 + sj/8)/12` grow at least linearly in the window index.
* A sub-Gaussian tail with a linearly growing threshold beats any geometric prefactor and any
  exponential rate once the scale `σ` is small.
* The product-window moment bound decays at any exponential rate once the moment order `Λ` is
  large and `Λσ ≤ 1`.
-/

namespace SubdiffusiveProcess.Lfgc
/-- The field-test threshold grows linearly. -/
theorem fThreshold_ge {s : ℝ} (hs : 0 < s) (j : ℕ) :
    Real.exp (-(s * Real.log 3 / 8)) * (s * Real.log 3 / 8) ^ 2 / 4 * ((j : ℝ) + 1) ≤
      (3 : ℝ) ^ (s * (j : ℝ) / 8) / (2 * j + 1) := by
  set a := s * Real.log 3 / 8 with ha
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha0 : 0 < a := by positivity
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h3 : (3 : ℝ) ^ (s * (j : ℝ) / 8) = Real.exp (a * ((j : ℝ) + 1)) * Real.exp (-a) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    rw [ha]
    ring
  have hexp : (a * ((j : ℝ) + 1)) ^ 2 / 2 ≤ Real.exp (a * ((j : ℝ) + 1)) := by
    have := Real.pow_div_factorial_le_exp (a * ((j : ℝ) + 1)) (by positivity) 2
    simpa using this
  have hden : (0 : ℝ) < 2 * j + 1 := by positivity
  rw [le_div_iff₀ hden, h3]
  have hea : 0 < Real.exp (-a) := Real.exp_pos _
  have h2 : (2 * (j : ℝ) + 1) ≤ 2 * ((j : ℝ) + 1) := by linarith
  have hk : 0 ≤ Real.exp (-a) * a ^ 2 / 4 * ((j : ℝ) + 1) := by positivity
  calc Real.exp (-a) * a ^ 2 / 4 * ((j : ℝ) + 1) * (2 * j + 1)
      ≤ Real.exp (-a) * a ^ 2 / 4 * ((j : ℝ) + 1) * (2 * ((j : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h2 hk
    _ = Real.exp (-a) * ((a * ((j : ℝ) + 1)) ^ 2 / 2) := by ring
    _ ≤ Real.exp (-a) * Real.exp (a * ((j : ℝ) + 1)) := mul_le_mul_of_nonneg_left hexp hea.le
    _ = Real.exp (a * ((j : ℝ) + 1)) * Real.exp (-a) := by ring

/-- The tail-layer threshold grows linearly in `j + l + 1`. -/
theorem bThreshold_ge {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (j l : ℕ) :
    s / 96 * ((j : ℝ) + l + 1) ≤ (3 / 2 : ℝ) ^ l * (1 + s * (j : ℝ) / 8) / 12 := by
  have hb : 1 + (l : ℝ) / 2 ≤ (3 / 2 : ℝ) ^ l := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / 2 by norm_num) l
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] at this
    linarith
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have h1 : (0 : ℝ) ≤ 1 + s * (j : ℝ) / 8 := by positivity
  have h2 : (1 + (l : ℝ) / 2) * (1 + s * (j : ℝ) / 8) ≤ (3 / 2 : ℝ) ^ l * (1 + s * (j : ℝ) / 8) :=
    mul_le_mul_of_nonneg_right hb h1
  have h3 : s / 8 * ((j : ℝ) + l + 1) ≤ (1 + (l : ℝ) / 2) * (1 + s * (j : ℝ) / 8) := by
    nlinarith [mul_nonneg hl hj, mul_nonneg (mul_nonneg hl hj) hs.le]
  linarith

/-- A sub-Gaussian tail with threshold at least `c h` beats a geometric prefactor. -/
theorem gauss_tail_le {c σ K Q R : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hK : 1 ≤ K) (hQ : 1 ≤ Q) (hsmall : Real.log (6 * K) + Real.log Q + R ≤ (c / σ) ^ 2)
    {h : ℕ} (hh : 1 ≤ h) {t : ℝ} (ht : c * h ≤ t) :
    K * Q ^ h * Real.exp (-(t / σ) ^ 2) ≤ Real.exp (-R * h) / 6 := by
  have hhr : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h0 : 0 ≤ c * h := by positivity
  have htσ : c * h / σ ≤ t / σ := div_le_div_of_nonneg_right ht hσ.le
  have hsq : (c / σ) ^ 2 * h ≤ (t / σ) ^ 2 := by
    have h1 : (c * h / σ) ^ 2 ≤ (t / σ) ^ 2 := pow_le_pow_left₀ (by positivity) htσ 2
    have h2 : (c / σ) ^ 2 * h ≤ (c * h / σ) ^ 2 := by
      rw [show c * h / σ = c / σ * h by ring, mul_pow]
      have : (h : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
    linarith
  have hK0 : 0 < K := by linarith
  have hQ0 : 0 < Q := by linarith
  have hl6 : 0 ≤ Real.log (6 * K) := Real.log_nonneg (by linarith)
  have hlQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  -- `K Q^h e^{-(t/σ)²} ≤ exp(log K + h log Q - (log(6K) + log Q + R) h)`
  have hKQ : K * Q ^ h = Real.exp (Real.log K + h * Real.log Q) := by
    rw [Real.exp_add, Real.exp_log hK0, ← Real.log_pow, Real.exp_log (pow_pos hQ0 h)]
  rw [hKQ, ← Real.exp_add, le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
  have h6 : (6 : ℝ) = Real.exp (Real.log 6) := (Real.exp_log (by norm_num)).symm
  rw [h6, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hlog6K : Real.log (6 * K) = Real.log 6 + Real.log K := Real.log_mul (by norm_num) hK0.ne'
  have hl6' : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hA : (Real.log (6 * K) + Real.log Q + R) * h ≤ (t / σ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hsmall (by positivity : (0 : ℝ) ≤ h)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hhr hl6]

/-- Choice of the moment order and the scale for the product-window tail. -/
theorem amaj_num {s R : ℝ} (hs : 0 < s) (hR : 0 < R) (ns d : ℕ) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ j : ℕ,
      6 * (ns + 1 : ℝ) * (9 : ℝ) ^ (d * (j + 1)) * (16 : ℝ) ^ (j + 1) ≤
        Real.exp (-R * ((j : ℝ) + 1)) * (6 ^ Λ * ((3 : ℝ) ^ (s * (j : ℝ) / 8)) ^ Λ) := by
  set q : ℝ := (9 : ℝ) ^ d * 16 * Real.exp R with hq
  have hq1 : 1 ≤ q := by
    have h9 : (1 : ℝ) ≤ (9 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have he : (1 : ℝ) ≤ Real.exp R := Real.one_le_exp hR.le
    have : (1 : ℝ) ≤ (9 : ℝ) ^ d * 16 := by nlinarith
    nlinarith
  have hq0 : 0 < q := by linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  set Λ : ℝ := max 1 (max (8 * Real.log q / (s * Real.log 3))
    (Real.log (6 * (ns + 1) * q) / Real.log 6)) with hΛ
  refine ⟨Λ, le_max_left _ _, fun j => ?_⟩
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one (le_max_left _ _)
  have hΛ1 : 8 * Real.log q / (s * Real.log 3) ≤ Λ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hΛ2 : Real.log (6 * (ns + 1) * q) / Real.log 6 ≤ Λ :=
    (le_max_right _ _).trans (le_max_right _ _)
  -- `3^{sΛ/8} ≥ q` and `6^Λ ≥ 6 (ns+1) q`
  have hA : q ≤ ((3 : ℝ) ^ (s / 8)) ^ Λ := by
    rw [← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
    calc q = Real.exp (Real.log q) := (Real.exp_log hq0).symm
      _ ≤ Real.exp (Real.log 3 * (s / 8 * Λ)) := by
          refine Real.exp_le_exp.mpr ?_
          have := mul_le_mul_of_nonneg_left hΛ1 (by positivity : (0 : ℝ) ≤ s * Real.log 3 / 8)
          rw [show s * Real.log 3 / 8 * (8 * Real.log q / (s * Real.log 3)) = Real.log q by
            field_simp] at this
          linarith
  have hB : 6 * (ns + 1 : ℝ) * q ≤ (6 : ℝ) ^ Λ := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    calc 6 * (ns + 1 : ℝ) * q = Real.exp (Real.log (6 * (ns + 1) * q)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (Real.log 6 * Λ) := by
          refine Real.exp_le_exp.mpr ?_
          have := mul_le_mul_of_nonneg_left hΛ2 hlog6.le
          rw [show Real.log 6 * (Real.log (6 * (ns + 1) * q) / Real.log 6) =
            Real.log (6 * (ns + 1) * q) by field_simp] at this
          exact this
  have hpow : ((3 : ℝ) ^ (s * (j : ℝ) / 8)) ^ Λ = (((3 : ℝ) ^ (s / 8)) ^ Λ) ^ j := by
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have hqj : q ^ j ≤ ((3 : ℝ) ^ (s * (j : ℝ) / 8)) ^ Λ := by
    rw [hpow]
    exact pow_le_pow_left₀ hq0.le hA j
  have hqq : q * q ^ j = (9 : ℝ) ^ (d * (j + 1)) * (16 : ℝ) ^ (j + 1) *
      Real.exp (R * ((j : ℝ) + 1)) := by
    rw [← pow_succ', hq, mul_pow, mul_pow, pow_mul, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hee : Real.exp (-R * ((j : ℝ) + 1)) * Real.exp (R * ((j : ℝ) + 1)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hlhs : 6 * (ns + 1 : ℝ) * (9 : ℝ) ^ (d * (j + 1)) * (16 : ℝ) ^ (j + 1) =
      Real.exp (-R * ((j : ℝ) + 1)) * (6 * (ns + 1 : ℝ) * q * q ^ j) := by
    rw [mul_assoc (6 * (ns + 1 : ℝ)) q, hqq]
    calc 6 * (ns + 1 : ℝ) * (9 : ℝ) ^ (d * (j + 1)) * (16 : ℝ) ^ (j + 1)
        = 6 * (ns + 1 : ℝ) * (9 : ℝ) ^ (d * (j + 1)) * (16 : ℝ) ^ (j + 1) *
          (Real.exp (-R * ((j : ℝ) + 1)) * Real.exp (R * ((j : ℝ) + 1))) := by
          rw [hee, mul_one]
      _ = _ := by ring
  rw [hlhs]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact mul_le_mul hB hqj (by positivity) (by positivity)

end SubdiffusiveProcess.Lfgc
