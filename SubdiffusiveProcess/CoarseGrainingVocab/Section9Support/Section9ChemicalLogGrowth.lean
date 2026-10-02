import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalLayeredBudget

/-!
# A polylogarithm is eventually dominated by the identity

For every real constant `C` and every exponent `n : ℕ` there is a threshold `L₀ ≥ 1` beyond
which `C * Real.log L ^ n ≤ L`.  The proof is elementary and filter-free: the bound
`log t ≤ k * t ^ (1 / k)` of `Section9ChemicalLayeredBudget.log_le_mul_rpow`, used with
`k = 2 n + 2`, turns `log L ^ n` into a constant multiple of `L ^ (n / (2 n + 2))`, whose
exponent is at most `1 / 2`.  So the polylogarithm is bounded by a fixed multiple of `√L`, and
every `L` past the square of that multiple is large enough.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

noncomputable section

/-- The polylogarithmic factor `log t ^ n` is bounded by `(2 n + 2) ^ n * √t` for `t ≥ 1`:
the rate `log t ≤ k * t ^ (1 / k)` with `k = 2 n + 2` costs an exponent `n / (2 n + 2) ≤ 1 / 2`. -/
private theorem log_pow_le_mul_sqrt (n : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    Real.log t ^ n ≤ (2 * (n : ℝ) + 2) ^ n * Real.sqrt t := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h0t : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hk : (1 : ℝ) ≤ 2 * (n : ℝ) + 2 := by linarith
  have hk0 : (0 : ℝ) < 2 * (n : ℝ) + 2 := lt_of_lt_of_le zero_lt_one hk
  have hlognn : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hlog : Real.log t ≤ (2 * (n : ℝ) + 2) * t ^ (1 / (2 * (n : ℝ) + 2)) :=
    log_le_mul_rpow hk ht
  have hexp : (1 / (2 * (n : ℝ) + 2)) * (n : ℝ) ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hk0 (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hroot : (t ^ (1 / (2 * (n : ℝ) + 2))) ^ n ≤ Real.sqrt t := by
    rw [← Real.rpow_natCast (t ^ (1 / (2 * (n : ℝ) + 2))) n, ← Real.rpow_mul h0t,
      Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le ht hexp
  calc Real.log t ^ n
      ≤ ((2 * (n : ℝ) + 2) * t ^ (1 / (2 * (n : ℝ) + 2))) ^ n :=
        pow_le_pow_left₀ hlognn hlog n
    _ = (2 * (n : ℝ) + 2) ^ n * (t ^ (1 / (2 * (n : ℝ) + 2))) ^ n := mul_pow _ _ _
    _ ≤ (2 * (n : ℝ) + 2) ^ n * Real.sqrt t :=
        mul_le_mul_of_nonneg_left hroot (pow_nonneg hk0.le n)

/-- **Polylogarithmic growth is eventually linear.**  For every constant `C` and every power
`n` there is a threshold `L₀ ≥ 1` past which `C * Real.log L ^ n ≤ L`.  No positivity of `C`
and no lower bound on `n` are needed. -/
theorem exists_log_pow_threshold (C : ℝ) (n : ℕ) :
    ∃ L0 : ℕ, 1 ≤ L0 ∧ ∀ L : ℕ, L0 ≤ L → C * Real.log (L : ℝ) ^ n ≤ (L : ℝ) := by
  set C' : ℝ := max C 1 with hC'def
  have hC' : (1 : ℝ) ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hk : (1 : ℝ) ≤ 2 * (n : ℝ) + 2 := by linarith
  set A : ℝ := C' * (2 * (n : ℝ) + 2) ^ n with hAdef
  have hA0 : (0 : ℝ) ≤ A := by
    have : (0 : ℝ) ≤ (2 * (n : ℝ) + 2) ^ n := pow_nonneg (by linarith) n
    exact mul_nonneg (le_trans zero_le_one hC') this
  refine ⟨max 1 ⌈A ^ 2⌉₊, le_max_left _ _, ?_⟩
  intro L hL
  have hL1N : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1N
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := le_trans zero_le_one hL1
  -- the polylogarithm is bounded by `A * √L`
  have hlognn : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  have hpow : Real.log (L : ℝ) ^ n ≤ (2 * (n : ℝ) + 2) ^ n * Real.sqrt (L : ℝ) :=
    log_pow_le_mul_sqrt n hL1
  have hstep : C' * Real.log (L : ℝ) ^ n ≤ A * Real.sqrt (L : ℝ) := by
    have := mul_le_mul_of_nonneg_left hpow (le_trans zero_le_one hC')
    rw [hAdef, mul_assoc]
    exact this
  -- `A ≤ √L`, since `L` is past `⌈A ^ 2⌉₊`
  have hsq : A ^ 2 ≤ (L : ℝ) := by
    have h1 : A ^ 2 ≤ (⌈A ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈A ^ 2⌉₊ : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast le_trans (le_max_right 1 ⌈A ^ 2⌉₊) hL
    exact le_trans h1 h2
  have hAsqrt : A ≤ Real.sqrt (L : ℝ) := (Real.le_sqrt hA0 hL0).mpr hsq
  have hfinal : A * Real.sqrt (L : ℝ) ≤ (L : ℝ) := by
    have hs : (0 : ℝ) ≤ Real.sqrt (L : ℝ) := Real.sqrt_nonneg _
    calc A * Real.sqrt (L : ℝ) ≤ Real.sqrt (L : ℝ) * Real.sqrt (L : ℝ) :=
          mul_le_mul_of_nonneg_right hAsqrt hs
      _ = (L : ℝ) := Real.mul_self_sqrt hL0
  have hC'step : C * Real.log (L : ℝ) ^ n ≤ C' * Real.log (L : ℝ) ^ n :=
    mul_le_mul_of_nonneg_right hCC' (pow_nonneg hlognn n)
  exact le_trans hC'step (le_trans hstep hfinal)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
