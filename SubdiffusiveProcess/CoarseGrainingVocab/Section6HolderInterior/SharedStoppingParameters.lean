import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.GateParameters

/-!
# One admissible stopping pair, and the model conditions it forces

The three frozen interior rows must run at a **single** stopping scale, hence at
a single pair `(C₁, C₂)`.  This module supplies the two arithmetic facts that
make such a pair admissible.

* `holderStopping_conditions_of_coupled` — with `2 ≤ C₁ ≤ C₂` the three
  *model-free* stopping conditions

  ```text
    0 ≤ lambda ,   lambda < 1 ,   epsilon ^ 8 ≤ lambda
  ```

  are theorems (`epsilon^8 ≤ lambda` reads `C₁(1-alpha)^3 ≤ C₂^8`).  This is the
  coupling already produced by row 2 and now shared by all three rows.

* `holderStopping_model_conditions` — the two conditions that genuinely couple
  the disorder strength `delta` to the manuscript's `alpha`-window,
  `epsilon ∈ Icc (s⁻¹ delta²) 1` and `delta² ≤ lambda`, together with
  `64 delta² ≤ s` and `alpha ∈ Icc (1/2) 1`, hold as soon as the frozen constant
  `C` is large relative to `(C₁, C₂)`: `C ≥ 46`, `C ≥ C₁`, `C ≥ 1024 C₂²`.

  The mechanism is the window itself: `alpha ≤ 1 - C delta |log delta|^{1/2}`
  gives `1 - alpha ≥ C delta`, since `delta ≤ 1/46` forces `|log delta| ≥ 1`.
  Note `0 < delta` is part of the model (`ShellLawPrefix.delta_pos`), so no
  degenerate `delta = 0` endpoint arises.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- `lambda = C₁⁻¹(1-alpha)` is nonnegative below `alpha = 1`. -/
theorem holderStoppingLambda_nonneg {C1 alpha : ℝ} (hC1 : 0 < C1)
    (halpha : alpha ≤ 1) :
    0 ≤ Section6Stopping.holderStoppingLambda C1 alpha := by
  rw [Section6Stopping.holderStoppingLambda]
  exact mul_nonneg (inv_nonneg.mpr hC1.le) (by linarith)

/-- `lambda ≤ 1/4` on the manuscript window once `C₁ ≥ 2`; this is what keeps
row 2's two selection windows inside the domain. -/
theorem holderStoppingLambda_le_quarter {C1 alpha : ℝ} (hC1 : 2 ≤ C1)
    (halpha : alpha ∈ Set.Icc (1 / 2 : ℝ) 1) :
    Section6Stopping.holderStoppingLambda C1 alpha ≤ 1 / 4 := by
  rw [Section6Stopping.holderStoppingLambda]
  have hinv : C1⁻¹ ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) hC1
  have hinv0 : (0 : ℝ) ≤ C1⁻¹ := by positivity
  have ha : (0 : ℝ) ≤ 1 - alpha := by linarith [halpha.2]
  have ha2 : (1 : ℝ) - alpha ≤ 1 / 2 := by linarith [halpha.1]
  nlinarith only [hinv, hinv0, ha, ha2]

/-- **The three model-free stopping conditions, from the coupling
`2 ≤ C₁ ≤ C₂`.** -/
theorem holderStopping_conditions_of_coupled {C1 C2 alpha : ℝ} (hC1 : 2 ≤ C1)
    (hC1C2 : C1 ≤ C2) (halpha : alpha ∈ Set.Icc (1 / 2 : ℝ) 1) :
    0 ≤ Section6Stopping.holderStoppingLambda C1 alpha ∧
      Section6Stopping.holderStoppingLambda C1 alpha < 1 ∧
      Section6Stopping.holderStoppingEpsilon C2 alpha ^ 8 ≤
        Section6Stopping.holderStoppingLambda C1 alpha := by
  have hC1pos : (0 : ℝ) < C1 := by linarith
  have hC2 : (1 : ℝ) ≤ C2 := by linarith
  have hC2pos : (0 : ℝ) < C2 := by linarith
  have ha0 : (0 : ℝ) ≤ 1 - alpha := by linarith [halpha.2]
  have hlam0 := holderStoppingLambda_nonneg hC1pos halpha.2
  have hquarter := holderStoppingLambda_le_quarter hC1 halpha
  refine ⟨hlam0, by linarith, ?_⟩
  rw [Section6Stopping.holderStoppingLambda, Section6Stopping.holderStoppingEpsilon]
  have hsq : Real.sqrt (1 - alpha) ^ 8 = (1 - alpha) ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt ha0]
  have hexp : (C2⁻¹ * Real.sqrt (1 - alpha)) ^ 8 =
      (C2⁻¹) ^ 8 * (1 - alpha) ^ 4 := by rw [mul_pow, hsq]
  rw [hexp]
  have hinvC2 : (0 : ℝ) ≤ C2⁻¹ := by positivity
  have hinvC2one : C2⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; linarith
  have h8 : (C2⁻¹) ^ 8 ≤ C2⁻¹ := by
    calc (C2⁻¹) ^ 8 ≤ (C2⁻¹) ^ 1 :=
          pow_le_pow_of_le_one hinvC2 hinvC2one (by norm_num)
      _ = C2⁻¹ := pow_one _
  have hmono : C2⁻¹ ≤ C1⁻¹ := inv_anti₀ hC1pos hC1C2
  have h1 : (C2⁻¹) ^ 8 ≤ C1⁻¹ := by linarith
  have ha1 : (1 : ℝ) - alpha ≤ 1 := by linarith [halpha.1]
  have h2 : (1 - alpha) ^ 4 ≤ (1 - alpha) := by
    calc (1 - alpha) ^ 4 ≤ (1 - alpha) ^ 1 :=
          pow_le_pow_of_le_one ha0 ha1 (by norm_num)
      _ = 1 - alpha := pow_one _
  have hpow0 : (0 : ℝ) ≤ (1 - alpha) ^ 4 := by positivity
  have hinvC10 : (0 : ℝ) ≤ C1⁻¹ := by positivity
  calc (C2⁻¹) ^ 8 * (1 - alpha) ^ 4 ≤ C1⁻¹ * (1 - alpha) ^ 4 :=
        mul_le_mul_of_nonneg_right h1 hpow0
    _ ≤ C1⁻¹ * (1 - alpha) := mul_le_mul_of_nonneg_left h2 hinvC10

/-- **`|log delta| ≥ 1` on the manuscript's smallness range.** -/
theorem one_le_abs_log_of_le {x : ℝ} (hx : 0 < x) (hle : x ≤ 1 / 46) :
    (1 : ℝ) ≤ |Real.log x| := by
  have hlog : Real.log x ≤ Real.log (1 / 46) := Real.log_le_log hx hle
  have hnum : Real.log (1 / 46) ≤ -1 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub,
      neg_le_neg_iff]
    have h : Real.exp 1 ≤ 46 := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at this
  have hneg : Real.log x ≤ -1 := le_trans hlog hnum
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **The four model-side stopping conditions.**  They follow from the frozen
smallness `delta ≤ C⁻¹` and the manuscript `alpha`-window once `C` is large
relative to the stopping pair. -/
theorem holderStopping_model_conditions
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {C C1 C2 alpha : ℝ}
    (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) (hC46 : 46 ≤ C) (hCC1 : C1 ≤ C)
    (hCC2 : 1024 * C2 ^ 2 ≤ C) (hdelta : M.delta ≤ C⁻¹)
    (halpha : alpha ∈ Set.Icc (1 / 2 : ℝ)
      (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ))) :
    64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS ∧
      alpha ∈ Set.Icc (1 / 2 : ℝ) 1 ∧
      Section6Stopping.holderStoppingEpsilon C2 alpha ∈
        Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 ∧
      M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha := by
  have hd0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hCpos : (0 : ℝ) < C := by linarith
  have hCinv : C⁻¹ ≤ 1 / 46 := by
    rw [show (1 / 46 : ℝ) = (46 : ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) hC46
  have hd46 : M.delta ≤ 1 / 46 := le_trans hdelta hCinv
  have hd1 : M.delta ≤ 1 := by linarith
  -- the root factor is at least one
  have hlog1 : (1 : ℝ) ≤ |Real.log M.delta| := one_le_abs_log_of_le hd0 hd46
  have hroot1 : (1 : ℝ) ≤ |Real.log M.delta| ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow hlog1 (by norm_num)
  have hCd0 : (0 : ℝ) ≤ C * M.delta := by positivity
  -- the window's lower bound on `1 - alpha`
  have hbeta : C * M.delta ≤ 1 - alpha := by
    have h1 : C * M.delta * 1 ≤ C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hroot1 hCd0
    have h2 := halpha.2
    linarith
  have halpha1 : alpha ≤ 1 := by nlinarith only [hbeta, hCd0]
  refine ⟨?_, ⟨halpha.1, halpha1⟩, ⟨?_, ?_⟩, ?_⟩
  · -- `64 delta^2 ≤ 1/32`
    rw [Section6Stopping.holderStoppingS]
    nlinarith only [hd0, hd46]
  · -- `32 delta^2 ≤ epsilon`
    rw [Section6Stopping.holderStoppingS, Section6Stopping.holderStoppingEpsilon]
    have hC2pos : (0 : ℝ) < C2 := by linarith
    have hd4 : M.delta ^ 4 ≤ M.delta := by
      have := pow_le_pow_of_le_one hd0.le hd1 (show 1 ≤ 4 by norm_num)
      simpa using this
    have hsqbound : (32 * C2 * M.delta ^ 2) ^ 2 ≤ 1 - alpha := by
      have hrw : (32 * C2 * M.delta ^ 2) ^ 2 = 1024 * C2 ^ 2 * M.delta ^ 4 := by
        ring
      rw [hrw]
      calc 1024 * C2 ^ 2 * M.delta ^ 4 ≤ C * M.delta ^ 4 :=
            mul_le_mul_of_nonneg_right hCC2 (by positivity)
        _ ≤ C * M.delta := mul_le_mul_of_nonneg_left hd4 hCpos.le
        _ ≤ 1 - alpha := hbeta
    have hnn : (0 : ℝ) ≤ 32 * C2 * M.delta ^ 2 := by positivity
    have hstep : 32 * C2 * M.delta ^ 2 ≤ Real.sqrt (1 - alpha) := by
      have := Real.sqrt_le_sqrt hsqbound
      rwa [Real.sqrt_sq hnn] at this
    have hfinal : 32 * M.delta ^ 2 ≤ C2⁻¹ * Real.sqrt (1 - alpha) := by
      have h := mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hC2pos.le)
      have heq : C2⁻¹ * (32 * C2 * M.delta ^ 2) = 32 * M.delta ^ 2 := by
        field_simp
      rw [heq] at h
      exact h
    rw [show ((1 : ℝ) / 32)⁻¹ = 32 by norm_num]
    exact hfinal
  · exact holderStoppingEpsilon_le_one hC2 halpha.1
  · -- `delta^2 ≤ C1⁻¹ (1 - alpha)`
    rw [Section6Stopping.holderStoppingLambda]
    have hC1pos : (0 : ℝ) < C1 := by linarith
    have h1 : C1 * M.delta ≤ C := by
      calc C1 * M.delta ≤ C1 * 1 :=
            mul_le_mul_of_nonneg_left hd1 (by linarith)
        _ = C1 := mul_one _
        _ ≤ C := hCC1
    have hstep : C1 * M.delta ^ 2 ≤ 1 - alpha := by
      calc C1 * M.delta ^ 2 = C1 * M.delta * M.delta := by ring
        _ ≤ C * M.delta := mul_le_mul_of_nonneg_right h1 hd0.le
        _ ≤ 1 - alpha := hbeta
    rw [inv_mul_eq_div, le_div_iff₀ hC1pos]
    calc M.delta ^ 2 * C1 = C1 * M.delta ^ 2 := by ring
      _ ≤ 1 - alpha := hstep

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
