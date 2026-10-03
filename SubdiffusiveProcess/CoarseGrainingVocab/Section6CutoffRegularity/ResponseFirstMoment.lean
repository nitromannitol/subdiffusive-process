module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ResponseRow

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped ENNReal

noncomputable section

/-- **Direct first-moment bound on the finite-cutoff parameterized response
row**, log-free in `δ`.

Contrast with the Gamma-two route, which yields
`∫ row ≤ gammaMomentConst 2 · √(coeff·s^{-3}) · δ · √|log δ|`.  The `√|log δ|`
is absent here, which is exactly what conjunct (2) of the frozen anchor
requires. -/
theorem exists_integral_cutoffParameterizedResponseRow_le
    {d : ℕ} [NeZero d] :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ), 0 < s → s ≤ 1 →
        K * M.delta ^ 2 * |Real.log M.delta| ≤ s →
        ∀ L j : ℕ,
          ∫ omega, cutoffParameterizedResponseRow M L s j omega
              ∂M.P.toMeasure ≤
            C * s ^ (-2 : ℤ) * M.delta := by
  obtain ⟨c0, C0, _hc0, hC0, hscore⟩ :=
    exists_cutoffParameterizedResponseScore_norm_bound (d := d)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    have : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    exact_mod_cast this
  refine ⟨C0 * (1 + 4 * (d : ℝ)),
    Real.sqrt (32 * C0 * (1 + 4 * (d : ℝ)) * (2 + 4 * (d : ℝ))),
    by positivity, Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro M s hs hs1 hbudget L j
  set q : ℝ := 1 + 4 * (d : ℝ) / s with hqdef
  have hspos : (0 : ℝ) < s := hs
  have hd0 : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le zero_lt_one hd1
  have hq1 : (1 : ℝ) ≤ q := by
    rw [hqdef]
    have : 0 < 4 * (d : ℝ) / s := by positivity
    linarith
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hdim : 2 * (d : ℝ) * (s / 2)⁻¹ ≤ q := by
    rw [hqdef]
    have heq : 2 * (d : ℝ) * (s / 2)⁻¹ = 4 * (d : ℝ) / s := by
      field_simp
      ring
    rw [heq]
    linarith
  -- the budget makes the smallest admissible exponent admissible
  have hdelta0 : (0 : ℝ) < M.delta := M.shellPrefix.delta_pos
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg hdelta0 (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  have hlogpos : (0 : ℝ) < |Real.log M.delta| := abs_pos.mpr hlogNeg.ne
  have hbase : (0 : ℝ) < M.delta ^ 2 * |Real.log M.delta| := by positivity
  have hone_le : (1 : ℝ) ≤ 1 / s := by
    rw [le_div_iff₀ hspos]; linarith
  have hqs : q ≤ (1 + 4 * (d : ℝ)) / s := by
    rw [hqdef]
    have hsplit : (1 + 4 * (d : ℝ)) / s = 1 / s + 4 * (d : ℝ) / s := by ring
    rw [hsplit]
    linarith
  have hfloor : q ≤ C0⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
    have hD : (0 : ℝ) < C0 * (M.delta ^ 2 * |Real.log M.delta|) := by
      positivity
    have hrhs : C0⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ =
        1 / (C0 * (M.delta ^ 2 * |Real.log M.delta|)) := by
      field_simp
    rw [hrhs, le_div_iff₀ hD]
    have hbud' : C0 * (1 + 4 * (d : ℝ)) *
        (M.delta ^ 2 * |Real.log M.delta|) ≤ s := by
      calc C0 * (1 + 4 * (d : ℝ)) * (M.delta ^ 2 * |Real.log M.delta|)
          = C0 * (1 + 4 * (d : ℝ)) * M.delta ^ 2 * |Real.log M.delta| := by
            ring
        _ ≤ s := hbudget
    have hstep : q * (C0 * (M.delta ^ 2 * |Real.log M.delta|)) ≤
        ((1 + 4 * (d : ℝ)) / s) *
          (C0 * (M.delta ^ 2 * |Real.log M.delta|)) :=
      mul_le_mul_of_nonneg_right hqs (by positivity)
    have hfin : ((1 + 4 * (d : ℝ)) / s) *
        (C0 * (M.delta ^ 2 * |Real.log M.delta|)) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hspos]
      nlinarith [hbud']
    linarith [hstep, hfin]
  -- the landed score bound at that exponent
  set R : ℝ := 8 * C0 * ((s / 2) ^ 2)⁻¹ * q * Real.log (2 + q) * M.delta ^ 2
    with hRdef
  have hlogq : (0 : ℝ) ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
  have hR0 : (0 : ℝ) ≤ R := by
    rw [hRdef]
    have : (0 : ℝ) < ((s / 2) ^ 2)⁻¹ := by positivity
    positivity
  have hmoment : paperENNRealLpNorm M.P.toMeasure ((2 * q) / 2)
      (cutoffLocalResponseScore M L (s / 2) 1 1 j) ≤ ENNReal.ofReal R := by
    have hhalf : (2 * q) / 2 = q := by ring
    rw [hhalf]
    exact hscore M q hq1 hfloor s hs hs1 hdim L j
  obtain ⟨hint, hrpow⟩ :=
    integral_cutoffParameterizedResponseRow_rpow_le_of_score_norm
      M L hs j (p := 2 * q) (by linarith) hR0 hmoment
  -- descend to the first moment
  obtain ⟨_hint1, hfirst⟩ :=
    integral_nonneg_rpow_le_of_high_moment
      (P := M.P.toMeasure) (Y := cutoffParameterizedResponseRow M L s j)
      (p := 1) (q := 2 * q) (B := Real.sqrt R)
      (measurable_cutoffParameterizedResponseRow M L s j)
      (cutoffParameterizedResponseRow_nonneg M L s j)
      zero_lt_one (by linarith) (Real.sqrt_nonneg R) hint hrpow
  have hone : ∫ omega, cutoffParameterizedResponseRow M L s j omega
      ∂M.P.toMeasure ≤ Real.sqrt R := by
    have hfun : (fun omega =>
        cutoffParameterizedResponseRow M L s j omega ^ (1 : ℝ)) =
        fun omega => cutoffParameterizedResponseRow M L s j omega := by
      funext omega
      exact Real.rpow_one _
    rw [hfun] at hfirst
    simpa [Real.rpow_one] using hfirst
  refine hone.trans ?_
  -- the arithmetic: `√R ≤ C s^{-2} δ`
  set Cc : ℝ := Real.sqrt (32 * C0 * (1 + 4 * (d : ℝ)) * (2 + 4 * (d : ℝ)))
    with hCcdef
  have hCc0 : (0 : ℝ) ≤ Cc := Real.sqrt_nonneg _
  have hz2 : s ^ (-2 : ℤ) = (s ^ (2 : ℕ))⁻¹ := by
    rw [show (-2 : ℤ) = -(2 : ℕ) by norm_num, zpow_neg, zpow_natCast]
  have htarget0 : (0 : ℝ) ≤ Cc * s ^ (-2 : ℤ) * M.delta := by
    rw [hz2]
    have : (0 : ℝ) < (s ^ (2 : ℕ))⁻¹ := by positivity
    positivity
  have hsq : R ≤ (Cc * s ^ (-2 : ℤ) * M.delta) ^ 2 := by
    have hCcsq : Cc ^ 2 =
        32 * C0 * (1 + 4 * (d : ℝ)) * (2 + 4 * (d : ℝ)) := by
      rw [hCcdef]
      exact Real.sq_sqrt (by positivity)
    have hlogle : Real.log (2 + q) ≤ (2 + 4 * (d : ℝ)) / s := by
      have h1 : Real.log (2 + q) ≤ (2 + q) - 1 :=
        Real.log_le_sub_one_of_pos (by linarith)
      have hsplit : (2 + 4 * (d : ℝ)) / s = 1 / s + (1 + 4 * (d : ℝ)) / s := by
        ring
      rw [hsplit]
      linarith [hqs]
    have hexpand : (Cc * s ^ (-2 : ℤ) * M.delta) ^ 2 =
        32 * C0 * (1 + 4 * (d : ℝ)) * (2 + 4 * (d : ℝ)) *
          (s ^ (2 : ℕ))⁻¹ ^ 2 * M.delta ^ 2 := by
      rw [hz2, mul_pow, mul_pow, hCcsq]
    rw [hexpand, hRdef]
    have hinv : ((s / 2) ^ 2)⁻¹ = 4 * (s ^ (2 : ℕ))⁻¹ := by
      field_simp
      ring
    rw [hinv]
    have hstep : q * Real.log (2 + q) ≤
        ((1 + 4 * (d : ℝ)) / s) * ((2 + 4 * (d : ℝ)) / s) :=
      mul_le_mul hqs hlogle hlogq (by positivity)
    have hsinv : ((1 + 4 * (d : ℝ)) / s) * ((2 + 4 * (d : ℝ)) / s) =
        (1 + 4 * (d : ℝ)) * (2 + 4 * (d : ℝ)) * (s ^ (2 : ℕ))⁻¹ := by
      field_simp
    rw [hsinv] at hstep
    have hfactor : (0 : ℝ) ≤ 32 * C0 * (s ^ (2 : ℕ))⁻¹ * M.delta ^ 2 := by
      have hpos : (0 : ℝ) < (s ^ (2 : ℕ))⁻¹ := by positivity
      positivity
    calc 8 * C0 * (4 * (s ^ (2 : ℕ))⁻¹) * q * Real.log (2 + q) * M.delta ^ 2
        = (32 * C0 * (s ^ (2 : ℕ))⁻¹ * M.delta ^ 2) *
            (q * Real.log (2 + q)) := by ring
      _ ≤ (32 * C0 * (s ^ (2 : ℕ))⁻¹ * M.delta ^ 2) *
            ((1 + 4 * (d : ℝ)) * (2 + 4 * (d : ℝ)) * (s ^ (2 : ℕ))⁻¹) :=
          mul_le_mul_of_nonneg_left hstep hfactor
      _ = 32 * C0 * (1 + 4 * (d : ℝ)) * (2 + 4 * (d : ℝ)) *
            (s ^ (2 : ℕ))⁻¹ ^ 2 * M.delta ^ 2 := by ring
  calc Real.sqrt R ≤ Real.sqrt ((Cc * s ^ (-2 : ℤ) * M.delta) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Cc * s ^ (-2 : ℤ) * M.delta := Real.sqrt_sq htarget0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
