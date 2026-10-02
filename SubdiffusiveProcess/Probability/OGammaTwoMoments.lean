import SubdiffusiveProcess.Probability.OGammaTwoControl

/-! Layer-cake evaluation of the moments of a two-sided Gaussian-tail variable. -/
open MeasureTheory
noncomputable section
namespace SubdiffusiveProcess.Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma gaussian_tail_le {Y : Ω → ℝ}
    (hi : Integrable (fun ω => Real.exp (Y ω ^ (2 : ℕ))) μ)
    (hb : ∫ ω, Real.exp (Y ω ^ (2 : ℕ)) ∂μ ≤ 4) {r : ℝ} (hr : 0 < r) :
    μ {ω | r < Y ω} ≤ ENNReal.ofReal (4 * Real.exp (-r ^ (2 : ℕ))) := by
  have hs : {ω | r < Y ω} ⊆ {ω | Real.exp (r ^ (2 : ℕ)) ≤ Real.exp (Y ω ^ (2 : ℕ))} := by
    intro ω hω
    exact Real.exp_le_exp.mpr (pow_le_pow_left₀ hr.le hω.le 2)
  have hm := measureReal_mono hs (measure_ne_top μ _)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos (Y ω ^ (2 : ℕ))).le) hi
    (Real.exp (r ^ (2 : ℕ)))
  have ht : μ.real {ω | r < Y ω} ≤ 4 / Real.exp (r ^ (2 : ℕ)) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    calc
      μ.real {ω | r < Y ω} * Real.exp (r ^ (2 : ℕ))
        ≤ Real.exp (r ^ (2 : ℕ)) * μ.real {ω | Real.exp (r ^ (2 : ℕ)) ≤ Real.exp (Y ω ^ (2 : ℕ))} := by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
      _ ≤ 4 := hmark.trans hb
  have heq : μ {ω | r < Y ω} = ENNReal.ofReal (μ.real {ω | r < Y ω}) := by
    simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ _)]
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  simpa only [div_eq_mul_inv, ← Real.exp_neg] using ht

lemma lintegral_rpow_le_gamma_of_gaussian_control {Y : Ω → ℝ}
    (hY : ∀ ω, 0 ≤ Y ω) (hm : AEMeasurable Y μ)
    (hi : Integrable (fun ω => Real.exp (Y ω ^ (2 : ℕ))) μ)
    (hb : ∫ ω, Real.exp (Y ω ^ (2 : ℕ)) ∂μ ≤ 4) {k : ℝ} (hk : 0 < k) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ k) ∂μ ≤ ENNReal.ofReal (4 * Real.Gamma (k / 2 + 1)) := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ (Filter.Eventually.of_forall hY) hm hk]
  have hd : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)),
      μ {ω | r < Y ω} * ENNReal.ofReal (r ^ (k - 1)) ≤
        ENNReal.ofReal (4 * (r ^ (k - 1) * Real.exp (-r ^ (2 : ℝ)))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    calc
      _ ≤ ENNReal.ofReal (4 * Real.exp (-r ^ (2 : ℕ))) * ENNReal.ofReal (r ^ (k - 1)) :=
        mul_le_mul_left (gaussian_tail_le hi hb hr) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_two]
        congr 1
        ring
  have hint : IntegrableOn (fun r : ℝ => 4 * (r ^ (k - 1) * Real.exp (-r ^ (2 : ℝ))))
      (Set.Ioi 0) := by
    simpa only [neg_mul, one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < k - 1)
        (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 1)).const_mul (4 : ℝ)
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun r : ℝ => 4 * (r ^ (k - 1) * Real.exp (-r ^ (2 : ℝ)))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le)
  calc
    _ ≤ ENNReal.ofReal k * ∫⁻ r in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (4 * (r ^ (k - 1) * Real.exp (-r ^ (2 : ℝ)))) :=
      mul_le_mul_right (lintegral_mono_ae hd) _
    _ = ENNReal.ofReal (k * (4 * ((1 / 2) * Real.Gamma (k / 2)))) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint hn, integral_const_mul,
        integral_rpow_mul_exp_neg_rpow (by norm_num : (0 : ℝ) < 2) (by linarith : -1 < k - 1)]
      simp only [sub_add_cancel]
      rw [← ENNReal.ofReal_mul hk.le]
    _ = _ := by
      rw [Real.Gamma_add_one (by positivity : k / 2 ≠ 0)]
      congr 1
      ring

lemma lintegral_abs_rpow_le_ogamma_two {σ : ℝ} (hσ : 0 < σ) {X : Ω → ℝ}
    (hp : SubdiffusiveProcess.OGammaLE μ 2 σ X) (hn : SubdiffusiveProcess.OGammaLE μ 2 σ (fun ω => -X ω))
    {k : ℝ} (hk : 0 < k) :
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ k) ∂μ ≤
      ENNReal.ofReal (4 * σ ^ k * Real.Gamma (k / 2 + 1)) := by
  let Y : Ω → ℝ := fun ω => σ⁻¹ * |X ω|
  have hY : ∀ ω, 0 ≤ Y ω := fun ω => mul_nonneg (inv_nonneg.mpr hσ.le) (abs_nonneg _)
  have hm : AEMeasurable Y μ := (aemeasurable_abs_of_ogamma_two hσ hp hn).const_mul σ⁻¹
  have hb := lintegral_rpow_le_gamma_of_gaussian_control hY hm
    (integrable_exp_abs_normalized_sq hp hn) (integral_exp_abs_normalized_sq_le hp hn) hk
  have heq : ∀ ω, |X ω| ^ k = σ ^ k * Y ω ^ k := by
    intro ω
    rw [← Real.mul_rpow hσ.le (hY ω)]
    congr 1
    dsimp [Y]
    field_simp
  simp_rw [heq, ENNReal.ofReal_mul (Real.rpow_nonneg hσ.le k)]
  rw [lintegral_const_mul'' _ ((hm.pow aemeasurable_const).ennreal_ofReal)]
  calc
    _ ≤ ENNReal.ofReal (σ ^ k) * ENNReal.ofReal (4 * Real.Gamma (k / 2 + 1)) :=
      mul_le_mul_right hb _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hσ.le k)]
      congr 1
      ring

end SubdiffusiveProcess.Probability
