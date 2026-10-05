module

public import SubdiffusiveProcess.Probability.OGammaTwoControl
public import SubdiffusiveProcess.Probability.ExpGaussianAbsorption

@[expose] public section

/-! Exponential moments obtained by pointwise Gaussian absorption. -/
open MeasureTheory
noncomputable section
namespace SubdiffusiveProcess.Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma lintegral_le_of_gaussian_dom {σ K : ℝ} (hK : 0 ≤ K) {X F : Ω → ℝ}
    (hp : SubdiffusiveProcess.OGammaLE μ 2 σ X) (hn : SubdiffusiveProcess.OGammaLE μ 2 σ (fun ω => -X ω))
    (hd : ∀ ω, F ω ≤ K * Real.exp ((σ⁻¹ * |X ω|) ^ (2 : ℕ))) :
    ∫⁻ ω, ENNReal.ofReal (F ω) ∂μ ≤ ENNReal.ofReal (4 * K) := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (K * Real.exp ((σ⁻¹ * |X ω|) ^ (2 : ℕ))) ∂μ :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hd ω)
    _ = ENNReal.ofReal K * ∫⁻ ω, ENNReal.ofReal (Real.exp ((σ⁻¹ * |X ω|) ^ (2 : ℕ))) ∂μ := by
      simp_rw [ENNReal.ofReal_mul hK]
      rw [lintegral_const_mul'' _ (integrable_exp_abs_normalized_sq hp hn).aemeasurable.ennreal_ofReal]
    _ ≤ ENNReal.ofReal K * 4 := mul_le_mul_right (lintegral_exp_abs_normalized_sq_le hp hn) _
    _ = _ := by rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul hK, mul_comm]

lemma exp_remainder_gaussian_dom {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (x : ℝ) :
    |Real.exp (t * x) - (1 + t * x)| ≤
      (6 * (σ * t) ^ (2 : ℕ) * Real.exp ((σ * t) ^ (2 : ℕ) / 2)) *
        Real.exp ((σ⁻¹ * |x|) ^ (2 : ℕ)) := by
  let y := σ⁻¹ * |x|
  let a := σ * t
  have hy : 0 ≤ y := mul_nonneg (inv_nonneg.mpr hσ.le) (abs_nonneg x)
  have hay : a * y = t * |x| := by dsimp [a, y]; field_simp
  have habs : |t * x| = a * y := by rw [abs_mul, abs_of_pos ht, hay]
  have hsq : (t * x) ^ (2 : ℕ) = a ^ (2 : ℕ) * y ^ (2 : ℕ) := by
    rw [← mul_pow, hay, mul_pow, mul_pow, sq_abs]
  have hr := rpow_mul_exp_linear_le (m := 2) (a := a) hy (by norm_num)
  have hs : ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hs, Real.rpow_two] at hr
  calc
    _ ≤ 3 * (t * x) ^ (2 : ℕ) * Real.exp |t * x| := abs_exp_sub_one_add_le _
    _ = (3 * a ^ (2 : ℕ)) * (y ^ (2 : ℕ) * Real.exp (a * y)) := by rw [habs, hsq]; ring
    _ ≤ (3 * a ^ (2 : ℕ)) * (2 * Real.exp (y ^ (2 : ℕ) + a ^ (2 : ℕ) / 2)) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by rw [Real.exp_add]; dsimp [a, y]; ring

lemma lintegral_exp_remainder_le {σ : ℝ} (hσ : 0 < σ) {X : Ω → ℝ}
    (hp : SubdiffusiveProcess.OGammaLE μ 2 σ X) (hn : SubdiffusiveProcess.OGammaLE μ 2 σ (fun ω => -X ω))
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ENNReal.ofReal |Real.exp (t * X ω) - (1 + t * X ω)| ∂μ ≤
      ENNReal.ofReal (32 * σ ^ (2 : ℕ) * t ^ (2 : ℕ) * Real.exp (32 * σ ^ (2 : ℕ) * t ^ (2 : ℕ))) := by
  have h := lintegral_le_of_gaussian_dom
    (K := 6 * (σ * t) ^ (2 : ℕ) * Real.exp ((σ * t) ^ (2 : ℕ) / 2))
    (by positivity) hp hn (fun ω => exp_remainder_gaussian_dom hσ ht (X ω))
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hs : 0 ≤ σ ^ (2 : ℕ) * t ^ (2 : ℕ) := by positivity
  have he : Real.exp ((σ * t) ^ (2 : ℕ) / 2) ≤ Real.exp (32 * σ ^ (2 : ℕ) * t ^ (2 : ℕ)) := by
    apply Real.exp_le_exp.mpr
    rw [mul_pow]
    nlinarith
  calc
    _ = (24 * σ ^ (2 : ℕ) * t ^ (2 : ℕ)) * Real.exp ((σ * t) ^ (2 : ℕ) / 2) := by ring
    _ ≤ (32 * σ ^ (2 : ℕ) * t ^ (2 : ℕ)) * Real.exp (32 * σ ^ (2 : ℕ) * t ^ (2 : ℕ)) :=
      mul_le_mul (by nlinarith) he (Real.exp_pos _).le (by positivity)

lemma exp_sub_one_rpow_gaussian_dom {σ t m : ℝ} (hσ : 0 < σ) (ht : 0 < t)
    (hm : 1 ≤ m) (x : ℝ) :
    |Real.exp (t * x) - 1| ^ m ≤
      ((m ^ (1 / 2 : ℝ) * σ * t) ^ m * Real.exp ((m * σ * t) ^ (2 : ℕ) / 2)) *
        Real.exp ((σ⁻¹ * |x|) ^ (2 : ℕ)) := by
  let y := σ⁻¹ * |x|
  let b := σ * t
  have hy : 0 ≤ y := mul_nonneg (inv_nonneg.mpr hσ.le) (abs_nonneg x)
  have hb : 0 ≤ b := mul_nonneg hσ.le ht.le
  have hby : b * y = t * |x| := by dsimp [b, y]; field_simp
  have habs : |t * x| = b * y := by rw [abs_mul, abs_of_pos ht, hby]
  have hr := rpow_mul_exp_linear_le (m := m) (a := m * b) hy (lt_of_lt_of_le zero_lt_one hm)
  calc
    _ ≤ (|t * x| * Real.exp |t * x|) ^ m :=
      Real.rpow_le_rpow (abs_nonneg _) (abs_exp_sub_one_le _) (by linarith)
    _ = b ^ m * (y ^ m * Real.exp ((m * b) * y)) := by
      rw [habs, Real.mul_rpow (by positivity) (Real.exp_pos _).le,
        Real.mul_rpow hb hy, ← Real.exp_mul]
      rw [show b * y * m = m * b * y by ring]
      ring
    _ ≤ b ^ m * ((m ^ (1 / 2 : ℝ)) ^ m * Real.exp (y ^ (2 : ℕ) + (m * b) ^ (2 : ℕ) / 2)) :=
      mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hb _)
    _ = _ := by
      rw [Real.exp_add, ← mul_assoc, ← Real.mul_rpow hb (by positivity)]
      have hbase : b * m ^ (1 / 2 : ℝ) = m ^ (1 / 2 : ℝ) * σ * t := by dsimp [b]; ring
      have hexp : (m * b) ^ (2 : ℕ) = (m * σ * t) ^ (2 : ℕ) := by dsimp [b]; ring
      rw [hbase, hexp]
      ring

lemma lintegral_exp_sub_one_rpow_le {σ : ℝ} (hσ : 0 < σ) {X : Ω → ℝ}
    (hp : SubdiffusiveProcess.OGammaLE μ 2 σ X) (hn : SubdiffusiveProcess.OGammaLE μ 2 σ (fun ω => -X ω))
    {m t : ℝ} (hm : 1 ≤ m) (ht : 0 < t) :
    ∫⁻ ω, ENNReal.ofReal (|Real.exp (t * X ω) - 1| ^ m) ∂μ ≤
      ENNReal.ofReal ((32 * m ^ (1 / 2 : ℝ) * σ * t) ^ m * Real.exp (32 * (m * σ * t) ^ (2 : ℕ))) := by
  have h := lintegral_le_of_gaussian_dom
    (K := (m ^ (1 / 2 : ℝ) * σ * t) ^ m * Real.exp ((m * σ * t) ^ (2 : ℕ) / 2))
    (by positivity) hp hn (fun ω => exp_sub_one_rpow_gaussian_dom hσ ht hm (X ω))
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have h4 : (4 : ℝ) ≤ (32 : ℝ) ^ m := by
    exact (by norm_num : (4 : ℝ) ≤ 32).trans (Real.self_le_rpow_of_one_le (by norm_num) hm)
  have he : Real.exp ((m * σ * t) ^ (2 : ℕ) / 2) ≤ Real.exp (32 * (m * σ * t) ^ (2 : ℕ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (m * σ * t)]
  calc
    _ = (4 * (m ^ (1 / 2 : ℝ) * σ * t) ^ m) * Real.exp ((m * σ * t) ^ (2 : ℕ) / 2) := by ring
    _ ≤ ((32 : ℝ) ^ m * (m ^ (1 / 2 : ℝ) * σ * t) ^ m) * Real.exp (32 * (m * σ * t) ^ (2 : ℕ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right h4 (by positivity)) he (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) (by positivity)]
      congr 2
      ring

end SubdiffusiveProcess.Probability
