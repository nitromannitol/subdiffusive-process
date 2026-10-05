module

public import SubdiffusiveProcess.Section10.ExitTailMoments

@[expose] public section

/-! Reuse the canonical exponential-tail integration theorem after measurable
ceiling discretization. All exponents are real and strictly positive. -/
open Filter MeasureTheory ProbabilityTheory MarkovProcess Set Topology
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.ExitTailMoments

/-- Fixed rate, independent of the law, domain and mean scale. -/
def ceilingRate : ℝ := Real.log 2 / 2

lemma ceilingRate_pos : 0 < ceilingRate :=
  half_pos (Real.log_pos (by norm_num))

lemma ceilingRate_lt_log_two : ceilingRate < Real.log 2 := by
  unfold ceilingRate
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

def ceilingExpBound : ℝ :=
  1 + Real.exp ceilingRate / (1 - Real.exp (ceilingRate - Real.log 2))

lemma ceilingExpBound_pos : 0 < ceilingExpBound := by
  have hden : 0 < 1 - Real.exp (ceilingRate - Real.log 2) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (sub_neg.mpr ceilingRate_lt_log_two))
  unfold ceilingExpBound
  exact add_pos (by norm_num) (div_pos (Real.exp_pos _) hden)

/-- Positive upper-moment coefficient, depending only on p. -/
def upperMomentConstant (p : ℝ) : ℝ :=
  (2 * (p / ceilingRate)) ^ p * ceilingExpBound

lemma upperMomentConstant_pos (p : ℝ) (hp : 0 < p) :
    0 < upperMomentConstant p :=
  mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num)
    (div_pos hp ceilingRate_pos)) _) ceilingExpBound_pos

lemma half_pow_eq_exp (n : ℕ) :
    (1 / 2 : ℝ) ^ n = Real.exp (-Real.log 2 * (n : ℝ)) := by
  have h : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [h, ← Real.exp_nat_mul]
  congr 1
  ring

/-- Scalar domination only; integration is delegated to the existing library. -/
lemma rpow_le_scaled_exp (p theta x : ℝ) (hp : 0 < p) (htheta : 0 < theta)
    (hx : 0 ≤ x) : x ^ p ≤ (p / theta) ^ p * Real.exp (theta * x) := by
  rcases eq_or_lt_of_le hx with rfl | hx0
  · rw [Real.zero_rpow hp.ne']
    positivity
  have hy : 0 < theta * x / p := div_pos (mul_pos htheta hx0) hp
  have hlog : Real.log (theta * x / p) ≤ theta * x / p := Real.log_le_self hy.le
  have hexp : (theta * x / p) ^ p ≤ Real.exp (theta * x) := by
    rw [Real.rpow_def_of_pos hy]
    apply Real.exp_le_exp.mpr
    calc Real.log (theta * x / p) * p ≤ (theta * x / p) * p :=
        mul_le_mul_of_nonneg_right hlog hp.le
      _ = theta * x := div_mul_cancel₀ _ hp.ne'
  have hfactor : (p / theta) * (theta * x / p) = x := by
    field_simp
  calc x ^ p = ((p / theta) * (theta * x / p)) ^ p := by rw [hfactor]
    _ = (p / theta) ^ p * (theta * x / p) ^ p :=
      Real.mul_rpow (div_pos hp htheta).le hy.le
    _ ≤ (p / theta) ^ p * Real.exp (theta * x) :=
      mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (div_pos hp htheta).le _)

/-- Generic probability-law passage from geometric survival to real positive
moments. This retains the ENNReal time and discards no infinite-time branch. -/
theorem moment_le_of_geometric_survival {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (tau : Ω → ℝ≥0∞)
    (htau : Measurable tau) (K : ℝ≥0) (hK : 1 ≤ K)
    (hmean : (∫⁻ w, tau w ∂mu) ≤ (K : ℝ≥0∞))
    (htail : ∀ n : ℕ,
      mu {w | ((n • (2 * K) : ℝ≥0) : ℝ≥0∞) < tau w} ≤ (1 / 2 : ℝ≥0∞) ^ n)
    (p : ℝ) (hp : 0 < p) :
    (∫⁻ w, tau w ^ p ∂mu) ≤ ENNReal.ofReal (upperMomentConstant p * (K : ℝ) ^ p) := by
  have hK0 : 0 < (K : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hK
  have h2K : 0 < 2 * (K : ℝ) := mul_pos (by norm_num) hK0
  let B : Ω → ℕ := fun w => Nat.ceil ((tau w).toReal / (2 * (K : ℝ)))
  have hB : Measurable B := (htau.ennreal_toReal.div_const _).nat_ceil
  have hBtail : ∀ n : ℕ, mu.real {w | n < B w} ≤ Real.exp (-Real.log 2 * (n : ℝ)) := by
    intro n
    have hsubset : {w | n < B w} ⊆
        {w | ((n • (2 * K) : ℝ≥0) : ℝ≥0∞) < tau w} := by
      intro w hw
      change n < Nat.ceil ((tau w).toReal / (2 * (K : ℝ))) at hw
      change ((n • (2 * K) : ℝ≥0) : ℝ≥0∞) < tau w
      have hfin : tau w ≠ ⊤ := by
        intro htop
        simp only [htop, ENNReal.toReal_top, zero_div, Nat.ceil_zero, not_lt_zero] at hw
      have hx : (n : ℝ) < (tau w).toReal / (2 * (K : ℝ)) := Nat.lt_ceil.mp hw
      have hy := (lt_div_iff₀ h2K).mp hx
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_toReal hfin]
      have hpos : 0 < (tau w).toReal :=
        lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg n) h2K.le) hy
      apply (ENNReal.ofReal_lt_ofReal_iff hpos).mpr
      simpa only [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat] using hy
    calc mu.real {w | n < B w} ≤
        mu.real {w | ((n • (2 * K) : ℝ≥0) : ℝ≥0∞) < tau w} := measureReal_mono hsubset
      _ ≤ ((1 / 2 : ℝ≥0∞) ^ n).toReal := ENNReal.toReal_mono (by finiteness) (htail n)
      _ = Real.exp (-Real.log 2 * (n : ℝ)) := by
        rw [ENNReal.toReal_pow]
        norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
        exact half_pow_eq_exp n
  obtain ⟨hint, hbound⟩ := SubdiffusiveProcess.integrable_exp_nat_of_exponential_tail
    mu B hB 1 (Real.log 2) ceilingRate (by norm_num) ceilingRate_pos.le
    ceilingRate_lt_log_two (by intro n; simpa only [one_mul] using hBtail n)
  have hexp : (∫⁻ w, ENNReal.ofReal (Real.exp (ceilingRate * (B w : ℝ))) ∂mu) ≤
      ENNReal.ofReal ceilingExpBound := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
    exact ENNReal.ofReal_le_ofReal (by simpa only [one_mul, ceilingExpBound] using hbound)
  have hfinite : ∀ᵐ w ∂mu, tau w < ⊤ :=
    ae_lt_top htau (ne_top_of_le_ne_top ENNReal.coe_ne_top hmean)
  have hcoef : 0 < (2 * (p / ceilingRate)) ^ p * (K : ℝ) ^ p :=
    mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) (div_pos hp ceilingRate_pos)) _)
      (Real.rpow_pos_of_pos hK0 _)
  have hpoint : ∀ᵐ w ∂mu, tau w ^ p ≤
      ENNReal.ofReal ((2 * (p / ceilingRate)) ^ p * (K : ℝ) ^ p) *
        ENNReal.ofReal (Real.exp (ceilingRate * (B w : ℝ))) := by
    filter_upwards [hfinite] with w hw
    have hceil := Nat.le_ceil ((tau w).toReal / (2 * (K : ℝ)))
    have htime : (tau w).toReal ≤ (2 * (K : ℝ)) * (B w : ℝ) := by
      have h := (div_le_iff₀ h2K).mp hceil
      simpa only [B, mul_comm] using h
    have hpow := Real.rpow_le_rpow ENNReal.toReal_nonneg htime hp.le
    have hdom := rpow_le_scaled_exp p ceilingRate (B w) hp ceilingRate_pos (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hdom (Real.rpow_nonneg h2K.le p)
    rw [Real.mul_rpow h2K.le (by positivity)] at hpow
    have hscalar : (tau w).toReal ^ p ≤
        (2 * (p / ceilingRate)) ^ p * (K : ℝ) ^ p *
          Real.exp (ceilingRate * (B w : ℝ)) := by
      apply le_trans hpow
      convert hmul using 1 ;
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hK0.le,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (div_pos hp ceilingRate_pos).le] ; ring
    rw [← ENNReal.ofReal_toReal hw.ne, ENNReal.ofReal_rpow_of_nonneg
      ENNReal.toReal_nonneg hp.le, ← ENNReal.ofReal_mul hcoef.le]
    exact ENNReal.ofReal_le_ofReal hscalar
  calc (∫⁻ w, tau w ^ p ∂mu)
      ≤ ∫⁻ w, ENNReal.ofReal ((2 * (p / ceilingRate)) ^ p * (K : ℝ) ^ p) *
          ENNReal.ofReal (Real.exp (ceilingRate * (B w : ℝ))) ∂mu := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal ((2 * (p / ceilingRate)) ^ p * (K : ℝ) ^ p) *
        ∫⁻ w, ENNReal.ofReal (Real.exp (ceilingRate * (B w : ℝ))) ∂mu :=
      lintegral_const_mul _ ((measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hB)).exp.ennreal_ofReal)
    _ ≤ ENNReal.ofReal ((2 * (p / ceilingRate)) ^ p * (K : ℝ) ^ p) *
        ENNReal.ofReal ceilingExpBound := mul_le_mul_right hexp _
    _ = ENNReal.ofReal (upperMomentConstant p * (K : ℝ) ^ p) := by
      rw [← ENNReal.ofReal_mul hcoef.le]
      congr 1
      unfold upperMomentConstant
      ring

/-- Complete generic tail-plus-moment supplier on an actual killed semigroup. -/
theorem upper_moment_of_mean {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (S : SubMarkovKernelSemigroup α) (law : Kernel α Ω) [IsMarkovKernel law]
    (tau : Ω → ℝ≥0∞) (htau : Measurable tau) (K : ℝ≥0) (hK : 1 ≤ K)
    (hrow : ∀ t : ℝ≥0, 0 < t → ∀ x,
      S t x univ = law x {w | (t : ℝ≥0∞) < tau w})
    (hmean : ∀ x, (∫⁻ w, tau w ∂law x) ≤ (K : ℝ≥0∞))
    (p : ℝ) (hp : 0 < p) (x : α) :
    (∫⁻ w, tau w ^ p ∂law x) ≤ ENNReal.ofReal (upperMomentConstant p * (K : ℝ) ^ p) :=
  moment_le_of_geometric_survival (law x) tau htau K hK (hmean x)
    (fun n => geometric_survival_of_mean S law tau htau K hK hrow hmean n x) p hp

end SubdiffusiveProcess.Section10.ExitTailMoments
