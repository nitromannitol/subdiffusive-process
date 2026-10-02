

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The small-disorder logarithmic exponent

Numerical support for the exponent used in the Section 9 one-cube estimate.
-/

namespace SubdiffusiveProcess.Section9

/-- The exact exponent `c δ⁻² |log δ|⁻²`. -/
noncomputable def smallDisorderExponent (c δ : ℝ) : ℝ :=
  c * δ⁻¹ ^ 2 * |Real.log δ|⁻¹ ^ 2

theorem smallDisorderExponent_eq_div {c δ : ℝ} (hδ : δ ≠ 0)
    (hlog : Real.log δ ≠ 0) :
    smallDisorderExponent c δ = c / (δ ^ 2 * |Real.log δ| ^ 2) := by
  unfold smallDisorderExponent
  have habs : |Real.log δ| ≠ 0 := abs_ne_zero.2 hlog
  field_simp

theorem smallDisorderExponent_mul_delta_sq {c δ : ℝ} (hδ : δ ≠ 0) :
    smallDisorderExponent c δ * δ ^ 2 = c * |Real.log δ|⁻¹ ^ 2 := by
  unfold smallDisorderExponent
  field_simp

/-- After writing `δ=e⁻ᵗ`, the exponent tends to infinity. -/
theorem tendsto_smallDisorderExponent_exp_neg (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => smallDisorderExponent c (Real.exp (-t)))
      Filter.atTop Filter.atTop := by
  have hraw := (tendsto_exp_mul_div_rpow_atTop 2 2 (by norm_num)).const_mul_atTop hc
  refine hraw.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
  unfold smallDisorderExponent
  rw [Real.log_exp, abs_neg, abs_of_nonneg (by linarith : 0 ≤ t)]
  rw [Real.rpow_two]
  simp only [inv_pow, Real.exp_neg, inv_inv, ← Real.exp_nat_mul]
  rw [div_eq_mul_inv]
  have hinv : (t ^ 2)⁻¹ = t⁻¹ ^ 2 := (inv_pow t 2).symm
  rw [mul_comm (2 : ℝ) t]
  rw [hinv]
  ring_nf

/-- An eventually large negative logarithm makes the exact exponent at least
any prescribed threshold. -/
theorem eventually_smallDisorderExponent_exp_neg_ge (c R : ℝ) (hc : 0 < c) :
    ∀ᶠ t in Filter.atTop, R ≤ smallDisorderExponent c (Real.exp (-t)) :=
  (tendsto_smallDisorderExponent_exp_neg c hc).eventually_ge_atTop R

theorem smallDisorderExponent_exp_neg_mul_sq (c t : ℝ) (ht : t ≠ 0) :
    smallDisorderExponent c (Real.exp (-t)) * Real.exp (-t) ^ 2 * t ^ 2 = c := by
  unfold smallDisorderExponent
  rw [Real.log_exp, abs_neg]
  have habs : |t| ≠ 0 := abs_ne_zero.2 ht
  field_simp [Real.exp_ne_zero]
  rw [sq_abs]

/-- The two numerical estimates needed after the substitution `δ=e⁻ᵗ`. -/
theorem smallDisorderExponent_exp_neg_estimates
    {B eta epsilon c t : ℝ} (hB : 0 < B) (heta : 0 < eta)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hsqrt : 2 * B * Real.sqrt c ≤ epsilon) (ht1 : 1 ≤ t)
    (hp2 : 2 ≤ smallDisorderExponent c (Real.exp (-t)))
    (hetaT : 3 * c / eta ≤ t) :
    smallDisorderExponent c (Real.exp (-t)) * Real.exp (-t) ^ 2 *
          Real.log (2 + smallDisorderExponent c (Real.exp (-t))) ≤ eta ∧
      B * Real.exp (-t) * Real.sqrt (smallDisorderExponent c (Real.exp (-t))) *
          Real.log (smallDisorderExponent c (Real.exp (-t))) ≤ epsilon := by
  let p := smallDisorderExponent c (Real.exp (-t))
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp2
  have hpexp : p ≤ Real.exp (2 * t) := by
    dsimp [p, smallDisorderExponent]
    rw [Real.log_exp, abs_neg, abs_of_pos ht0, Real.exp_neg, inv_inv]
    have htSq : 1 ≤ t ^ 2 := by nlinarith
    have hcdiv : c / t ^ 2 ≤ 1 := (div_le_one (by positivity)).2 (hc1.trans htSq)
    rw [inv_pow, ← div_eq_mul_inv]
    calc
      c * Real.exp t ^ 2 / t ^ 2 = (c / t ^ 2) * Real.exp t ^ 2 := by ring
      _ ≤ 1 * Real.exp t ^ 2 :=
        mul_le_mul_of_nonneg_right hcdiv (sq_nonneg _)
      _ = Real.exp (2 * t) := by rw [one_mul, ← Real.exp_nat_mul]; norm_num
  have hlogp : Real.log p ≤ 2 * t := by
    rw [Real.log_le_iff_le_exp hp0]
    exact hpexp
  have hlogTwoP : Real.log (2 + p) ≤ 3 * t := by
    have h2p : 2 + p ≤ 2 * p := by linarith
    have hlogmono := Real.log_le_log (by positivity : 0 < 2 + p) h2p
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp0.ne'] at hlogmono
    have hlog2 : Real.log 2 ≤ t :=
      (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by linarith)
    linarith
  constructor
  · have hcancel := smallDisorderExponent_exp_neg_mul_sq c t ht0.ne'
    have hbound : p * Real.exp (-t) ^ 2 * Real.log (2 + p) ≤ 3 * c / t := by
      have htSqPos : 0 < t ^ 2 := sq_pos_of_pos ht0
      have := mul_le_mul_of_nonneg_left hlogTwoP
        (mul_nonneg hp0.le (sq_nonneg (Real.exp (-t))))
      rw [show p * Real.exp (-t) ^ 2 = c / t ^ 2 by
        apply (eq_div_iff htSqPos.ne').2
        simpa only [mul_assoc] using hcancel] at this
      field_simp [ht0.ne'] at this ⊢
      nlinarith
    exact hbound.trans ((div_le_iff₀ ht0).2 (by
      apply (div_le_iff₀ heta).1 at hetaT
      nlinarith))
  · have hpnonneg : 0 ≤ p := hp0.le
    have hy0 : 0 ≤ Real.exp (-t) * Real.sqrt p * t := by positivity
    have hySq : (Real.exp (-t) * Real.sqrt p * t) ^ 2 = c := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hpnonneg]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        smallDisorderExponent_exp_neg_mul_sq c t ht0.ne'
    have hy : Real.exp (-t) * Real.sqrt p * t = Real.sqrt c := by
      symm
      apply (Real.sqrt_eq_iff_mul_self_eq hc.le hy0).2
      simpa only [pow_two] using hySq.symm
    have hamp : Real.exp (-t) * Real.sqrt p * Real.log p ≤ 2 * Real.sqrt c := by
      have hfac : 0 ≤ Real.exp (-t) * Real.sqrt p := by positivity
      have := mul_le_mul_of_nonneg_left hlogp hfac
      rw [show (Real.exp (-t) * Real.sqrt p) * (2 * t) =
        2 * (Real.exp (-t) * Real.sqrt p * t) by ring, hy] at this
      exact this
    calc
      B * Real.exp (-t) * Real.sqrt p * Real.log p =
          B * (Real.exp (-t) * Real.sqrt p * Real.log p) := by ring
      _ ≤ B * (2 * Real.sqrt c) := mul_le_mul_of_nonneg_left hamp hB.le
      _ = 2 * B * Real.sqrt c := by ring
      _ ≤ epsilon := hsqrt

/-- Simultaneous choice of the source exponent constant and disorder
threshold, uniform in the subsequently chosen disorder strength. -/
theorem exists_smallDisorderExponent_parameters
    (B eta epsilon : ℝ) (hB : 0 < B) (heta : 0 < eta)
    (hepsilon : 0 < epsilon) :
    ∃ c δzero : ℝ, 0 < c ∧ 0 < δzero ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δzero →
        δ ≤ 1 / 2 ∧
        2 ≤ smallDisorderExponent c δ ∧
        smallDisorderExponent c δ * δ ^ 2 *
            Real.log (2 + smallDisorderExponent c δ) ≤ eta ∧
        B * δ * Real.sqrt (smallDisorderExponent c δ) *
            Real.log (smallDisorderExponent c δ) ≤ epsilon := by
  let q : ℝ := min 1 (epsilon / (4 * B))
  let c : ℝ := q ^ 2
  have hq : 0 < q := lt_min (by norm_num) (div_pos hepsilon (by positivity))
  have hq1 : q ≤ 1 := min_le_left _ _
  have hc : 0 < c := sq_pos_of_pos hq
  have hc1 : c ≤ 1 := by dsimp [c]; nlinarith
  have hsqrt : 2 * B * Real.sqrt c ≤ epsilon := by
    have hqeps : q ≤ epsilon / (4 * B) := min_le_right _ _
    have hsqrtc : Real.sqrt c = q := by
      dsimp [c]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
    rw [hsqrtc]
    have := (le_div_iff₀ (show 0 < 4 * B by positivity)).1 hqeps
    nlinarith
  have hevent := eventually_smallDisorderExponent_exp_neg_ge c 2 hc
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Ttwo, hTtwo⟩ := hevent
  let T : ℝ := max 1 (max Ttwo (max (3 * c / eta) (Real.log 2)))
  let δzero : ℝ := Real.exp (-T)
  refine ⟨c, δzero, hc, Real.exp_pos _, ?_⟩
  intro δ hδ hδzero
  let t : ℝ := -Real.log δ
  have hT1 : 1 ≤ T := le_max_left _ _
  have hTtwo' : Ttwo ≤ T :=
    (le_max_left Ttwo (max (3 * c / eta) (Real.log 2))).trans (le_max_right _ _)
  have hTeta : 3 * c / eta ≤ T :=
    (le_max_left (3 * c / eta) (Real.log 2)).trans
      ((le_max_right Ttwo _).trans (le_max_right _ _))
  have hTlog : Real.log 2 ≤ T :=
    (le_max_right (3 * c / eta) (Real.log 2)).trans
      ((le_max_right Ttwo _).trans (le_max_right _ _))
  have htT : T ≤ t := by
    have hlog := Real.log_le_log hδ hδzero
    dsimp [δzero] at hlog
    rw [Real.log_exp] at hlog
    dsimp [t]
    linarith
  have ht1 : 1 ≤ t := hT1.trans htT
  have hteta : 3 * c / eta ≤ t := hTeta.trans htT
  have hδexp : Real.exp (-t) = δ := by
    dsimp [t]
    rw [neg_neg, Real.exp_log hδ]
  have hp2exp : 2 ≤ smallDisorderExponent c (Real.exp (-t)) :=
    hTtwo t (hTtwo'.trans htT)
  have hest := smallDisorderExponent_exp_neg_estimates hB heta hc hc1 hsqrt ht1 hp2exp hteta
  have hhalf : δ ≤ 1 / 2 := by
    have hexpmono : Real.exp (-T) ≤ Real.exp (-Real.log 2) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hr : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hr] at hexpmono
    exact hδzero.trans hexpmono
  rw [hδexp] at hp2exp hest
  exact ⟨hhalf, hp2exp, hest.1, hest.2⟩

end SubdiffusiveProcess.Section9
