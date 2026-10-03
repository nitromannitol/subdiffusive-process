module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ExponentialSequence

@[expose] public section

/-!
# Universal arithmetic for exponential-sequence concentration

This module chooses the universal amplitude, moment denominator, and final
constant left explicit by `concentration_exp_sequence_of_parameters`.
The transcendental normalization is kept separate from the probabilistic
carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.IndependentSums
open scoped BigOperators ENNReal

noncomputable section

/-- A fixed amplitude dominating the score threshold after `p ≥ 2/θ`. -/
def expSequenceAmplitude : ℝ :=
  12 * max 1 SubdiffusiveProcess.Concentration.Cstar * Real.exp 1

theorem expSequenceAmplitude_gt_one : 1 < expSequenceAmplitude := by
  have hC : (1 : ℝ) ≤ max 1 SubdiffusiveProcess.Concentration.Cstar := le_max_left _ _
  have he : 1 < Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.2 (by norm_num : (0 : ℝ) < 1)
  unfold expSequenceAmplitude
  nlinarith only [hC, he, Real.exp_pos 1]

/-- Denominator in the choice `p = (s/δ₀)^2 / D`. -/
def expSequenceMomentDenom : ℝ :=
  18 * (Real.log expSequenceAmplitude + Real.log 3 + 1)

theorem expSequenceMomentDenom_pos : 0 < expSequenceMomentDenom := by
  have hlogA : 0 < Real.log expSequenceAmplitude :=
    Real.log_pos expSequenceAmplitude_gt_one
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold expSequenceMomentDenom
  positivity

/-- One universal constant simultaneously enforces the forward-log scale,
the crossing threshold, `p ≥ 2/θ`, and the final exponential rate. -/
def expSequenceConcentrationConst : ℝ :=
  4 + 2 * gammaTriangleConst 2 +
    Real.sqrt (2 * expSequenceMomentDenom) + 32 * expSequenceMomentDenom

theorem expSequenceConcentrationConst_pos : 0 < expSequenceConcentrationConst := by
  unfold expSequenceConcentrationConst
  have hgamma := gammaTriangleConst_pos (σ := 2)
  have hD := expSequenceMomentDenom_pos
  positivity

private theorem Cstar_rpow_one_div_le_max {p : ℝ} (hp : 1 ≤ p) :
    SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) ≤ max 1 SubdiffusiveProcess.Concentration.Cstar := by
  have hC0 : 0 < SubdiffusiveProcess.Concentration.Cstar := SubdiffusiveProcess.Concentration.Cstar_pos
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hexp0 : 0 ≤ 1 / p := by positivity
  have hexp1 : 1 / p ≤ 1 := by
    rw [div_le_one hp0]
    exact hp
  rcases le_total SubdiffusiveProcess.Concentration.Cstar 1 with hCle | hCle
  · exact (Real.rpow_le_one hC0.le hCle hexp0).trans (le_max_left _ _)
  · simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hCle hexp1).trans (le_max_right 1 _)

private theorem theta_half_rpow_neg_one_div_le_exp_one
    {theta p : ℝ} (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hp : 2 / theta ≤ p) :
    (theta / 2) ^ (-1 / p) ≤ Real.exp 1 := by
  have hp0 : 0 < p := (div_pos (by norm_num) htheta).trans_le hp
  have hx0 : 0 < theta / 2 := by positivity
  have hinv0 : 0 < 2 / theta := div_pos (by norm_num) htheta
  have hinv1 : 1 ≤ 2 / theta := by
    rw [le_div_iff₀ htheta]
    linarith
  have hlog0 : 0 ≤ Real.log (2 / theta) := Real.log_nonneg hinv1
  have hlogle : Real.log (2 / theta) ≤ 2 / theta := by
    exact (Real.log_le_sub_one_of_pos hinv0).trans (by linarith)
  have hpinv : 1 / p ≤ theta / 2 := by
    rw [div_le_iff₀ hp0]
    have := mul_le_mul_of_nonneg_left hp htheta.le
    field_simp [htheta.ne'] at this ⊢
    linarith
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.2
  have hlogid : -Real.log (theta / 2) = Real.log (2 / theta) := by
    rw [show theta / 2 = (2 / theta)⁻¹ by field_simp]
    rw [Real.log_inv]
    ring
  have hprod : Real.log (2 / theta) * (1 / p) ≤ (2 / theta) * (theta / 2) :=
    calc
      Real.log (2 / theta) * (1 / p) ≤ (2 / theta) * (1 / p) :=
        mul_le_mul_of_nonneg_right hlogle (by positivity)
      _ ≤ (2 / theta) * (theta / 2) :=
        mul_le_mul_of_nonneg_left hpinv hinv0.le
  have hcancel : (2 / theta) * (theta / 2) = 1 := by field_simp
  rw [hcancel] at hprod
  calc
    Real.log (theta / 2) * (-1 / p) =
        Real.log (2 / theta) * (1 / p) := by rw [← hlogid]; ring
    _ ≤ 1 := hprod

theorem expSequence_threshold_lt_amplitude
    {theta p : ℝ} (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hp : 2 / theta ≤ p) :
    6 * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) * (theta / 2) ^ (-1 / p) <
      expSequenceAmplitude := by
  have hC := Cstar_rpow_one_div_le_max (le_trans (by
    have : (1 : ℝ) ≤ 2 / theta := by
      rw [le_div_iff₀ htheta]
      linarith
    exact this) hp)
  have hthetaPow := theta_half_rpow_neg_one_div_le_exp_one htheta htheta1 hp
  have hmax0 : 0 ≤ max 1 SubdiffusiveProcess.Concentration.Cstar := (le_max_left _ _).trans' zero_le_one
  have hpow0 : 0 ≤ SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) :=
    Real.rpow_nonneg SubdiffusiveProcess.Concentration.Cstar_pos.le _
  have htheta0 : 0 ≤ (theta / 2) ^ (-1 / p) :=
    Real.rpow_nonneg (by positivity) _
  unfold expSequenceAmplitude
  calc
    6 * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) * (theta / 2) ^ (-1 / p) ≤
        6 * max 1 SubdiffusiveProcess.Concentration.Cstar * Real.exp 1 := by gcongr
    _ < 12 * max 1 SubdiffusiveProcess.Concentration.Cstar * Real.exp 1 := by
      have hbase : 0 < max 1 SubdiffusiveProcess.Concentration.Cstar * Real.exp 1 :=
        mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Real.exp_pos _)
      nlinarith

/-- The manuscript choice `p = (s/δ₀)^2 / D`. -/
def expSequenceMoment (s delta0 : ℝ) : ℝ :=
  (s / delta0) ^ 2 / expSequenceMomentDenom

theorem expSequenceMoment_pos {s delta0 : ℝ} (hs : 0 < s) (hdelta0 : 0 < delta0) :
    0 < expSequenceMoment s delta0 := by
  unfold expSequenceMoment
  exact div_pos (sq_pos_of_pos (div_pos hs hdelta0)) expSequenceMomentDenom_pos

/-- The Gaussian quadratic in the one-coordinate tail pays for the fixed
amplitude and every geometric compensation `3^n`. -/
theorem expSequence_moment_numeric
    {s delta0 : ℝ} (hs : 0 < s) (hdelta0 : 0 < delta0) :
    ∀ n : ℕ,
      (expSequenceAmplitude * (3 : ℝ) ^ (n : ℝ)) ^
          expSequenceMoment s delta0 *
        Real.exp (-(((s / 3) * ((n : ℝ) + 1) / delta0) ^ 2)) ≤ 1 := by
  intro n
  let q : ℝ := (s / delta0) ^ 2
  let D : ℝ := expSequenceMomentDenom
  have hq : 0 < q := sq_pos_of_pos (div_pos hs hdelta0)
  have hD : 0 < D := expSequenceMomentDenom_pos
  have hp : expSequenceMoment s delta0 = q / D := rfl
  have hp0 : 0 < expSequenceMoment s delta0 := expSequenceMoment_pos hs hdelta0
  have hA : 0 < expSequenceAmplitude := zero_lt_one.trans expSequenceAmplitude_gt_one
  have h3n : 0 < (3 : ℝ) ^ (n : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hlogA : 0 ≤ Real.log expSequenceAmplitude :=
    (Real.log_pos expSequenceAmplitude_gt_one).le
  have hlog3 : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hL : Real.log expSequenceAmplitude + Real.log 3 + 1 = D / 18 := by
    unfold D expSequenceMomentDenom
    ring
  have hlogBound :
      Real.log expSequenceAmplitude + (n : ℝ) * Real.log 3 ≤
        (D / 18) * ((n : ℝ) + 1) ^ 2 := by
    rw [← hL]
    have hL0 : 0 ≤ Real.log expSequenceAmplitude + Real.log 3 + 1 := by positivity
    have hfirst : Real.log expSequenceAmplitude + (n : ℝ) * Real.log 3 ≤
        (Real.log expSequenceAmplitude + Real.log 3 + 1) * ((n : ℝ) + 1) := by
      nlinarith only [hlogA, hlog3, hn,
        mul_nonneg hn hlogA]
    have hsecond :
        (Real.log expSequenceAmplitude + Real.log 3 + 1) * ((n : ℝ) + 1) ≤
          (Real.log expSequenceAmplitude + Real.log 3 + 1) * ((n : ℝ) + 1) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hL0
      nlinarith only [hn, sq_nonneg ((n : ℝ) + 1)]
    exact hfirst.trans hsecond
  have hpd : expSequenceMoment s delta0 * D = q := by
    rw [hp]
    field_simp [hD.ne']
  have hmain :
      (Real.log expSequenceAmplitude + (n : ℝ) * Real.log 3) *
          expSequenceMoment s delta0 ≤
        q / 18 * ((n : ℝ) + 1) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hlogBound hp0.le
    have hright : (D / 18 * ((n : ℝ) + 1) ^ 2) *
        expSequenceMoment s delta0 =
          q / 18 * ((n : ℝ) + 1) ^ 2 := by
      nlinarith only [hpd]
    exact hmul.trans_eq hright
  have htail : ((s / 3) * ((n : ℝ) + 1) / delta0) ^ 2 =
      q / 9 * ((n : ℝ) + 1) ^ 2 := by
    unfold q
    field_simp [hdelta0.ne']
    ring
  rw [Real.rpow_def_of_pos (mul_pos hA h3n)]
  rw [Real.log_mul hA.ne' h3n.ne', Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
  rw [← Real.exp_add, htail]
  have hexp :
      (Real.log expSequenceAmplitude + (n : ℝ) * Real.log 3) *
          expSequenceMoment s delta0 +
        -(q / 9 * ((n : ℝ) + 1) ^ 2) ≤ 0 := by
    have hqn : 0 ≤ q * ((n : ℝ) + 1) ^ 2 := mul_nonneg hq.le (sq_nonneg _)
    nlinarith only [hmain, hqn]
  simpa only [Real.exp_zero] using Real.exp_le_exp.2 hexp

private theorem expSequenceConst_ge_four :
    (4 : ℝ) ≤ expSequenceConcentrationConst := by
  unfold expSequenceConcentrationConst
  have hgamma := (gammaTriangleConst_pos (σ := 2)).le
  have hD := expSequenceMomentDenom_pos.le
  have hsqrt : 0 ≤ Real.sqrt (2 * expSequenceMomentDenom) := Real.sqrt_nonneg _
  nlinarith

private theorem expSequenceConst_ge_two_gamma :
    2 * gammaTriangleConst 2 ≤ expSequenceConcentrationConst := by
  unfold expSequenceConcentrationConst
  have hD := expSequenceMomentDenom_pos.le
  have hsqrt : 0 ≤ Real.sqrt (2 * expSequenceMomentDenom) := Real.sqrt_nonneg _
  nlinarith

private theorem expSequenceConst_ge_sqrt_two_D :
    Real.sqrt (2 * expSequenceMomentDenom) ≤ expSequenceConcentrationConst := by
  unfold expSequenceConcentrationConst
  have hgamma := (gammaTriangleConst_pos (σ := 2)).le
  have hD := expSequenceMomentDenom_pos.le
  nlinarith

private theorem expSequenceConst_ge_thirtytwo_D :
    32 * expSequenceMomentDenom ≤ expSequenceConcentrationConst := by
  unfold expSequenceConcentrationConst
  have hgamma := (gammaTriangleConst_pos (σ := 2)).le
  have hsqrt : 0 ≤ Real.sqrt (2 * expSequenceMomentDenom) := Real.sqrt_nonneg _
  nlinarith

private theorem expSequence_smallness_budget
    {s theta delta0 : ℝ} (_hdelta0 : 0 < delta0) (hs : 0 < s)
    (htheta : 0 < theta)
    (hsmall : delta0 ≤ expSequenceConcentrationConst⁻¹ * s * Real.sqrt theta) :
    delta0 * expSequenceConcentrationConst ≤ s * Real.sqrt theta := by
  have hC := expSequenceConcentrationConst_pos
  calc
    delta0 * expSequenceConcentrationConst ≤
        (expSequenceConcentrationConst⁻¹ * s * Real.sqrt theta) *
          expSequenceConcentrationConst :=
      mul_le_mul_of_nonneg_right hsmall hC.le
    _ = s * Real.sqrt theta := by field_simp [hC.ne']

theorem expSequenceMoment_ge_two_div_theta
    {s theta delta0 : ℝ} (hdelta0 : 0 < delta0) (hs : 0 < s)
    (htheta : 0 < theta)
    (hsmall : delta0 ≤ expSequenceConcentrationConst⁻¹ * s * Real.sqrt theta) :
    2 / theta ≤ expSequenceMoment s delta0 := by
  have hbudget := expSequence_smallness_budget hdelta0 hs htheta hsmall
  have hD := expSequenceMomentDenom_pos
  have hsqrtD : 0 ≤ Real.sqrt (2 * expSequenceMomentDenom) := Real.sqrt_nonneg _
  have hdeltaSqrt : delta0 * Real.sqrt (2 * expSequenceMomentDenom) ≤
      s * Real.sqrt theta :=
    (mul_le_mul_of_nonneg_left expSequenceConst_ge_sqrt_two_D hdelta0.le).trans hbudget
  have hsqrtTheta : 0 ≤ Real.sqrt theta := Real.sqrt_nonneg _
  have hsquare := mul_self_le_mul_self
    (mul_nonneg hdelta0.le hsqrtD) hdeltaSqrt
  have hsquare' : delta0 ^ 2 * (2 * expSequenceMomentDenom) ≤ s ^ 2 * theta := by
    calc
      delta0 ^ 2 * (2 * expSequenceMomentDenom) =
          (delta0 * Real.sqrt (2 * expSequenceMomentDenom)) *
            (delta0 * Real.sqrt (2 * expSequenceMomentDenom)) := by
        symm
        calc
          (delta0 * Real.sqrt (2 * expSequenceMomentDenom)) *
              (delta0 * Real.sqrt (2 * expSequenceMomentDenom)) =
            delta0 ^ 2 * Real.sqrt (2 * expSequenceMomentDenom) ^ 2 := by ring
          _ = delta0 ^ 2 * (2 * expSequenceMomentDenom) := by
            rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * expSequenceMomentDenom)]
      _ ≤ (s * Real.sqrt theta) * (s * Real.sqrt theta) := hsquare
      _ = s ^ 2 * theta := by
        calc
          (s * Real.sqrt theta) * (s * Real.sqrt theta) =
              s ^ 2 * Real.sqrt theta ^ 2 := by ring
          _ = s ^ 2 * theta := by rw [Real.sq_sqrt htheta.le]
  unfold expSequenceMoment
  rw [div_le_div_iff₀ htheta hD]
  field_simp [hdelta0.ne']
  nlinarith only [hsquare']

theorem expSequenceLogScale_le_of_smallness
    {s theta delta0 : ℝ} (hdelta0 : 0 < delta0) (hs : 0 < s)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hsmall : delta0 ≤ expSequenceConcentrationConst⁻¹ * s * Real.sqrt theta) :
    expSequenceLogScale delta0 ≤ s := by
  have hbudget := expSequence_smallness_budget hdelta0 hs htheta hsmall
  have hsqrt1 : Real.sqrt theta ≤ 1 := (Real.sqrt_le_iff).2 ⟨by norm_num, by simpa using htheta1⟩
  have hbudget' : delta0 * expSequenceConcentrationConst ≤ s :=
    hbudget.trans (by exact mul_le_of_le_one_right hs.le hsqrt1)
  rw [expSequenceLogScale_eq]
  have hcoef : gammaTriangleConst 2 * (3 / 2 : ℝ) ≤
      expSequenceConcentrationConst := by
    have hgamma := gammaTriangleConst_pos (σ := 2)
    exact (by nlinarith : gammaTriangleConst 2 * (3 / 2 : ℝ) ≤
      2 * gammaTriangleConst 2).trans expSequenceConst_ge_two_gamma
  calc
    gammaTriangleConst 2 * (3 / 2) * delta0 ≤
        expSequenceConcentrationConst * delta0 :=
      mul_le_mul_of_nonneg_right hcoef hdelta0.le
    _ = delta0 * expSequenceConcentrationConst := by ring
    _ ≤ s := hbudget'

theorem expSequence_delta_le_third_of_smallness
    {s theta delta0 : ℝ} (hdelta0 : 0 < delta0) (hs : 0 < s)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hsmall : delta0 ≤ expSequenceConcentrationConst⁻¹ * s * Real.sqrt theta) :
    delta0 ≤ s / 3 := by
  have hbudget := expSequence_smallness_budget hdelta0 hs htheta hsmall
  have hsqrt1 : Real.sqrt theta ≤ 1 := (Real.sqrt_le_iff).2 ⟨by norm_num, by simpa using htheta1⟩
  have hbudget' : delta0 * expSequenceConcentrationConst ≤ s :=
    hbudget.trans (mul_le_of_le_one_right hs.le hsqrt1)
  have hfour := expSequenceConst_ge_four
  nlinarith only [hbudget', hfour, hdelta0]

theorem expSequence_rate_le_moment
    {s delta0 : ℝ} (hdelta0 : 0 < delta0) (hs : 0 < s) :
    s ^ 2 / (expSequenceConcentrationConst * delta0 ^ 2) ≤
      expSequenceMoment s delta0 / 32 := by
  have hC := expSequenceConcentrationConst_pos
  have hD := expSequenceMomentDenom_pos
  have hdeltaSq : 0 < delta0 ^ 2 := sq_pos_of_pos hdelta0
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos hC hdeltaSq)]
  unfold expSequenceMoment
  have hCD := expSequenceConst_ge_thirtytwo_D
  field_simp [hdelta0.ne', hD.ne']
  nlinarith only [hCD, sq_pos_of_pos hs]

/-- Proposition `p.concentration.for.scales.exp.sequence`.  All
universal-constant arithmetic is discharged. -/
theorem concentration_exp_sequence
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : ℤ → Omega → ℝ} {delta0 s theta : ℝ}
    (hdelta0 : 0 < delta0) (_hdelta01 : delta0 ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hXnn : ∀ i omega, 0 ≤ X i omega)
    (hXm : ∀ i, Measurable (X i))
    (hXindep : iIndepFun X mu)
    (hX : ∀ i, IsBigOWith mu (gammaSigma 2) (X i) delta0)
    (hsmall : delta0 ≤ expSequenceConcentrationConst⁻¹ * s * Real.sqrt theta) :
    ∀ (m0 : ℤ) (M : ℕ),
      mu (expSequenceDensityEvent X s theta m0 M) ≤
        ENNReal.ofReal (Real.exp
          (-(s ^ 2 * theta) /
            (expSequenceConcentrationConst * delta0 ^ 2) * ((M : ℝ) + 1))) := by
  intro m0 M
  have hpTheta := expSequenceMoment_ge_two_div_theta hdelta0 hs htheta hsmall
  have hp : 1 ≤ expSequenceMoment s delta0 := by
    have hone : (1 : ℝ) ≤ 2 / theta := by
      rw [le_div_iff₀ htheta]
      linarith
    exact hone.trans hpTheta
  have hraw := concentration_exp_sequence_of_parameters
    hdelta0 hs hs1 htheta htheta1 hp
    (zero_le_one.trans expSequenceAmplitude_gt_one.le)
    hXnn hXm hXindep hX
    (expSequenceLogScale_le_of_smallness hdelta0 hs htheta htheta1 hsmall)
    (expSequence_delta_le_third_of_smallness hdelta0 hs htheta htheta1 hsmall)
    (expSequence_threshold_lt_amplitude htheta htheta1 hpTheta)
    (expSequence_moment_numeric hs hdelta0) m0 M
  refine hraw.trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have hrate := expSequence_rate_le_moment hdelta0 hs
  have hthetaM : 0 ≤ theta * ((M : ℝ) + 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hrate hthetaM
  calc
    -(expSequenceMoment s delta0 * theta) / 32 * ((M : ℝ) + 1) =
        -(expSequenceMoment s delta0 / 32 * (theta * ((M : ℝ) + 1))) := by ring
    _ ≤ -(s ^ 2 / (expSequenceConcentrationConst * delta0 ^ 2) *
          (theta * ((M : ℝ) + 1))) := neg_le_neg hmul
    _ = -(s ^ 2 * theta) /
          (expSequenceConcentrationConst * delta0 ^ 2) * ((M : ℝ) + 1) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
