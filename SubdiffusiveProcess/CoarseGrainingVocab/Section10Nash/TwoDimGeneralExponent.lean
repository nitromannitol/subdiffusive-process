module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section10Nash.Interpolation
public import Homogenization.Sobolev.CubeEmbedding.LimitFiniteP
public import Homogenization.Sobolev.MatchedPair.ScaledPoincare
public import Homogenization.Sobolev.W1p.FiniteMeasureDowngrade

@[expose] public section

/-!
# General finite-exponent Nash inequality in dimension two

For every finite exponent `q > 2`, this file constructs the Sobolev source
exponent `2q / (q + 2)`, proves the corresponding `H¹ → L^q` cube estimate,
and combines it with the exact `L¹`--`L²`--`L^q` interpolation inequality.

The Nash parameter is `theta = 1 - 2 / q`.  Thus the final inequality has
the form

`||u||₂^(2(1 + theta)) ≤ ||u||₁^(2 theta) * (Sobolev RHS)²`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section10Nash

open MeasureTheory Homogenization
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The Nash parameter associated with a finite two-dimensional target
exponent `q`. -/
def twoDimNashThetaOfExponent (q : FiniteLpExponent) : ℝ :=
  1 - 2 / q.exponent.toReal

/-- The source exponent `2q / (q + 2)` whose two-dimensional Sobolev conjugate
is `q`. -/
def twoDimSobolevSourceExponent (q : FiniteLpExponent)
    (hq : (2 : ℝ≥0∞) < q.exponent) : FiniteLpExponent where
  exponent := ENNReal.ofReal (2 * q.exponent.toReal / (q.exponent.toReal + 2))
  one_lt := by
    rw [ENNReal.one_lt_ofReal]
    have hq' : 2 < q.exponent.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).2 hq
    have hden : 0 < q.exponent.toReal + 2 := by linarith
    calc
      1 = (q.exponent.toReal + 2) / (q.exponent.toReal + 2) := by field_simp
      _ < 2 * q.exponent.toReal / (q.exponent.toReal + 2) :=
        (div_lt_div_iff_of_pos_right hden).2 (by linarith)
  lt_top := ENNReal.ofReal_lt_top

/-- A finite target exponent above two has a real value above two. -/
theorem two_lt_toReal_of_two_lt_exponent (q : FiniteLpExponent)
    (hq : (2 : ℝ≥0∞) < q.exponent) : 2 < q.exponent.toReal :=
  (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).2 hq

/-- The source exponent for a finite two-dimensional target is at most two. -/
theorem twoDimSobolevSourceExponent_le_two (q : FiniteLpExponent)
    (hq : (2 : ℝ≥0∞) < q.exponent) :
    (twoDimSobolevSourceExponent q hq).exponent ≤ 2 := by
  rw [show (twoDimSobolevSourceExponent q hq).exponent =
    ENNReal.ofReal (2 * q.exponent.toReal / (q.exponent.toReal + 2)) by rfl]
  norm_num
  have hden : 0 < q.exponent.toReal + 2 := by positivity
  exact (div_le_iff₀ hden).2 (by linarith)

/-- The source exponent for a finite two-dimensional target is strictly below
the dimension. -/
theorem twoDimSobolevSourceExponent_toReal_lt_two (q : FiniteLpExponent)
    (hq : (2 : ℝ≥0∞) < q.exponent) :
    (twoDimSobolevSourceExponent q hq).exponent.toReal < 2 := by
  rw [show (twoDimSobolevSourceExponent q hq).exponent.toReal =
    2 * q.exponent.toReal / (q.exponent.toReal + 2) by
      simp [twoDimSobolevSourceExponent]
      exact div_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (by positivity)]
  have hq' := two_lt_toReal_of_two_lt_exponent q hq
  rw [div_lt_iff₀ (by positivity : 0 < q.exponent.toReal + 2)]
  nlinarith

/-- The source and target exponents obey the two-dimensional Sobolev relation. -/
theorem twoDimSobolevSourceExponent_relation (q : FiniteLpExponent)
    (hq : (2 : ℝ≥0∞) < q.exponent) :
    q.exponent.toReal⁻¹ =
      (twoDimSobolevSourceExponent q hq).exponent.toReal⁻¹ - (2 : ℝ)⁻¹ := by
  rw [show (twoDimSobolevSourceExponent q hq).exponent.toReal =
    2 * q.exponent.toReal / (q.exponent.toReal + 2) by
      simp [twoDimSobolevSourceExponent]
      exact div_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (by positivity)]
  have hq0 : 0 < q.exponent.toReal :=
    lt_trans (by norm_num) (two_lt_toReal_of_two_lt_exponent q hq)
  field_simp
  ring

/-- The finite-exponent Nash parameter is positive when `q > 2`. -/
theorem twoDimNashThetaOfExponent_pos (q : FiniteLpExponent)
    (hq : (2 : ℝ≥0∞) < q.exponent) :
    0 < twoDimNashThetaOfExponent q := by
  rw [twoDimNashThetaOfExponent]
  have hq' := two_lt_toReal_of_two_lt_exponent q hq
  rw [sub_pos, div_lt_one (by linarith : 0 < q.exponent.toReal)]
  exact hq'

/-- The finite-exponent Nash parameter is at most one. -/
theorem twoDimNashThetaOfExponent_le_one (q : FiniteLpExponent) :
    twoDimNashThetaOfExponent q ≤ 1 := by
  rw [twoDimNashThetaOfExponent]
  exact sub_le_self _ (div_nonneg (by norm_num) ENNReal.toReal_nonneg)

/-- The finite-exponent Nash parameter is strictly below one. -/
theorem twoDimNashThetaOfExponent_lt_one (q : FiniteLpExponent)
    (hq : (2 : ℝ≥0∞) < q.exponent) :
    twoDimNashThetaOfExponent q < 1 := by
  rw [twoDimNashThetaOfExponent]
  have hq0 : 0 < q.exponent.toReal :=
    lt_trans (by norm_num) (two_lt_toReal_of_two_lt_exponent q hq)
  exact sub_lt_self _ (div_pos (by norm_num) hq0)

/-- General finite-exponent interpolation in integral form. -/
theorem lintegral_two_dim_nash_interpolation
    {alpha : Type*} [MeasurableSpace alpha] (mu : Measure alpha)
    (f : alpha → ℝ) (q : FiniteLpExponent) (hq : (2 : ℝ≥0∞) < q.exponent)
    (hf : AEStronglyMeasurable f mu) :
    let theta := twoDimNashThetaOfExponent q
    (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 + theta) ≤
      (∫⁻ x, ‖f x‖ₑ ∂mu) ^ (2 * theta) *
        (∫⁻ x, ‖f x‖ₑ ^ q.exponent.toReal ∂mu) ^
          (2 / q.exponent.toReal) := by
  dsimp only
  let theta := twoDimNashThetaOfExponent q
  let s : ℝ := (1 + theta) / (2 * theta)
  let t : ℝ := q.exponent.toReal * (1 + theta) / 2
  let F : alpha → ℝ≥0∞ := fun x ↦ ‖f x‖ₑ ^ (2 * theta / (1 + theta))
  let G : alpha → ℝ≥0∞ := fun x ↦ ‖f x‖ₑ ^ (2 / (1 + theta))
  have htheta0 : 0 < theta := twoDimNashThetaOfExponent_pos q hq
  have htheta1 : theta < 1 := twoDimNashThetaOfExponent_lt_one q hq
  have hq0 : 0 < q.exponent.toReal :=
    lt_trans (by norm_num) (two_lt_toReal_of_two_lt_exponent q hq)
  have hs : 1 < s := by
    dsimp [s]
    rw [lt_div_iff₀ (mul_pos (by norm_num) htheta0)]
    linarith
  have ht : 1 < t := by
    have ht_eq : t = q.exponent.toReal - 1 := by
      dsimp [t, theta, twoDimNashThetaOfExponent]
      field_simp [hq0.ne']
      ring
    rw [ht_eq]
    linarith [two_lt_toReal_of_two_lt_exponent q hq]
  have hsum : (1 : ℝ) / 1 = 1 / s + 1 / t := by
    have hden : -2 + q.exponent.toReal * 2 ≠ 0 := by
      nlinarith [two_lt_toReal_of_two_lt_exponent q hq]
    dsimp [s, t, theta, twoDimNashThetaOfExponent]
    field_simp [hq0.ne', hden]
    ring_nf
    calc
      1 = (-2 + q.exponent.toReal * 2)⁻¹ *
          (-2 + q.exponent.toReal * 2) := (inv_mul_cancel₀ hden).symm
      _ = q.exponent.toReal * (-2 + q.exponent.toReal * 2)⁻¹ * 2 -
          (-2 + q.exponent.toReal * 2)⁻¹ * 2 := by ring
  have hholder := ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr
    (μ := mu) (f := F) (g := G) (p := (1 : ℝ)) (q := s) (r := t)
    zero_lt_one hs hsum (hf.enorm.pow_const _) (hf.enorm.pow_const _)
  have hpow := ENNReal.rpow_le_rpow hholder (by linarith : 0 ≤ 1 + theta)
  dsimp [F, G] at hpow
  norm_num at hpow
  convert hpow using 1
  · apply congrArg (fun z : ℝ≥0∞ ↦ z ^ (1 + theta))
    apply lintegral_congr
    intro x
    rw [← ENNReal.rpow_add_of_nonneg _ _
      (div_nonneg (mul_nonneg (by norm_num) htheta0.le) (by linarith))
      (div_nonneg (by norm_num) (by linarith))]
    congr 1
    field_simp
    ring
  · rw [ENNReal.mul_rpow_of_nonneg]
    rotate_left
    · linarith
    simp_rw [← ENNReal.rpow_mul]
    have hFs : 2 * theta / (1 + theta) * s = 1 := by
      dsimp [s]
      field_simp
    have hFout : s⁻¹ * (1 + theta) = 2 * theta := by
      dsimp [s]
      field_simp
    have hGt : 2 / (1 + theta) * t = q.exponent.toReal := by
      dsimp [t]
      field_simp
    have hGout : t⁻¹ * (1 + theta) = 2 / q.exponent.toReal := by
      dsimp [t]
      field_simp
    rw [hFs, hFout, hGt, hGout]
    simp only [ENNReal.rpow_one]
    simp only [theta]

/-- Exact `L¹`--`L²`--`L^q` interpolation for every finite `q > 2`. -/
theorem eLpNorm_two_dim_nash_interpolation
    {alpha : Type*} [MeasurableSpace alpha] (mu : Measure alpha)
    (f : alpha → ℝ) (q : FiniteLpExponent) (hq : (2 : ℝ≥0∞) < q.exponent)
    (hf : AEStronglyMeasurable f mu) :
    let theta := twoDimNashThetaOfExponent q
    eLpNorm f 2 mu ^ (2 * (1 + theta) : ℝ) ≤
      eLpNorm f 1 mu ^ (2 * theta : ℝ) *
        eLpNorm f q.exponent mu ^ (2 : ℝ) := by
  dsimp only
  let theta := twoDimNashThetaOfExponent q
  have h := lintegral_two_dim_nash_interpolation mu f q hq hf
  have hq0 : q.exponent ≠ 0 := ne_of_gt (zero_lt_one.trans q.one_lt)
  calc
    eLpNorm f 2 mu ^ (2 * (1 + theta) : ℝ) =
        (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 + theta) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hf) (by norm_num) (by norm_num)]
      simp only [ENNReal.toReal_ofNat, one_div]
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    _ ≤ (∫⁻ x, ‖f x‖ₑ ∂mu) ^ (2 * theta) *
        (∫⁻ x, ‖f x‖ₑ ^ q.exponent.toReal ∂mu) ^
          (2 / q.exponent.toReal) := h
    _ = eLpNorm f 1 mu ^ (2 * theta : ℝ) *
        eLpNorm f q.exponent mu ^ (2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hf) (by norm_num) (by norm_num),
        eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hf) hq0 q.lt_top.ne]
      congr 1
      · norm_num
      · rw [← ENNReal.rpow_mul]
        congr 1
        field_simp

/-- The two-dimensional `H¹ → L^q` cube estimate for every finite `q > 2`.
The exact finite-measure downgrade factor is `volume(cube)^(1/q)`. -/
theorem exists_cube_two_dim_lq_constant (q : FiniteLpExponent)
    (hq : (2 : ℝ≥0∞) < q.exponent) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (z : Vec 2) (L : ℝ), 0 < L → ∀ u : H1Function (axisCube z L),
        eLpNorm u.toFun q.exponent (volumeMeasureOn (axisCube z L)) ≤
          (C : ℝ≥0∞) *
            ((∑ i : Fin 2,
                eLpNorm (fun x ↦ u.grad x i) 2
                    (volumeMeasureOn (axisCube z L)) *
                  (volumeMeasureOn (axisCube z L)) Set.univ ^
                    (1 / q.exponent.toReal)) +
              ENNReal.ofReal L⁻¹ *
                (eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L)) *
                  (volumeMeasureOn (axisCube z L)) Set.univ ^
                    (1 / q.exponent.toReal))) := by
  let p := twoDimSobolevSourceExponent q hq
  have hpdim : p.exponent.toReal < 2 :=
    twoDimSobolevSourceExponent_toReal_lt_two q hq
  have hp2 : p.exponent ≤ 2 := twoDimSobolevSourceExponent_le_two q hq
  obtain ⟨C, hC, hSob⟩ :=
    cubeSobolevEmbedding_finiteLp (d := 2) (by omega) p hpdim
  refine ⟨C, hC, fun z L hL u ↦ ?_⟩
  let mu : Measure (Vec 2) := volumeMeasureOn (axisCube z L)
  let : IsFiniteMeasure mu := isFiniteMeasure_volumeMeasureOn_axisCube z L
  let up : W1pFunction (axisCube z L) p.exponent :=
    u.toW1pOfExponentLETwo p hp2
  have hSob' := hSob q (twoDimSobolevSourceExponent_relation q hq) z L hL up
  have hexponent : 1 / p.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal =
      1 / q.exponent.toReal := by
    have hrelation := twoDimSobolevSourceExponent_relation q hq
    dsimp [p]
    simpa only [one_div, ENNReal.toReal_ofNat] using hrelation.symm
  have hgrad : ∀ i : Fin 2,
      eLpNorm (fun x ↦ u.grad x i) p.exponent mu ≤
        eLpNorm (fun x ↦ u.grad x i) 2 mu *
          mu Set.univ ^ (1 / q.exponent.toReal) := by
    intro i
    have h := eLpNorm_finiteMeasure_downgrade_le p hp2 (fun x ↦ u.grad x i)
      (u.gradMemL2 i).aestronglyMeasurable
    rw [hexponent] at h
    exact h
  have hvalue : eLpNorm u.toFun p.exponent mu ≤
      eLpNorm u.toFun 2 mu * mu Set.univ ^ (1 / q.exponent.toReal) := by
    have h := eLpNorm_finiteMeasure_downgrade_le p hp2 u.toFun
      u.memL2.aestronglyMeasurable
    rw [hexponent] at h
    exact h
  change eLpNorm u.toFun q.exponent mu ≤ _
  calc
    eLpNorm u.toFun q.exponent mu ≤
        (C : ℝ≥0∞) *
          ((∑ i : Fin 2, eLpNorm (fun x ↦ u.grad x i) p.exponent mu) +
            ENNReal.ofReal L⁻¹ * eLpNorm u.toFun p.exponent mu) := by
      simpa [up, mu] using hSob'
    _ ≤ (C : ℝ≥0∞) *
          ((∑ i : Fin 2,
              eLpNorm (fun x ↦ u.grad x i) 2 mu *
                mu Set.univ ^ (1 / q.exponent.toReal)) +
            ENNReal.ofReal L⁻¹ *
              (eLpNorm u.toFun 2 mu *
                mu Set.univ ^ (1 / q.exponent.toReal))) := by
      gcongr with i
      exact hgrad i

/-- The general finite-exponent two-dimensional cube Nash inequality. -/
theorem exists_cube_two_dim_general_nash_constant (q : FiniteLpExponent)
    (hq : (2 : ℝ≥0∞) < q.exponent) :
    let theta := twoDimNashThetaOfExponent q
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (z : Vec 2) (L : ℝ), 0 < L → ∀ u : H1Function (axisCube z L),
        eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L)) ^
            (2 * (1 + theta) : ℝ) ≤
          eLpNorm u.toFun 1 (volumeMeasureOn (axisCube z L)) ^
              (2 * theta : ℝ) *
            (((C : ℝ≥0∞) *
              ((∑ i : Fin 2,
                  eLpNorm (fun x ↦ u.grad x i) 2
                      (volumeMeasureOn (axisCube z L)) *
                    (volumeMeasureOn (axisCube z L)) Set.univ ^
                      (1 / q.exponent.toReal)) +
                ENNReal.ofReal L⁻¹ *
                  (eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L)) *
                    (volumeMeasureOn (axisCube z L)) Set.univ ^
                      (1 / q.exponent.toReal)))) ^ (2 : ℝ)) := by
  dsimp only
  obtain ⟨C, hC, hSob⟩ := exists_cube_two_dim_lq_constant q hq
  refine ⟨C, hC, fun z L hL u ↦ ?_⟩
  calc
    eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L)) ^
        (2 * (1 + twoDimNashThetaOfExponent q) : ℝ) ≤
      eLpNorm u.toFun 1 (volumeMeasureOn (axisCube z L)) ^
          (2 * twoDimNashThetaOfExponent q : ℝ) *
        eLpNorm u.toFun q.exponent (volumeMeasureOn (axisCube z L)) ^ (2 : ℝ) :=
      eLpNorm_two_dim_nash_interpolation _ _ q hq u.memL2.aestronglyMeasurable
    _ ≤ _ := by
      gcongr
      exact hSob z L hL u

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section10Nash
