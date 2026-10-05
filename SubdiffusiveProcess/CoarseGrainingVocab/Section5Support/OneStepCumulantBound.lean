module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCumulant
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section

/-!
# Fourth-order bound for the one-step cutoff cumulant

This file proves the quantitative one-shell calculation in
`l.laplacian.corrector.energy`.  Negation
symmetry rewrites the first two exponential moments as hyperbolic-cosine
moments.  The remainder after the quadratic term is controlled directly by
the expectation-form `Gamma₂` observable from `(g2)`.
-/

open MeasureTheory ProbabilityTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Field (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialField d

private theorem exp_sub_one_le_mul_exp {x : ℝ} :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos x).le
  rw [← Real.exp_add] at hm
  norm_num at hm
  linarith

private theorem abs_log_sub_log_le_abs_sub_of_one_le
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hypos : 0 < y := zero_lt_one.trans_le hy
  rcases le_total x y with hxy | hyx
  · have hlogxy : Real.log x - Real.log y ≤ 0 :=
      sub_nonpos.mpr (Real.log_le_log hxpos hxy)
    rw [abs_of_nonpos hlogxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hlog := Real.log_le_sub_one_of_pos (div_pos hypos hxpos)
    rw [Real.log_div hypos.ne' hxpos.ne'] at hlog
    have hdiv : y / x - 1 ≤ y - x := by
      rw [div_sub_one hxpos.ne']
      exact (div_le_iff₀ hxpos).2 (by nlinarith)
    linarith
  · have hlogyx : 0 ≤ Real.log x - Real.log y :=
      sub_nonneg.mpr (Real.log_le_log hypos hyx)
    rw [abs_of_nonneg hlogyx, abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hlog := Real.log_le_sub_one_of_pos (div_pos hxpos hypos)
    rw [Real.log_div hxpos.ne' hypos.ne'] at hlog
    have hdiv : x / y - 1 ≤ x - y := by
      rw [div_sub_one hypos.ne']
      exact (div_le_iff₀ hypos).2 (by nlinarith)
    linarith

private theorem integral_exp_neg_mul_eq_exp_mul {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (t : ℝ) :
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (-t * g 0)
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure =
      ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (t * g 0)
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let F : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g => Real.exp (t * g 0)
  have hF : Measurable F :=
    (measurable_const.mul
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0)).exp
  have hneg : Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate mu0 = mu0 := by
    simpa [mu0] using congrArg ProbabilityMeasure.toMeasure M.G3.negation
  calc
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (-t * g 0) ∂mu0 =
        ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, F (_root_.SubdiffusiveProcess.Model.PotentialField.negate g) ∂mu0 := by
      apply integral_congr_ae
      filter_upwards with g
      simp [F]
    _ = ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, F g
        ∂Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate mu0 := by
      exact (integral_map
        _root_.SubdiffusiveProcess.Model.PotentialField.measurable_negate.aemeasurable
        hF.aestronglyMeasurable).symm
    _ = ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (t * g 0) ∂mu0 := by rw [hneg]

private theorem integrable_exp_neg_zeroPotential_at_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => Real.exp (-g 0))
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let F : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g => Real.exp (g 0)
  have hF : Measurable F :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).exp
  have hneg : Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate mu0 = mu0 := by
    simpa [mu0] using congrArg ProbabilityMeasure.toMeasure M.G3.negation
  have hmapped : Integrable F
      (Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate mu0) := by
    rw [hneg]
    exact M.G4.exponential_integrable
  have hcomp := (integrable_map_measure hF.aestronglyMeasurable
    _root_.SubdiffusiveProcess.Model.PotentialField.measurable_negate.aemeasurable).1 hmapped
  simpa [F, mu0, Function.comp_def] using hcomp

private theorem integrable_exp_neg_two_zeroPotential_at_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => Real.exp (-2 * g 0))
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let F : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g => Real.exp (2 * g 0)
  have hF : Measurable F :=
    (measurable_const.mul
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0)).exp
  have hneg : Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate mu0 = mu0 := by
    simpa [mu0] using congrArg ProbabilityMeasure.toMeasure M.G3.negation
  have hmapped : Integrable F
      (Measure.map _root_.SubdiffusiveProcess.Model.PotentialField.negate mu0) := by
    rw [hneg]
    exact integrable_exp_two_zeroPotential_at_zero M
  have hcomp := (integrable_map_measure hF.aestronglyMeasurable
    _root_.SubdiffusiveProcess.Model.PotentialField.measurable_negate.aemeasurable).1 hmapped
  simpa [F, mu0, Function.comp_def] using hcomp

/-- The first exponential moment is the corresponding cosh moment. -/
theorem integral_cosh_zeroPotential_at_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.cosh (g 0)
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure =
      ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g 0)
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  have hpos := M.G4.exponential_integrable
  have hneg := integrable_exp_neg_zeroPotential_at_zero M
  calc
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.cosh (g 0) ∂mu0 =
        (2 : ℝ)⁻¹ *
          (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g 0) ∂mu0 +
            ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (-g 0) ∂mu0) := by
      rw [← integral_add hpos hneg, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with g
      rw [Real.cosh_eq]
      ring_nf
    _ = ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g 0) ∂mu0 := by
      have hsymm : ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (-g 0) ∂mu0 =
          ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g 0) ∂mu0 := by
        simpa using integral_exp_neg_mul_eq_exp_mul M 1
      rw [hsymm]
      ring_nf

/-- The second exponential moment is the corresponding cosh moment. -/
theorem integral_cosh_two_zeroPotential_at_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.cosh (2 * g 0)
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure =
      oneShellExpTwoMoment M := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  have hpos := integrable_exp_two_zeroPotential_at_zero M
  have hneg := integrable_exp_neg_two_zeroPotential_at_zero M
  calc
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.cosh (2 * g 0) ∂mu0 =
        (2 : ℝ)⁻¹ *
          (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (2 * g 0) ∂mu0 +
            ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (-2 * g 0) ∂mu0) := by
      rw [← integral_add hpos hneg, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with g
      rw [Real.cosh_eq]
      ring_nf
    _ = ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (2 * g 0) ∂mu0 := by
      have hsymm : ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (-2 * g 0) ∂mu0 =
          ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (2 * g 0) ∂mu0 := by
        simpa using integral_exp_neg_mul_eq_exp_mul M 2
      rw [hsymm]
      ring_nf
    _ = oneShellExpTwoMoment M := rfl

private theorem cosh_sub_one_le_gamma_majorant
    {delta x : ℝ} (hdelta : 0 < delta) (hhalf : delta ≤ 1 / 2) :
    Real.cosh x - 1 ≤
      2 * delta ^ 2 * Real.exp ((delta⁻¹ * |x|) ^ 2) := by
  let W : ℝ := (delta⁻¹ * |x|) ^ 2
  have hW0 : 0 ≤ W := sq_nonneg _
  have hdeltaSq : delta ^ 2 ≤ 1 / 4 := by nlinarith
  have hxW : x ^ 2 = delta ^ 2 * W := by
    dsimp [W]
    field_simp [hdelta.ne']
    rw [sq_abs]
  have hexpRemainder : Real.exp (x ^ 2 / 2) - 1 ≤
      (x ^ 2 / 2) * Real.exp (x ^ 2 / 2) :=
    exp_sub_one_le_mul_exp
  have hWexp : W ≤ 4 * Real.exp (W / 4) := by
    have h := Real.le_inv_mul_exp W (by norm_num : (0 : ℝ) < 1 / 4)
    simpa [div_eq_mul_inv, mul_comm] using h
  have hexponent : x ^ 2 / 2 ≤ W / 8 := by
    rw [hxW]
    nlinarith
  have hexpLe : Real.exp (x ^ 2 / 2) ≤ Real.exp (W / 8) :=
    Real.exp_le_exp.mpr hexponent
  have hWquarter : 0 ≤ W / 4 := by positivity
  have hWeighth : 0 ≤ W / 8 := by positivity
  have hcombine : Real.exp (W / 4) * Real.exp (W / 8) ≤ Real.exp W := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc
    Real.cosh x - 1 ≤ Real.exp (x ^ 2 / 2) - 1 :=
      sub_le_sub_right (Real.cosh_le_exp_half_sq x) 1
    _ ≤ (x ^ 2 / 2) * Real.exp (x ^ 2 / 2) := hexpRemainder
    _ = (delta ^ 2 / 2) * W * Real.exp (x ^ 2 / 2) := by rw [hxW]; ring_nf
    _ ≤ (delta ^ 2 / 2) * (4 * Real.exp (W / 4)) * Real.exp (W / 8) := by
      gcongr
    _ ≤ 2 * delta ^ 2 * Real.exp W := by
      nlinarith [mul_le_mul_of_nonneg_left hcombine (sq_nonneg delta)]

private theorem cosh_sub_one_sq_le_gamma_majorant
    {delta x : ℝ} (hdelta : 0 < delta) (hhalf : delta ≤ 1 / 2) :
    (Real.cosh x - 1) ^ 2 ≤
      16 * delta ^ 4 * Real.exp ((delta⁻¹ * |x|) ^ 2) := by
  let W : ℝ := (delta⁻¹ * |x|) ^ 2
  have hinc0 : 0 ≤ Real.cosh x - 1 := sub_nonneg.mpr (Real.one_le_cosh x)
  have hfirst := cosh_sub_one_le_gamma_majorant hdelta hhalf (x := x)
  have hZ1 : 1 ≤ Real.exp W := Real.one_le_exp (sq_nonneg _)
  have hZ0 : 0 ≤ Real.exp W := (Real.exp_pos _).le
  have hsharper : Real.cosh x - 1 ≤
      4 * delta ^ 2 * Real.exp (W / 4) := by
    have hdeltaSq : delta ^ 2 ≤ 1 / 4 := by nlinarith
    have hxW : x ^ 2 = delta ^ 2 * W := by
      dsimp [W]
      field_simp [hdelta.ne']
      rw [sq_abs]
    have hrem : Real.exp (x ^ 2 / 2) - 1 ≤
        (x ^ 2 / 2) * Real.exp (x ^ 2 / 2) :=
      exp_sub_one_le_mul_exp
    have hWexp : W ≤ 8 * Real.exp (W / 8) := by
      have h := Real.le_inv_mul_exp W (by norm_num : (0 : ℝ) < 1 / 8)
      simpa [div_eq_mul_inv, mul_comm] using h
    have hexponent : x ^ 2 / 2 ≤ W / 8 := by rw [hxW]; nlinarith
    have hexpLe : Real.exp (x ^ 2 / 2) ≤ Real.exp (W / 8) :=
      Real.exp_le_exp.mpr hexponent
    calc
      Real.cosh x - 1 ≤ Real.exp (x ^ 2 / 2) - 1 :=
        sub_le_sub_right (Real.cosh_le_exp_half_sq x) 1
      _ ≤ (x ^ 2 / 2) * Real.exp (x ^ 2 / 2) := hrem
      _ = (delta ^ 2 / 2) * W * Real.exp (x ^ 2 / 2) := by rw [hxW]; ring_nf
      _ ≤ (delta ^ 2 / 2) * (8 * Real.exp (W / 8)) * Real.exp (W / 8) := by
        gcongr
      _ = 4 * delta ^ 2 * Real.exp (W / 4) := by
        have hexp : Real.exp (W / 8) * Real.exp (W / 8) =
            Real.exp (W / 4) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
        rw [show (delta ^ 2 / 2) * (8 * Real.exp (W / 8)) *
          Real.exp (W / 8) = 4 * delta ^ 2 *
            (Real.exp (W / 8) * Real.exp (W / 8)) by ring_nf, hexp]
  have hsq := pow_le_pow_left₀ hinc0 hsharper 2
  calc
    (Real.cosh x - 1) ^ 2 ≤
        (4 * delta ^ 2 * Real.exp (W / 4)) ^ 2 := hsq
    _ = 16 * delta ^ 4 * Real.exp (W / 2) := by
      have hexp : Real.exp (W / 4) ^ 2 = Real.exp (W / 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring_nf
      rw [mul_pow, mul_pow, hexp]
      ring_nf
    _ ≤ 16 * delta ^ 4 * Real.exp W := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (delta⁻¹ * |x|)]))
        (by positivity)

theorem integrable_cosh_sub_one_zeroPotential_at_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => Real.cosh (g 0) - 1)
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  have hpos := M.G4.exponential_integrable
  have hneg := integrable_exp_neg_zeroPotential_at_zero M
  have hcosh : Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => Real.cosh (g 0)) mu0 := by
    have h := (hpos.add hneg).const_mul (2 : ℝ)⁻¹
    refine h.congr ?_
    filter_upwards with g
    rw [Real.cosh_eq]
    simp only [Pi.add_apply]
    ring_nf
  exact hcosh.sub (integrable_const 1)

theorem integrable_cosh_sub_one_sq_zeroPotential_at_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => (Real.cosh (g 0) - 1) ^ 2)
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  have hpos := integrable_exp_two_zeroPotential_at_zero M
  have hneg := integrable_exp_neg_two_zeroPotential_at_zero M
  have hcoshTwo : Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => Real.cosh (2 * g 0)) mu0 := by
    have h := (hpos.add hneg).const_mul (2 : ℝ)⁻¹
    refine h.congr ?_
    filter_upwards with g
    rw [Real.cosh_eq]
    simp only [Pi.add_apply]
    ring_nf
  have hcosh : Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => Real.cosh (g 0)) mu0 := by
    have h := (integrable_cosh_sub_one_zeroPotential_at_zero M).add
      (integrable_const 1)
    refine h.congr ?_
    filter_upwards with g
    simp only [Pi.add_apply]
    ring_nf
  have hcombination : Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      (Real.cosh (2 * g 0) - 4 * Real.cosh (g 0) + 3) / 2) mu0 := by
    have h := ((hcoshTwo.sub (hcosh.const_mul 4)).add
      (integrable_const 3)).div_const 2
    refine h.congr ?_
    filter_upwards with g
    simp only [Pi.sub_apply, Pi.add_apply]
  convert hcombination using 1
  funext g
  rw [Real.cosh_two_mul, Real.sinh_sq]
  ring_nf

/-- The mean one-shell `cosh - 1` increment is of order `delta²`. -/
theorem integral_cosh_sub_one_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1)
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure ≤
      4 * M.delta ^ 2 := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let Z : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g =>
    Real.exp ((M.delta⁻¹ * |g 0|) ^ 2)
  have hZog := ogammaLE_abs_zeroPotential_at_zero M
  have hZint : Integrable Z mu0 := by
    simpa [Z, mu0, SubdiffusiveProcess.OGammaLE, max_eq_left, Real.rpow_natCast] using hZog.1
  have hZle : ∫ g, Z g ∂mu0 ≤ 2 := by
    simpa [Z, mu0, SubdiffusiveProcess.OGammaLE, max_eq_left, Real.rpow_natCast] using hZog.2
  have hmajorant : Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => 2 * M.delta ^ 2 * Z g) mu0 :=
    hZint.const_mul _
  have hint := integrable_cosh_sub_one_zeroPotential_at_zero M
  calc
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1) ∂mu0 ≤
        ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, 2 * M.delta ^ 2 * Z g ∂mu0 := by
      exact integral_mono hint hmajorant fun g =>
        cosh_sub_one_le_gamma_majorant M.shellPrefix.delta_pos
          M.shellPrefix.delta_le_half
    _ = 2 * M.delta ^ 2 * ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Z g ∂mu0 := by
      rw [integral_const_mul]
    _ ≤ 4 * M.delta ^ 2 := by nlinarith [sq_nonneg M.delta]

/-- The squared one-shell `cosh - 1` increment is of order `delta⁴`. -/
theorem integral_cosh_sub_one_sq_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1) ^ 2
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure ≤
      32 * M.delta ^ 4 := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let Z : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g => Real.exp ((M.delta⁻¹ * |g 0|) ^ 2)
  have hZog := ogammaLE_abs_zeroPotential_at_zero M
  have hZint : Integrable Z mu0 := by
    simpa [Z, mu0, SubdiffusiveProcess.OGammaLE, max_eq_left, Real.rpow_natCast] using hZog.1
  have hZle : ∫ g, Z g ∂mu0 ≤ 2 := by
    simpa [Z, mu0, SubdiffusiveProcess.OGammaLE, max_eq_left, Real.rpow_natCast] using hZog.2
  have hmajorant : Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => 16 * M.delta ^ 4 * Z g) mu0 :=
    hZint.const_mul _
  have hint := integrable_cosh_sub_one_sq_zeroPotential_at_zero M
  calc
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1) ^ 2 ∂mu0 ≤
        ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, 16 * M.delta ^ 4 * Z g ∂mu0 := by
      exact integral_mono hint hmajorant fun g =>
        cosh_sub_one_sq_le_gamma_majorant M.shellPrefix.delta_pos
          M.shellPrefix.delta_le_half
    _ = 16 * M.delta ^ 4 * ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Z g ∂mu0 := by
      rw [integral_const_mul]
    _ ≤ 32 * M.delta ^ 4 := by nlinarith [sq_nonneg (M.delta ^ 2)]

/-- Exact cosh decomposition of the raw second exponential moment. -/
theorem oneShellExpTwoMoment_eq_cosh_remainders {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    oneShellExpTwoMoment M =
      1 + 4 * (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1)
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) +
      2 * (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1) ^ 2
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let Y : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g => Real.cosh (g 0) - 1
  have hY : Integrable Y mu0 := integrable_cosh_sub_one_zeroPotential_at_zero M
  have hY2 : Integrable (fun g => (Y g) ^ 2) mu0 :=
    integrable_cosh_sub_one_sq_zeroPotential_at_zero M
  have hone : Integrable (fun _ : _root_.SubdiffusiveProcess.Model.PotentialField d => (1 : ℝ)) mu0 := integrable_const 1
  calc
    oneShellExpTwoMoment M = ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.cosh (2 * g 0) ∂mu0 :=
      (integral_cosh_two_zeroPotential_at_zero M).symm
    _ = ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (1 + 4 * Y g + 2 * (Y g) ^ 2) ∂mu0 := by
      apply integral_congr_ae
      filter_upwards with g
      dsimp [Y]
      rw [Real.cosh_two_mul, Real.sinh_sq]
      ring_nf
    _ = (∫ _g : _root_.SubdiffusiveProcess.Model.PotentialField d, 1 ∂mu0) +
        4 * (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Y g ∂mu0) +
        2 * (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Y g) ^ 2 ∂mu0) := by
      have houter := integral_add (hone.add (hY.const_mul 4)) (hY2.const_mul 2)
      have hinner := integral_add hone (hY.const_mul 4)
      change (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (1 + 4 * Y g) + 2 * (Y g) ^ 2 ∂mu0) =
        (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, 1 + 4 * Y g ∂mu0) +
          ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, 2 * (Y g) ^ 2 ∂mu0 at houter
      change (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, 1 + 4 * Y g ∂mu0) =
        (∫ _g : _root_.SubdiffusiveProcess.Model.PotentialField d, 1 ∂mu0) + ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, 4 * Y g ∂mu0 at hinner
      rw [houter, hinner, integral_const_mul, integral_const_mul]
    _ = 1 + 4 * (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1) ∂mu0) +
        2 * (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1) ^ 2 ∂mu0) := by
      rw [integral_const, probReal_univ, one_smul]

/-- Exact first-moment decomposition into its even remainder. -/
theorem integral_exp_zeroPotential_eq_one_add_cosh_remainder {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g 0)
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) =
      1 + ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1)
        ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  have hcosh : Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => Real.cosh (g 0)) mu0 := by
    have h := (integrable_cosh_sub_one_zeroPotential_at_zero M).add
      (integrable_const 1)
    refine h.congr ?_
    filter_upwards with g
    simp only [Pi.add_apply]
    ring
  calc
    ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g 0) ∂mu0 =
        ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.cosh (g 0) ∂mu0 :=
      (integral_cosh_zeroPotential_at_zero M).symm
    _ = ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, ((1 : ℝ) + (Real.cosh (g 0) - 1)) ∂mu0 := by
      apply integral_congr_ae
      filter_upwards with g
      ring
    _ = (∫ _g : _root_.SubdiffusiveProcess.Model.PotentialField d, 1 ∂mu0) +
        ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1) ∂mu0 := by
      rw [integral_add (integrable_const 1)
        (integrable_cosh_sub_one_zeroPotential_at_zero M)]
    _ = 1 + ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1) ∂mu0 := by
      rw [integral_const, probReal_univ, one_smul]

/-- The raw second exponential moment differs from the fourth power of the
first moment only at fourth order in the disorder amplitude. -/
theorem abs_oneShellExpTwoMoment_sub_firstMoment_pow_four_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    |oneShellExpTwoMoment M -
        (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g 0)
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ^ 4| ≤
      256 * M.delta ^ 4 := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let u : ℝ := ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1) ∂mu0
  let v : ℝ := ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1) ^ 2 ∂mu0
  have hu0 : 0 ≤ u := integral_nonneg fun g => sub_nonneg.mpr (Real.one_le_cosh _)
  have hv0 : 0 ≤ v := integral_nonneg fun g => sq_nonneg _
  have hu : u ≤ 4 * M.delta ^ 2 := integral_cosh_sub_one_le M
  have hv : v ≤ 32 * M.delta ^ 4 := integral_cosh_sub_one_sq_le M
  have hdeltaSq : M.delta ^ 2 ≤ 1 / 4 := by
    nlinarith [M.shellPrefix.delta_pos, M.shellPrefix.delta_le_half]
  have hu1 : u ≤ 1 := hu.trans (by nlinarith)
  have hu2 : u ^ 2 ≤ 16 * M.delta ^ 4 := by
    have h := pow_le_pow_left₀ hu0 hu 2
    nlinarith
  have hu3 : u ^ 3 ≤ u ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  have hu4 : u ^ 4 ≤ u ^ 2 := by
    have hu2u : u ^ 2 ≤ u := by
      have h := mul_le_mul_of_nonneg_left hu1 hu0
      nlinarith
    have h := pow_le_pow_left₀ (sq_nonneg u) hu2u 2
    nlinarith
  have hsecond : oneShellExpTwoMoment M = 1 + 4 * u + 2 * v := by
    simpa [u, v, mu0] using oneShellExpTwoMoment_eq_cosh_remainders M
  have hfirst : (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g 0) ∂mu0) = 1 + u := by
    simpa [u, mu0] using integral_exp_zeroPotential_eq_one_add_cosh_remainder M
  rw [hsecond, hfirst, abs_le]
  constructor <;> nlinarith [sq_nonneg (M.delta ^ 2)]

/-- The source's fourth-order one-shell cumulant estimate. -/
theorem abs_oneStepCumulant_sub_two_tauSq_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    |oneStepCumulant M - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P| ≤
      256 * M.delta ^ 4 := by
  let mu0 := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let A : ℝ := ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g 0) ∂mu0
  let B : ℝ := oneShellExpTwoMoment M
  let u : ℝ := ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1) ∂mu0
  let v : ℝ := ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, (Real.cosh (g 0) - 1) ^ 2 ∂mu0
  have hu0 : 0 ≤ u := integral_nonneg fun g => sub_nonneg.mpr (Real.one_le_cosh _)
  have hv0 : 0 ≤ v := integral_nonneg fun g => sq_nonneg _
  have hA : A = 1 + u := by
    simpa [A, u, mu0] using integral_exp_zeroPotential_eq_one_add_cosh_remainder M
  have hB : B = 1 + 4 * u + 2 * v := by
    simpa [B, u, v, mu0] using oneShellExpTwoMoment_eq_cosh_remainders M
  have hAone : 1 ≤ A := by rw [hA]; linarith
  have hBone : 1 ≤ B := by rw [hB]; linarith
  have hApowOne : 1 ≤ A ^ 4 := by nlinarith [sq_nonneg (A ^ 2 - 1)]
  have hApos : 0 < A := zero_lt_one.trans_le hAone
  have hAexp : A = Real.exp (_root_.SubdiffusiveProcess.Model.tauSq M.P) := by
    simpa [A, mu0, _root_.SubdiffusiveProcess.Model.tauSq] using (Real.exp_log hApos).symm
  have hlogApow : Real.log (A ^ 4) =
      4 * _root_.SubdiffusiveProcess.Model.tauSq M.P := by
    rw [hAexp, ← Real.exp_nat_mul, Real.log_exp]
    norm_num
  have hlog := abs_log_sub_log_le_abs_sub_of_one_le hBone hApowOne
  have hmoment : |B - A ^ 4| ≤ 256 * M.delta ^ 4 := by
    simpa [A, B, mu0] using abs_oneShellExpTwoMoment_sub_firstMoment_pow_four_le M
  have hrewrite : oneStepCumulant M - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P =
      Real.log B - Real.log (A ^ 4) := by
    rw [hlogApow]
    simp only [oneStepCumulant, B]
    ring
  rw [hrewrite]
  exact hlog.trans hmoment

/-- Logarithmic second-moment expansion for an arbitrary suffix length. -/
theorem abs_log_oneShellCentered_pow_sub_two_tauSq_mul_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (h : ℕ) :
    |Real.log ((oneShellCenteredExpTwoMoment M) ^ h) -
        2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ)| ≤
      256 * M.delta ^ 4 * (h : ℝ) := by
  have hlog : Real.log ((oneShellCenteredExpTwoMoment M) ^ h) =
      (h : ℝ) * oneStepCumulant M := by
    rw [oneShellCenteredExpTwoMoment_eq_exp_oneStepCumulant,
      ← Real.exp_nat_mul, Real.log_exp]
  rw [hlog]
  have hrewrite :
      (h : ℝ) * oneStepCumulant M -
          2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) =
        (h : ℝ) *
          (oneStepCumulant M - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg (Nat.cast_nonneg h)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
    (abs_oneStepCumulant_sub_two_tauSq_le M) (Nat.cast_nonneg h)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
