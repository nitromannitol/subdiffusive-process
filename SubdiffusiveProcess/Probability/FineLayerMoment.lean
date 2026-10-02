import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments

open MeasureTheory ProbabilityTheory Homogenization
noncomputable section

namespace SubdiffusiveProcess

theorem fineLayer_exp_moment_le
    {d : ℕ} (t : ℝ)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : Vec d)
    (ht : |t| * M.delta ≤ 1) :
    Integrable
        (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d ↦ Real.exp (t * g x))
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ∧
      ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (t * g x)
          ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ≤
        Real.exp ((Real.log 2 / 2) * t ^ 2 * M.delta ^ 2) := by
  let mu0 := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => g 0
  let Z : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g =>
    Real.exp ((M.delta⁻¹ * |X g|) ^ (2 : ℕ))
  let r : ℝ := t ^ 2 * M.delta ^ 2 / 2
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have ht_abs : |t| * M.delta ≤ 1 := ht
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    have hprod : (|t| * M.delta) ^ 2 ≤ 1 := by
      have haux : 0 ≤ (1 - |t| * M.delta) * (1 + |t| * M.delta) := by
        exact mul_nonneg (sub_nonneg.mpr ht_abs) (by positivity)
      nlinarith
    have hsq : t ^ 2 * M.delta ^ 2 ≤ 1 := by
      calc
        t ^ 2 * M.delta ^ 2 = (|t| * M.delta) ^ 2 := by
          rw [← sq_abs t]
          ring
        _ ≤ 1 := hprod
    nlinarith
  have hZog := SubdiffusiveProcess.CoarseGrainingVocab.ogammaLE_abs_zeroPotential_at_zero M
  have hZint : Integrable Z mu0 := by
    simpa [Z, X, mu0, SubdiffusiveProcess.OGammaLE, max_eq_left,
      Real.rpow_natCast] using hZog.1
  have hZle : ∫ g, Z g ∂mu0 ≤ 2 := by
    simpa [Z, X, mu0, SubdiffusiveProcess.OGammaLE, max_eq_left,
      Real.rpow_natCast] using hZog.2
  have hZone : ∀ g, 1 ≤ Z g := by
    intro g
    exact Real.one_le_exp (sq_nonneg _)
  have hZr_le : ∀ g, Z g ^ r ≤ Z g := by
    intro g
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (hZone g) hr1
  have hZr_meas : Measurable (fun g => Z g ^ r) := by
    have hZmeas : Measurable Z := by
      dsimp [Z, X]
      have habs : Measurable
          (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => |g 0|) := by
        simpa only [Real.norm_eq_abs] using
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval (0 : Vec d)).norm
      exact (measurable_const.mul habs).pow_const 2 |>.exp
    exact hZmeas.pow measurable_const
  have hZrint : Integrable (fun g => Z g ^ r) mu0 := by
    refine hZint.mono' hZr_meas.aestronglyMeasurable ?_
    filter_upwards with g
    calc
      ‖Z g ^ r‖ = Z g ^ r :=
        Real.norm_of_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _)
      _ ≤ Z g := hZr_le g
  have hJensen : ∫ g, Z g ^ r ∂mu0 ≤ (∫ g, Z g ∂mu0) ^ r := by
    exact (Real.concaveOn_rpow hr0 hr1).le_map_integral
      (Real.continuous_rpow_const hr0).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun g => (Real.exp_pos _).le)
      hZint hZrint
  have hIntZ_nonneg : 0 ≤ ∫ g, Z g ∂mu0 :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hJensenTwo : ∫ g, Z g ^ r ∂mu0 ≤ (2 : ℝ) ^ r := by
    exact hJensen.trans (Real.rpow_le_rpow hIntZ_nonneg hZle hr0)
  let expT : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ :=
    fun g => Real.exp (t * X g)
  let expNegT : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ :=
    fun g => Real.exp (-(t * X g))
  have hexpTmeas : Measurable expT := by
    exact (measurable_const.mul
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval 0)).exp
  have hexpNegTmeas : Measurable expNegT := by
    exact (measurable_const.mul
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval 0)).neg.exp
  have hcosh_le : ∀ g, Real.cosh (t * X g) ≤ Z g ^ r := by
    intro g
    calc
      Real.cosh (t * X g) ≤ Real.exp ((t * X g) ^ 2 / 2) :=
        Real.cosh_le_exp_half_sq _
      _ = Z g ^ r := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        dsimp [Z, r]
        congr 1
        field_simp [hdelta.ne']
        rw [sq_abs]
  have hcosh_meas : Measurable
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => Real.cosh (t * X g)) := by
    exact Real.continuous_cosh.measurable.comp
      (measurable_const.mul
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval 0))
  have hcosh_int : Integrable (fun g => Real.cosh (t * X g)) mu0 := by
    refine hZrint.mono' hcosh_meas.aestronglyMeasurable ?_
    filter_upwards with g
    rw [Real.norm_of_nonneg (Real.cosh_pos _).le]
    exact hcosh_le g
  have htwo_cosh_int : Integrable
      (fun g => 2 * Real.cosh (t * X g)) mu0 := hcosh_int.const_mul 2
  have hexpTint : Integrable expT mu0 := by
    refine htwo_cosh_int.mono' hexpTmeas.aestronglyMeasurable ?_
    filter_upwards with g
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      Real.exp (t * X g) ≤ Real.exp (t * X g) + Real.exp (-(t * X g)) :=
        le_add_of_nonneg_right (Real.exp_pos _).le
      _ = 2 * Real.cosh (t * X g) := by
        rw [Real.cosh_eq]
        ring
  have hexpNegTint : Integrable expNegT mu0 := by
    refine htwo_cosh_int.mono' hexpNegTmeas.aestronglyMeasurable ?_
    filter_upwards with g
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      Real.exp (-(t * X g)) ≤ Real.exp (t * X g) + Real.exp (-(t * X g)) :=
        le_add_of_nonneg_left (Real.exp_pos _).le
      _ = 2 * Real.cosh (t * X g) := by
        rw [Real.cosh_eq]
        ring
  have hneg : Measure.map SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate mu0 = mu0 := by
    simpa [mu0] using congrArg ProbabilityMeasure.toMeasure M.G3.negation
  have hexp_symm : ∫ g, expNegT g ∂mu0 = ∫ g, expT g ∂mu0 := by
    calc
      ∫ g, expNegT g ∂mu0 =
          ∫ g, expT (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate g) ∂mu0 := by
        apply integral_congr_ae
        filter_upwards with g
        simp [expNegT, expT, X]
      _ = ∫ z, expT z
          ∂Measure.map SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate mu0 := by
        exact (integral_map
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_negate.aemeasurable
          hexpTmeas.aestronglyMeasurable).symm
      _ = ∫ g, expT g ∂mu0 := by rw [hneg]
  have hcosh_eq : ∫ g, Real.cosh (t * X g) ∂mu0 = ∫ g, expT g ∂mu0 := by
    calc
      ∫ g, Real.cosh (t * X g) ∂mu0 =
          (2 : ℝ)⁻¹ * (∫ g, expT g ∂mu0 + ∫ g, expNegT g ∂mu0) := by
        rw [← integral_add hexpTint hexpNegTint, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with g
        rw [Real.cosh_eq]
        simp [expT, expNegT, X]
        ring
      _ = ∫ g, expT g ∂mu0 := by rw [hexp_symm]; ring
  have horigin :
      Integrable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
        Real.exp (t * g 0)) mu0 ∧
        ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (t * g 0)
            ∂mu0 ≤ (2 : ℝ) ^ r := by
    constructor
    · simpa [expT, X] using hexpTint
    · calc
        ∫ g, Real.exp (t * g 0) ∂mu0 = ∫ g, expT g ∂mu0 := by rfl
        _ = ∫ g, Real.cosh (t * X g) ∂mu0 := hcosh_eq.symm
        _ ≤ ∫ g, Z g ^ r ∂mu0 := integral_mono hcosh_int hZrint hcosh_le
        _ ≤ (2 : ℝ) ^ r := hJensenTwo
  let T := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate x
  have hstationary : Measure.map T mu0 = mu0 := by
    simpa [T] using M.G1.stationary x
  have horigin_meas : Measurable
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => Real.exp (t * g 0)) := by
    exact (measurable_const.mul
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval 0)).exp
  have hmapint : Integrable
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => Real.exp (t * g 0))
      (Measure.map T mu0) := by
    rw [hstationary]
    exact horigin.1
  have hcompint := (integrable_map_measure horigin_meas.aestronglyMeasurable
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate x).aemeasurable).1 hmapint
  have hfinal_int : Integrable
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => Real.exp (t * g x)) mu0 := by
    simpa [T, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply, Function.comp_def] using
      hcompint
  have hfinal_le :
      ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (t * g x) ∂mu0 ≤
        (2 : ℝ) ^ r := by
    calc
      ∫ g, Real.exp (t * g x) ∂mu0 =
          ∫ g, Real.exp (t * (T g) 0) ∂mu0 := by
            apply integral_congr_ae
            filter_upwards with g
            simp [T, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply]
      _ = ∫ g, Real.exp (t * g 0)
          ∂Measure.map T mu0 := by
            exact (integral_map
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate x).aemeasurable
              horigin_meas.aestronglyMeasurable).symm
      _ = ∫ g, Real.exp (t * g 0) ∂mu0 := by rw [hstationary]
      _ ≤ (2 : ℝ) ^ r := horigin.2
  refine ⟨hfinal_int, ?_⟩
  calc
    ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (t * g x) ∂mu0 ≤
        (2 : ℝ) ^ r := hfinal_le
    _ = Real.exp ((Real.log 2 / 2) * t ^ 2 * M.delta ^ 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      dsimp [r]
      ring

end SubdiffusiveProcess
