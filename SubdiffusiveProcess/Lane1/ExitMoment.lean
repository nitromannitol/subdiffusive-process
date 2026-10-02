import SubdiffusiveProcess.Main.DiffusionPath
import MarkovProcess.Path.ExitTime
import MarkovProcess.Path.ExitTimeShift
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The discounted survival integral and the mean exit time

The killed discounted resolvent applied to the constant source is the integral
of `e^{-lambda s}` over the survival interval of a path.  As the discount
vanishes that quantity increases to the exit time itself, which is how a bound
on the resolvents at every positive discount becomes a bound on the mean exit
time.
-/

open MeasureTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess

/-- The discounted length of the survival interval `{s > 0 | s < tau}`. -/
def survivalIntegral (lam : ℝ) (tau : ℝ≥0∞) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Set.indicator {s : ℝ | ENNReal.ofReal s < tau} (fun s => Real.exp (-lam * s)) t

theorem measurableSet_survival (tau : ℝ≥0∞) :
    MeasurableSet {s : ℝ | ENNReal.ofReal s < tau} :=
  measurableSet_lt ENNReal.measurable_ofReal measurable_const

theorem survivalIntegral_eq_setIntegral (lam : ℝ) (tau : ℝ≥0∞) :
    survivalIntegral lam tau
      = ∫ t in ({s : ℝ | ENNReal.ofReal s < tau} ∩ Set.Ioi 0),
          Real.exp (-lam * t) := by
  rw [survivalIntegral, integral_indicator (measurableSet_survival tau),
    Measure.restrict_restrict (measurableSet_survival tau)]

theorem survivalIntegral_top (lam : ℝ) :
    survivalIntegral lam ⊤ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) := by
  have hset : {s : ℝ | ENNReal.ofReal s < (⊤ : ℝ≥0∞)} ∩ Set.Ioi 0
      = Set.Ioi (0 : ℝ) := by
    have h := ContinuousPath.survivalSet (⊤ : ℝ≥0∞)
    rw [if_pos rfl] at h
    exact h
  rw [survivalIntegral_eq_setIntegral, hset]

theorem survivalIntegral_of_ne_top (lam : ℝ) {tau : ℝ≥0∞} (htau : tau ≠ ⊤) :
    survivalIntegral lam tau
      = ∫ t in Set.Ioo (0 : ℝ) tau.toReal, Real.exp (-lam * t) := by
  have hset : {s : ℝ | ENNReal.ofReal s < tau} ∩ Set.Ioi 0
      = Set.Ioo (0 : ℝ) tau.toReal := by
    have h := ContinuousPath.survivalSet tau
    rw [if_neg htau] at h
    exact h
  rw [survivalIntegral_eq_setIntegral, hset]

theorem integrableOn_exp_neg_Ioo (lam : ℝ) (T : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-lam * t)) (Set.Ioo 0 T) := by
  have hcont : Continuous fun t : ℝ => Real.exp (-lam * t) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
    Set.Ioo_subset_Icc_self

theorem survivalIntegral_nonneg (lam : ℝ) (tau : ℝ≥0∞) :
    0 ≤ survivalIntegral lam tau := by
  rw [survivalIntegral_eq_setIntegral]
  exact setIntegral_nonneg
    ((measurableSet_survival tau).inter measurableSet_Ioi)
    fun x _ => (Real.exp_pos _).le

/-- The discounted survival integral never exceeds the horizon. -/
theorem ofReal_survivalIntegral_le {lam : ℝ} (hlam : 0 ≤ lam) (tau : ℝ≥0∞) :
    ENNReal.ofReal (survivalIntegral lam tau) ≤ tau := by
  by_cases htau : tau = ⊤
  · simp [htau]
  · rw [survivalIntegral_of_ne_top lam htau]
    have hT : (0 : ℝ) ≤ tau.toReal := ENNReal.toReal_nonneg
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 tau.toReal) := by
      refine integrableOn_const ?_
      simpa using (measure_Ioo_lt_top (a := (0 : ℝ)) (b := tau.toReal)).ne
    have hle : ∫ t in Set.Ioo (0 : ℝ) tau.toReal, Real.exp (-lam * t)
        ≤ tau.toReal := by
      have hmono : ∫ t in Set.Ioo (0 : ℝ) tau.toReal, Real.exp (-lam * t)
          ≤ ∫ _t in Set.Ioo (0 : ℝ) tau.toReal, (1 : ℝ) := by
        refine setIntegral_mono_on (integrableOn_exp_neg_Ioo lam tau.toReal)
          hconst measurableSet_Ioo fun x hx => ?_
        have : -lam * x ≤ 0 := by nlinarith [hx.1]
        simpa using Real.exp_le_one_iff.mpr this
      have hval : ∫ _t in Set.Ioo (0 : ℝ) tau.toReal, (1 : ℝ) = tau.toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
          Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hT]
      linarith [hmono, hval.le, hval.ge]
    calc ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) tau.toReal, Real.exp (-lam * t))
        ≤ ENNReal.ofReal tau.toReal := ENNReal.ofReal_le_ofReal hle
      _ = tau := ENNReal.ofReal_toReal htau

/-- Lowering the discount raises the integral. -/
theorem survivalIntegral_mono {lam1 lam2 : ℝ} (h1 : 0 < lam1) (h12 : lam1 ≤ lam2)
    (tau : ℝ≥0∞) : survivalIntegral lam2 tau ≤ survivalIntegral lam1 tau := by
  have h2 : 0 < lam2 := lt_of_lt_of_le h1 h12
  by_cases htau : tau = ⊤
  · subst htau
    rw [survivalIntegral_top, survivalIntegral_top]
    refine setIntegral_mono_on (exp_neg_integrableOn_Ioi 0 h2)
      (exp_neg_integrableOn_Ioi 0 h1) measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [survivalIntegral_of_ne_top lam2 htau, survivalIntegral_of_ne_top lam1 htau]
    refine setIntegral_mono_on (integrableOn_exp_neg_Ioo lam2 tau.toReal)
      (integrableOn_exp_neg_Ioo lam1 tau.toReal) measurableSet_Ioo fun x hx => ?_
    exact Real.exp_le_exp.mpr (by nlinarith [hx.1])

/-- At an infinite horizon the discounted survival integral is the reciprocal
of the discount. -/
theorem survivalIntegral_top_eq {lam : ℝ} (hlam : 0 < lam) :
    survivalIntegral lam ⊤ = lam⁻¹ := by
  rw [survivalIntegral_top]
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 0 hlam
  simp only [mul_zero, smul_eq_mul] at h
  rw [integral_exp_neg_Ioi_zero] at h
  simp only [mul_one] at h
  simpa only [neg_mul] using h

/-- The vanishing sequence of discounts used to recover the exit time. -/
def discountSeq (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem discountSeq_pos (k : ℕ) : 0 < discountSeq k := by
  unfold discountSeq
  positivity

theorem discountSeq_antitone : Antitone discountSeq := by
  intro k l hkl
  unfold discountSeq
  apply one_div_le_one_div_of_le
  · positivity
  · have : (k : ℝ) ≤ (l : ℝ) := Nat.cast_le.mpr hkl
    linarith

theorem tendsto_discountSeq : Tendsto discountSeq atTop (nhds 0) := by
  unfold discountSeq
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem monotone_survivalIntegral (tau : ℝ≥0∞) :
    Monotone (fun k : ℕ => survivalIntegral (discountSeq k) tau) := by
  intro k l hkl
  exact survivalIntegral_mono (discountSeq_pos l) (discountSeq_antitone hkl) tau

/-- As the discount vanishes the discounted survival integral recovers the
horizon. -/
theorem tendsto_ofReal_survivalIntegral (tau : ℝ≥0∞) :
    Tendsto (fun k : ℕ => ENNReal.ofReal (survivalIntegral (discountSeq k) tau))
      atTop (nhds tau) := by
  by_cases htau : tau = ⊤
  · subst htau
    rw [ENNReal.tendsto_nhds_top_iff_nnreal]
    intro y
    have hval : ∀ k : ℕ, survivalIntegral (discountSeq k) ⊤ = (k : ℝ) + 1 := by
      intro k
      rw [survivalIntegral_top_eq (discountSeq_pos k)]
      unfold discountSeq
      rw [one_div, inv_inv]
    obtain ⟨n, hn⟩ := exists_nat_gt ((y : ℝ) + 1)
    refine Filter.eventually_atTop.mpr ⟨n, fun k hk => ?_⟩
    rw [hval k]
    have hyk : (y : ℝ) < (k : ℝ) + 1 := by
      have : (n : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
      linarith
    calc (y : ℝ≥0∞) = ENNReal.ofReal (y : ℝ) := by
          simp [ENNReal.ofReal_coe_nnreal]
      _ < ENNReal.ofReal ((k : ℝ) + 1) := by
          refine (ENNReal.ofReal_lt_ofReal_iff ?_).mpr hyk
          positivity
  · set T : ℝ := tau.toReal with hT
    have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
    have hbound : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 T) := by
      refine integrableOn_const ?_
      simpa using (measure_Ioo_lt_top (a := (0 : ℝ)) (b := T)).ne
    have hdom : Tendsto
        (fun k : ℕ => ∫ t in Set.Ioo (0 : ℝ) T, Real.exp (-discountSeq k * t))
        atTop (nhds (∫ _t in Set.Ioo (0 : ℝ) T, (1 : ℝ))) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun k => ((Real.continuous_exp.comp
          (continuous_const.mul continuous_id)).aestronglyMeasurable)) hbound
        (fun k => ?_) ?_
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
        have ht0 : (0 : ℝ) < t := ht.1
        have : -discountSeq k * t ≤ 0 := by
          have := (discountSeq_pos k).le
          nlinarith
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr this
      · filter_upwards with t
        have hmul : Tendsto (fun k : ℕ => -discountSeq k * t) atTop (nhds 0) := by
          have := tendsto_discountSeq.neg
          simpa using this.mul_const t
        simpa using (Real.continuous_exp.tendsto 0).comp hmul
    have hval : ∫ _t in Set.Ioo (0 : ℝ) T, (1 : ℝ) = T := by
      rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
        Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hT0]
    have hreal : Tendsto
        (fun k : ℕ => survivalIntegral (discountSeq k) tau) atTop (nhds T) := by
      refine (hval ▸ hdom).congr fun k => ?_
      exact (survivalIntegral_of_ne_top (discountSeq k) htau).symm
    have := (ENNReal.tendsto_ofReal hreal)
    rwa [hT, ENNReal.ofReal_toReal htau] at this

/-- The exit time is the supremum of the discounted survival integrals. -/
theorem iSup_ofReal_survivalIntegral (tau : ℝ≥0∞) :
    ⨆ k : ℕ, ENNReal.ofReal (survivalIntegral (discountSeq k) tau) = tau := by
  have hmono : Monotone
      (fun k : ℕ => ENNReal.ofReal (survivalIntegral (discountSeq k) tau)) := by
    intro k l hkl
    exact ENNReal.ofReal_le_ofReal (monotone_survivalIntegral tau hkl)
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono)
    (tendsto_ofReal_survivalIntegral tau)

/-- Leaving a smaller set happens no later. -/
theorem exitTime_mono {alpha : Type*} [PseudoMetricSpace alpha]
    {U V : Set alpha} (h : U ⊆ V) (path : ContinuousPath alpha) :
    ContinuousPath.exitTime U path ≤ ContinuousPath.exitTime V path := by
  refine sInf_le_sInf fun s hs => ?_
  obtain ⟨t, hst, htV⟩ := hs
  exact ⟨t, hst, fun htU => htV (h htU)⟩

/-- The closed form of the discounted survival integral. -/
theorem survivalIntegral_eq_formula {lam : ℝ} (hlam : 0 < lam) (tau : ℝ≥0∞) :
    survivalIntegral lam tau
      = (1 - (if tau = ⊤ then 0 else Real.exp (-lam * tau.toReal))) / lam := by
  by_cases htau : tau = ⊤
  · subst htau
    rw [survivalIntegral_top_eq hlam, if_pos rfl, sub_zero, one_div]
  · rw [survivalIntegral_of_ne_top lam htau, if_neg htau]
    set T : ℝ := tau.toReal with hT
    have hT0 : (0 : ℝ) ≤ T := ENNReal.toReal_nonneg
    have hIoo : ∫ t in Set.Ioo (0 : ℝ) T, Real.exp (-lam * t)
        = ∫ t in (0 : ℝ)..T, Real.exp (-lam * t) := by
      rw [intervalIntegral.integral_of_le hT0, ← integral_Ioc_eq_integral_Ioo]
    rw [hIoo]
    have hcomp : ∫ t in (0 : ℝ)..T, Real.exp (-lam * t)
        = lam⁻¹ • ∫ y in (lam * 0)..(lam * T), Real.exp (-y) := by
      have h := intervalIntegral.integral_comp_mul_left
        (a := (0 : ℝ)) (b := T) (fun y : ℝ => Real.exp (-y)) (ne_of_gt hlam)
      simpa only [neg_mul] using h
    rw [hcomp, mul_zero]
    have hneg : ∫ y in (0 : ℝ)..(lam * T), Real.exp (-y)
        = ∫ y in (-(lam * T))..0, Real.exp y := by
      simpa using intervalIntegral.integral_comp_neg
        (a := (0 : ℝ)) (b := lam * T) (fun y : ℝ => Real.exp y)
    rw [hneg, integral_exp, Real.exp_zero, smul_eq_mul]
    have : -(lam * T) = -lam * T := by ring
    rw [this]
    field_simp

/-- The discounted survival integral increases with the horizon. -/
theorem measurable_survivalIntegral {lam : ℝ} (hlam : 0 < lam) :
    Measurable (survivalIntegral lam) := by
  have hcongr : survivalIntegral lam = fun tau : ℝ≥0∞ =>
      (1 - (if tau = ⊤ then 0 else Real.exp (-lam * tau.toReal))) / lam := by
    funext tau
    exact survivalIntegral_eq_formula hlam tau
  rw [hcongr]
  refine Measurable.div_const (Measurable.const_sub ?_ 1) lam
  refine Measurable.ite (measurableSet_singleton (⊤ : ℝ≥0∞)) measurable_const ?_
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
    ENNReal.measurable_toReal

/-- The discounted survival integral is at most the reciprocal discount. -/
theorem survivalIntegral_le_inv {lam : ℝ} (hlam : 0 < lam) (tau : ℝ≥0∞) :
    survivalIntegral lam tau ≤ lam⁻¹ := by
  rw [survivalIntegral_eq_formula hlam tau, div_le_iff₀ hlam]
  have hsub : (1 : ℝ) - (if tau = ⊤ then 0 else Real.exp (-lam * tau.toReal))
      ≤ 1 := by
    by_cases htau : tau = ⊤
    · simp [htau]
    · rw [if_neg htau]
      have := (Real.exp_pos (-lam * tau.toReal)).le
      linarith
  calc (1 : ℝ) - (if tau = ⊤ then 0 else Real.exp (-lam * tau.toReal)) ≤ 1 := hsub
    _ = lam⁻¹ * lam := by field_simp


end SubdiffusiveProcess