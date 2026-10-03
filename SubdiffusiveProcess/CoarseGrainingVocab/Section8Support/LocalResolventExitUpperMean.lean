module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpperTail
public import Mathlib.MeasureTheory.Integral.ExpDecay

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper

variable {d : ℕ}

/-! ### The exponential integral -/

/-- The exponential integral on the positive half line. -/
theorem integral_Ioi_exp_neg_mul {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(b * t)) = b⁻¹ := by
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun u : ℝ => -Real.exp (-(b * u)) / b) (Real.exp (-(b * t))) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => -(b * u)) (-b) t := by
      simpa only [Pi.neg_apply, id_eq, mul_one] using! ((hasDerivAt_id t).const_mul b).neg
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-(b * u))) (Real.exp (-(b * t)) * (-b)) t :=
      h1.exp
    have h3 := h2.neg.div_const b
    convert h3 using 1
    field_simp
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(b * t))) (Ioi 0) := by
    simpa only [neg_mul] using! exp_neg_integrableOn_Ioi 0 hb
  have htend : Tendsto (fun u : ℝ => -Real.exp (-(b * u)) / b) atTop (𝓝 0) := by
    have hexp : Tendsto (fun u : ℝ => Real.exp (-(b * u))) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      simpa using! tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 hb)
    simpa using! (hexp.neg.div_const b)
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [hval, mul_zero, neg_zero, Real.exp_zero]
  ring

/-- The lower integral of an exponentially decaying bound. -/
theorem lintegral_Ioi_ofReal_exp_neg_mul {K b : ℝ} (hK : 0 ≤ K) (hb : 0 < b) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (K * Real.exp (-(b * t))))
      = ENNReal.ofReal (K * b⁻¹) := by
  have hint : IntegrableOn (fun t : ℝ => K * Real.exp (-(b * t))) (Ioi 0) := by
    have h := (exp_neg_integrableOn_Ioi (0 : ℝ) hb).const_mul K
    simpa only [neg_mul, IntegrableOn] using! h
  have hnn : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ K * Real.exp (-(b * t)) :=
    Filter.Eventually.of_forall fun t => mul_nonneg hK (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
    integral_Ioi_exp_neg_mul hb]

/-! ### The layer-cake formula for the exit time -/

/-- The Lebesgue measure of the times before an extended threshold. -/
theorem volume_setOf_ofReal_lt (tau : ℝ≥0∞) :
    volume {t : ℝ | 0 < t ∧ ENNReal.ofReal t < tau} = tau := by
  rcases eq_or_ne tau ∞ with h | h
  · have hset : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < tau} = Ioi 0 := by
      ext t
      simp [h, ENNReal.ofReal_lt_top]
    rw [hset, h, Real.volume_Ioi]
  · have hset : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < tau} = Ioo 0 tau.toReal := by
      ext t
      constructor
      · rintro ⟨ht, hlt⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le h).mp hlt⟩
      · rintro ⟨ht, hlt⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le h).mpr hlt⟩
    rw [hset, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal h]

/-- **The layer-cake formula for the mean exit time.** -/
theorem meanExit_eq_lintegral_survival (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpen U) (x : Vec d) :
    meanExit law U x
      = ∫⁻ t in Ioi (0 : ℝ), law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w} := by
  have hτ : Measurable (fun w : Path d => LifetimePath.exitTime U w) :=
    (LifetimePath.isStoppingTime_exitTime U hU).measurable'
  set S : Set (Path d × ℝ) :=
    {q : Path d × ℝ | ENNReal.ofReal q.2 < LifetimePath.exitTime U q.1} with hSdef
  have hSmeas : MeasurableSet S :=
    measurableSet_lt measurable_snd.ennreal_ofReal (hτ.comp measurable_fst)
  set G : Path d × ℝ → ℝ≥0∞ := S.indicator (fun _ => 1) with hGdef
  have hGmeas : Measurable G := measurable_const.indicator hSmeas
  have hslice1 : ∀ w : Path d,
      (fun t : ℝ => G (w, t))
        = ({t : ℝ | ENNReal.ofReal t < LifetimePath.exitTime U w}).indicator (fun _ => 1) := by
    intro w
    funext t
    by_cases h : ENNReal.ofReal t < LifetimePath.exitTime U w <;> simp [G, S, h]
  have hslice2 : ∀ t : ℝ,
      (fun w : Path d => G (w, t))
        = ({w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w}).indicator (fun _ => 1) := by
    intro t
    funext w
    by_cases h : ENNReal.ofReal t < LifetimePath.exitTime U w <;> simp [G, S, h]
  have hinner : ∀ w : Path d, (∫⁻ t in Ioi (0 : ℝ), G (w, t)) = LifetimePath.exitTime U w := by
    intro w
    have hmeasset : MeasurableSet {t : ℝ | ENNReal.ofReal t < LifetimePath.exitTime U w} :=
      measurableSet_lt measurable_id.ennreal_ofReal measurable_const
    rw [hslice1 w, lintegral_indicator hmeasset, lintegral_const, one_mul,
      Measure.restrict_apply_univ, Measure.restrict_apply hmeasset]
    have hsetEq : {t : ℝ | ENNReal.ofReal t < LifetimePath.exitTime U w} ∩ Ioi 0
        = {t : ℝ | 0 < t ∧ ENNReal.ofReal t < LifetimePath.exitTime U w} := by
      ext t
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hsetEq, volume_setOf_ofReal_lt]
  have houter : ∀ t : ℝ, (∫⁻ w, G (w, t) ∂law x)
      = law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w} := by
    intro t
    have hmeasset : MeasurableSet {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w} :=
      measurableSet_lt measurable_const hτ
    rw [hslice2 t, lintegral_indicator hmeasset, lintegral_const, one_mul,
      Measure.restrict_apply_univ]
  calc meanExit law U x = ∫⁻ w, LifetimePath.exitTime U w ∂law x := rfl
    _ = ∫⁻ w, (∫⁻ t in Ioi (0 : ℝ), G (w, t)) ∂law x := by
        exact lintegral_congr fun w => (hinner w).symm
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ w, G (w, t) ∂law x :=
        lintegral_lintegral_swap hGmeas.aemeasurable
    _ = ∫⁻ t in Ioi (0 : ℝ), law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w} :=
        lintegral_congr houter

/-- An exponential tail bound integrates to a bound on the mean exit time. -/
theorem meanExit_le_of_tail (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpen U) (x : Vec d) {K b : ℝ} (hK : 0 ≤ K) (hb : 0 < b)
    (htail : ∀ t : ℝ, 0 < t →
      law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w} ≤
        ENNReal.ofReal (K * Real.exp (-(b * t)))) :
    meanExit law U x ≤ ENNReal.ofReal (K * b⁻¹) := by
  rw [meanExit_eq_lintegral_survival law hU x, ← lintegral_Ioi_ofReal_exp_neg_mul hK hb]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact htail t ht

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper
