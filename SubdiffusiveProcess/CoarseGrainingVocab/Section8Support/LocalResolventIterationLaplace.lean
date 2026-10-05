module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeLaplaceUniqueness
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
@[expose] public section

/-!
# Laplace uniqueness for bounded right-continuous functions

The weighted primitive reduces half-line Laplace uniqueness for right-continuous measurable
functions to the existing continuous uniqueness theorem. Right integration by parts supplies the
primitive's Laplace transform without requiring two-sided derivatives at discontinuities.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
/-- A bounded measurable function has an integrable Laplace integrand at every positive rate. -/
theorem integrableOn_exp_neg_mul_of_bound (h : ℝ → ℝ) (hm : Measurable h) (C : ℝ) (hb : ∀ t, |h t| ≤ C) (r : ℝ) (hr : 0 < r) : IntegrableOn (fun t => Real.exp (-(r*t)) * h t) (Ioi 0) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hb 0)
  have hmeas : AEStronglyMeasurable (fun t => Real.exp (-(r*t)) * h t)
      (volume.restrict (Ioi 0)) :=
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id).neg).mul hm).aestronglyMeasurable
  have hdom : IntegrableOn (fun t => C * Real.exp (-(r*t))) (Ioi 0) := by
    simpa [IntegrableOn, neg_mul] using! (exp_neg_integrableOn_Ioi (b := r) 0 hr).const_mul C
  apply Integrable.mono hdom hmeas
  exact Eventually.of_forall fun t => by
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hC]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le

/-- Changing the inclusion of the endpoint preserves integrability of the half-line indicator. -/
theorem integrable_indicator_Ici_of_integrableOn_Ioi (h : ℝ → ℝ) (hh : IntegrableOn h (Ioi 0)) : Integrable ((Ici (0:ℝ)).indicator h) := by
  have hi : IntegrableOn h (Ici (0:ℝ)) := by rwa [integrableOn_Ici_iff_integrableOn_Ioi]
  exact (integrable_indicator_iff measurableSet_Ici).mpr hi

/-- The absolute integral of an integrable function bounds every interval primitive. -/
theorem abs_intervalIntegral_le_integral_abs (k : ℝ → ℝ) (hk : Integrable k) (t : ℝ) : |∫ u in (0:ℝ)..t, k u| ≤ ∫ u, |k u| := by
  simpa only [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := k) (a := 0) (b := t)).trans
      (setIntegral_le_integral hk.norm (Eventually.of_forall (fun _ => norm_nonneg _)))

/-- The interval primitive of an integrable function is continuous. -/
theorem continuous_intervalIntegral_of_integrable (k : ℝ → ℝ) (hk : Integrable k) : Continuous (fun t => ∫ u in (0:ℝ)..t, k u) := by
  exact hk.continuous_primitive 0

/-- Right continuity of an integrable function gives the right derivative of its primitive. -/
theorem hasDerivWithinAt_intervalIntegral_right (k : ℝ → ℝ) (hk : Integrable k) (hm : StronglyMeasurable k) (t : ℝ) (hc : ContinuousWithinAt k (Ici t) t) : HasDerivWithinAt (fun u => ∫ x in (0:ℝ)..u, k x) (k t) (Ici t) t := by
  exact intervalIntegral.integral_hasDerivWithinAt_right hk.intervalIntegrable
    hm.stronglyMeasurableAtFilter (hc.mono Ioi_subset_Ici_self)

/-- An improper fundamental theorem of calculus using right derivatives. -/
theorem integral_Ioi_eq_neg_of_hasDeriv_right (F D : ℝ → ℝ) (hc : Continuous F) (hd : ∀ t, 0 < t → HasDerivWithinAt F (D t) (Ioi t) t) (hi : IntegrableOn D (Ioi 0)) (hlim : Tendsto F atTop (nhds 0)) : ∫ t in Ioi (0:ℝ), D t = -F 0 := by
  have hlimint := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hi tendsto_id
  have heq : (fun b : ℝ => ∫ t in (0:ℝ)..b, D t) =ᶠ[atTop] (fun b => F b - F 0) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with b hb
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hb.le hc.continuousOn
      (fun t ht => hd t ht.1) ⟨hi.mono_set Ioc_subset_Ioi_self, by simp [Ioc_eq_empty_of_le hb.le]⟩
  have hlim' := (hlim.sub_const (F 0)).congr' heq.symm
  simpa only [zero_sub] using tendsto_nhds_unique hlimint hlim' 

/-- Exponential decay times a uniformly bounded function tends to zero. -/
theorem tendsto_exp_neg_mul_of_bound (H : ℝ → ℝ) (M : ℝ) (hb : ∀ t, |H t| ≤ M) (r : ℝ) (hr : 0 < r) : Tendsto (fun t => Real.exp (-(r*t)) * H t) atTop (nhds 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-(r*t))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)
  apply squeeze_zero_norm (fun t => ?_) (by simpa using he.mul_const M)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le

/-- The right derivative of a function multiplied by an exponential weight. -/
theorem hasDerivWithinAt_exp_neg_mul (H : ℝ → ℝ) (r t v : ℝ) (hH : HasDerivWithinAt H v (Ioi t) t) : HasDerivWithinAt (fun x => Real.exp (-(r*x)) * H x) (Real.exp (-(r*t)) * (v-r*H t)) (Ioi t) t := by
  have he := (((hasDerivAt_id t).const_mul r).neg.exp).hasDerivWithinAt (s := Ioi t)
  exact (he.mul hH).congr_deriv (by dsimp; ring)

/-- A right derivative of a function vanishing on the right half-line is zero. -/
theorem eq_zero_of_hasDerivWithinAt_zero_on_Ici (H : ℝ → ℝ) (t v : ℝ) (hH : HasDerivWithinAt H v (Ici t) t) (hz : ∀ u, t ≤ u → H u = 0) : v = 0 := by
  have hc : HasDerivWithinAt H 0 (Ici t) t :=
    (hasDerivWithinAt_const t (Ici t) (0:ℝ)).congr_of_mem (fun u hu => hz u hu) Set.self_mem_Ici
  exact (hH.derivWithin (uniqueDiffWithinAt_Ici t)).symm.trans
    (hc.derivWithin (uniqueDiffWithinAt_Ici t))

/-- The nonnegative half-line indicator preserves right continuity at nonnegative points. -/
theorem continuousWithinAt_indicator_exp_neg_mul (h : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (hc : ContinuousWithinAt h (Ici t) t) : ContinuousWithinAt ((Ici (0:ℝ)).indicator (fun u => Real.exp (-u) * h u)) (Ici t) t := by
  apply ((Real.continuous_exp.comp continuous_neg).continuousWithinAt.mul hc).congr_of_mem
    (fun u hu => Set.indicator_of_mem (ht.trans hu) _) Set.self_mem_Ici

/-- A bounded measurable right-continuous function with vanishing Laplace transforms vanishes.

The weighted primitive is bounded and continuous. Right integration by parts gives its vanishing
Laplace transforms, so continuous Laplace uniqueness and the right fundamental theorem apply. -/
theorem eq_zero_of_forall_integral_exp_neg_mul_eq_zero_of_rightContinuous
    {h : ℝ → ℝ} (hm : Measurable h)
    (hright : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt h (Ici t) t)
    {C : ℝ} (hb : ∀ t : ℝ, |h t| ≤ C)
    (hlap : ∀ r : ℝ, 0 < r →
      ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) * h t = 0) :
    ∀ t : ℝ, 0 ≤ t → h t = 0 := by
  let k : ℝ → ℝ := (Ici (0 : ℝ)).indicator (fun t => Real.exp (-t) * h t)
  have hk : Integrable k := integrable_indicator_Ici_of_integrableOn_Ioi _ (by
    simpa only [one_mul] using integrableOn_exp_neg_mul_of_bound h hm C hb 1 zero_lt_one)
  have hkm : StronglyMeasurable k :=
    (((Real.measurable_exp.comp measurable_id.neg).mul hm).indicator measurableSet_Ici).stronglyMeasurable
  let H : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, k u
  let M : ℝ := ∫ u, |k u|
  have hHc : Continuous H := continuous_intervalIntegral_of_integrable k hk
  have hHb : ∀ t : ℝ, |H t| ≤ M := abs_intervalIntegral_le_integral_abs k hk
  have hH0 : H 0 = 0 := by simp [H]
  have hHd : ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt H (Real.exp (-t) * h t) (Ici t) t := by
    intro t ht
    have hd := hasDerivWithinAt_intervalIntegral_right k hk hkm t
      (continuousWithinAt_indicator_exp_neg_mul h t ht (hright t ht))
    simpa only [k, Set.indicator_of_mem (show t ∈ Ici (0:ℝ) from ht)] using hd
  have hHlap : ∀ r : ℝ, 0 < r →
      ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) * H t = 0 := by
    intro r hr
    let Q : ℝ → ℝ := fun t => Real.exp (-(r * t)) * H t
    let D : ℝ → ℝ := fun t =>
      -r * (Real.exp (-(r * t)) * H t) + Real.exp (-((r + 1) * t)) * h t
    have hI := integrableOn_exp_neg_mul_of_bound H hHc.measurable M hHb r hr
    have hJ := integrableOn_exp_neg_mul_of_bound h hm C hb (r + 1) (by linarith)
    have hDi : IntegrableOn D (Ioi 0) := (hI.const_mul (-r)).add hJ
    have hQc : Continuous Q := (Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg).mul hHc
    have hQd : ∀ t : ℝ, 0 < t → HasDerivWithinAt Q (D t) (Ioi t) t := by
      intro t ht
      have hd := hasDerivWithinAt_exp_neg_mul H r t (Real.exp (-t) * h t)
        ((hHd t ht.le).mono Ioi_subset_Ici_self)
      apply hd.congr_deriv
      dsimp [D]
      rw [show -((r + 1) * t) = -(r * t) + -t by ring, Real.exp_add]
      ring
    have hQlim : Tendsto Q atTop (nhds 0) := tendsto_exp_neg_mul_of_bound H M hHb r hr
    have heq := integral_Ioi_eq_neg_of_hasDeriv_right Q D hQc hQd hDi hQlim
    have hsplit : (∫ t in Ioi (0 : ℝ), D t) =
        -r * (∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) * H t) := by
      rw [show D = (fun t => -r * (Real.exp (-(r * t)) * H t) +
          Real.exp (-((r + 1) * t)) * h t) from rfl,
        integral_add (hI.const_mul (-r)) hJ, integral_const_mul,
        hlap (r + 1) (by linarith), add_zero]
    rw [hsplit, show Q 0 = 0 by simp [Q, hH0], neg_zero] at heq
    exact (mul_eq_zero.mp heq).resolve_left (neg_ne_zero.mpr hr.ne')
  have hHz := SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.eq_zero_of_forall_integral_exp_neg_mul_eq_zero
    hHc hHb hHlap
  intro t ht
  have hz := eq_zero_of_hasDerivWithinAt_zero_on_Ici H t (Real.exp (-t) * h t) (hHd t ht)
    (fun u hu => hHz u (ht.trans hu))
  exact (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)

/-- Globally bounded measurable functions with equal Laplace transforms and right continuity agree
on the nonnegative half-line. -/
theorem eq_of_forall_integral_exp_neg_mul_eq_of_rightContinuous_of_bound
    {F G : ℝ → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt F (Ici t) t)
    (hG : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt G (Ici t) t)
    {C : ℝ} (hFb : ∀ t : ℝ, |F t| ≤ C) (hGb : ∀ t : ℝ, |G t| ≤ C)
    (hlap : ∀ r : ℝ, 0 < r →
      ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) * F t =
        ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) * G t) :
    ∀ t : ℝ, 0 ≤ t → F t = G t := by
  have hb : ∀ t : ℝ, |F t - G t| ≤ C + C := by
    intro t
    have h1 := abs_le.mp (hFb t)
    have h2 := abs_le.mp (hGb t)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hd : ∀ r : ℝ, 0 < r →
      ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) * (F t - G t) = 0 := by
    intro r hr
    simp only [mul_sub]
    rw [integral_sub (integrableOn_exp_neg_mul_of_bound F hFm C hFb r hr)
      (integrableOn_exp_neg_mul_of_bound G hGm C hGb r hr), hlap r hr, sub_self]
  have hz := eq_zero_of_forall_integral_exp_neg_mul_eq_zero_of_rightContinuous
    (hFm.sub hGm) (fun t ht => (hF t ht).sub (hG t ht)) hb hd
  intro t ht
  exact sub_eq_zero.mp (hz t ht)

/-- Bounded measurable functions on the nonnegative half-line are determined by their Laplace
transforms if they are right-continuous at every nonnegative point.

Only the values and bounds on the nonnegative half-line enter the conclusion. -/
theorem eq_of_forall_integral_exp_neg_mul_eq_of_rightContinuous
    {F G : ℝ → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt F (Ici t) t)
    (hG : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt G (Ici t) t)
    {C : ℝ} (hFb : ∀ t : ℝ, 0 ≤ t → |F t| ≤ C)
    (hGb : ∀ t : ℝ, 0 ≤ t → |G t| ≤ C)
    (hlap : ∀ r : ℝ, 0 < r →
      ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) * F t =
        ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) * G t) :
    ∀ t : ℝ, 0 ≤ t → F t = G t := by
  let F' := (Ici (0 : ℝ)).indicator F
  let G' := (Ici (0 : ℝ)).indicator G
  have hC : 0 ≤ C := (abs_nonneg (F 0)).trans (hFb 0 le_rfl)
  have hF'b : ∀ t : ℝ, |F' t| ≤ C := by
    intro t
    by_cases ht : 0 ≤ t
    · simpa only [F', Set.indicator_of_mem (show t ∈ Ici (0:ℝ) from ht)] using hFb t ht
    · simpa only [F', Set.indicator_of_notMem (show t ∉ Ici (0:ℝ) from ht), abs_zero] using hC
  have hG'b : ∀ t : ℝ, |G' t| ≤ C := by
    intro t
    by_cases ht : 0 ≤ t
    · simpa only [G', Set.indicator_of_mem (show t ∈ Ici (0:ℝ) from ht)] using hGb t ht
    · simpa only [G', Set.indicator_of_notMem (show t ∉ Ici (0:ℝ) from ht), abs_zero] using hC
  have hF'c : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt F' (Ici t) t := by
    intro t ht
    exact (hF t ht).congr_of_mem (fun u hu => Set.indicator_of_mem (ht.trans hu) _) Set.self_mem_Ici
  have hG'c : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt G' (Ici t) t := by
    intro t ht
    exact (hG t ht).congr_of_mem (fun u hu => Set.indicator_of_mem (ht.trans hu) _) Set.self_mem_Ici
  have h'lap : ∀ r : ℝ, 0 < r →
      ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) * F' t =
        ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) * G' t := by
    intro r hr
    calc
      _ = ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) * F t :=
        setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
          rw [show F' t = F t from Set.indicator_of_mem ht.le F])
      _ = ∫ t in Ioi (0 : ℝ), Real.exp (-(r * t)) * G t := hlap r hr
      _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
          rw [show G' t = G t from Set.indicator_of_mem ht.le G])
  have heq := eq_of_forall_integral_exp_neg_mul_eq_of_rightContinuous_of_bound
    (hFm.indicator measurableSet_Ici) (hGm.indicator measurableSet_Ici)
    hF'c hG'c hF'b hG'b h'lap
  intro t ht
  simpa only [F', G', Set.indicator_of_mem (show t ∈ Ici (0:ℝ) from ht)] using heq t ht

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
