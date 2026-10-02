import SubdiffusiveProcess.PartProcess.FeynmanKac
import SubdiffusiveProcess.PartProcess.CompactCoverExit
import SubdiffusiveProcess.PartProcess.CompactKillingDetection
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7
variable {d : ℕ} {m : Measure (Fin d → ℝ)}

/-- For a closed set, time spent outside detects every exit except the exit time itself. -/
theorem penalty_weight_tendsto (A : Set (Fin d → ℝ)) (hA : IsClosed A)
    (w : ContinuousPath (Fin d → ℝ)) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp
        (-SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional
          (penalty A n) (Real.toNNReal t) w))) atTop
      (𝓝 ({t : ℝ | ENNReal.ofReal t <
        LifetimePath.exitTime A (LifetimePath.ofContinuousPath w)}.indicator
          (fun _ => (1 : ℝ≥0∞)) t)) := by
  filter_upwards [ae_ofReal_ne_exit A w, ae_restrict_mem measurableSet_Ioi] with t hne ht
  simpa only [LifetimePath.exitTime_ofContinuousPath] using
    penalty_weight_tendsto_of_ne A hA w t ht hne

theorem penaltyOcc_tendsto
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) (hK : IsMarkovKernel K)
    (A : Set (Fin d → ℝ)) (hA : IsClosed A) (α : ℝ) (hα : 0 < α)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (x : Fin d → ℝ) (hfin : potentialOcc K 0 α f x < ⊤) :
    Tendsto (fun n => potentialOcc K (penalty A n) α f x) atTop
      (𝓝 (killedOcc K A α f x)) := by
  letI := hK
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let S : Set (ℝ × ContinuousPath (Fin d → ℝ)) :=
    {p | ENNReal.ofReal p.1 < ContinuousPath.exitTime A p.2}
  have hS : MeasurableSet S := measurableSet_lt
    (ENNReal.measurable_ofReal.comp measurable_fst)
    ((measurable_closed_exit A hA).comp measurable_snd)
  let B : ℝ × ContinuousPath (Fin d → ℝ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (-α * p.1)) * ENNReal.ofReal (f (p.2 (Real.toNNReal p.1)))
  let W : ℕ → ℝ × ContinuousPath (Fin d → ℝ) → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (Real.exp (-SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional
      (penalty A n) (Real.toNNReal p.1) p.2))
  let F : ℕ → ℝ × ContinuousPath (Fin d → ℝ) → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (Real.exp (-α * p.1)) *
      (W n p * ENNReal.ofReal (f (p.2 (Real.toNNReal p.1))))
  have hc : Measurable (fun p : ℝ × ContinuousPath (Fin d → ℝ) =>
      ENNReal.ofReal (Real.exp (-α * p.1))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).measurable
  have hg : Measurable (fun p : ℝ × ContinuousPath (Fin d → ℝ) =>
      ENNReal.ofReal (f (p.2 (Real.toNNReal p.1)))) :=
    ENNReal.measurable_ofReal.comp (hf.comp aux_n8_measurable_eval)
  have hq : ∀ n, Measurable (penalty A n) := fun n =>
    measurable_const.mul (measurable_const.indicator hA.measurableSet.compl)
  have hq0 : ∀ n x, 0 ≤ penalty A n x := fun n x =>
    mul_nonneg (Nat.cast_nonneg n) (indicator_nonneg (fun _ _ => zero_le_one) x)
  have hW : ∀ n, Measurable (W n) := by
    intro n
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (((SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional_joint
        (hq n)).measurable.comp
          ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)).neg))
  have hF : ∀ n, Measurable (F n) := fun n => hc.mul ((hW n).mul hg)
  have hB : Measurable B := hc.mul hg
  have htest : ∀ t, Measurable (fun w : ContinuousPath (Fin d → ℝ) =>
      ENNReal.ofReal (f (w (Real.toNNReal t)))) := fun t =>
    ENNReal.measurable_ofReal.comp (hf.comp (ContinuousPath.measurable_coordinateProcess _))
  have hfree : ∫⁻ p, B p ∂(μ.prod (K x)) = potentialOcc K 0 α f x := by
    rw [lintegral_prod _ hB.aemeasurable]
    unfold potentialOcc
    simp only [SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional,
      Pi.zero_apply, intervalIntegral.integral_zero, neg_zero, Real.exp_zero,
      ENNReal.ofReal_one, one_mul]
    apply lintegral_congr
    intro t
    change (∫⁻ w, ENNReal.ofReal (Real.exp (-α * t)) *
      ENNReal.ofReal (f (w (Real.toNNReal t))) ∂K x) = _
    exact lintegral_const_mul _ (htest t)
  have hpen : ∀ n, ∫⁻ p, F n p ∂(μ.prod (K x)) = potentialOcc K (penalty A n) α f x := by
    intro n
    rw [lintegral_prod _ (hF n).aemeasurable]
    apply lintegral_congr
    intro t
    have hWt : Measurable (fun w : ContinuousPath (Fin d → ℝ) => W n (t, w)) :=
      (hW n).comp (measurable_const.prodMk measurable_id)
    change (∫⁻ w, ENNReal.ofReal (Real.exp (-α * t)) *
      (W n (t, w) * ENNReal.ofReal (f (w (Real.toNNReal t)))) ∂K x) =
        ENNReal.ofReal (Real.exp (-α * t)) *
          ∫⁻ w, W n (t, w) * ENNReal.ofReal (f (w (Real.toNNReal t))) ∂K x
    exact lintegral_const_mul _ (hWt.mul (htest t))
  have hkilled : ∫⁻ p, S.indicator B p ∂(μ.prod (K x)) = killedOcc K A α f x := by
    rw [lintegral_prod _ (hB.indicator hS).aemeasurable, killedOcc_continuousPath]
    apply lintegral_congr
    intro t
    rw [← lintegral_indicator (measurableSet_lt measurable_const (measurable_closed_exit A hA))]
    rw [← lintegral_const_mul _ ((htest t).indicator
      (measurableSet_lt measurable_const (measurable_closed_exit A hA)))]
    apply lintegral_congr
    intro w
    change S.indicator B (t, w) = _
    by_cases h : ENNReal.ofReal t < ContinuousPath.exitTime A w
    · rw [indicator_of_mem (show (t, w) ∈ S from h),
        indicator_of_mem (show w ∈ {w | ENNReal.ofReal t < ContinuousPath.exitTime A w} from h)]
    · rw [indicator_of_notMem (show (t, w) ∉ S from h),
        indicator_of_notMem (show w ∉ {w | ENNReal.ofReal t < ContinuousPath.exitTime A w} from h),
        mul_zero]
  have hbound : ∀ n, F n ≤ᵐ[μ.prod (K x)] B := by
    intro n
    filter_upwards with p
    have hw : W n p ≤ 1 := by
      change ENNReal.ofReal _ ≤ 1
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 (neg_nonpos.2
        (SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional_nonneg (hq0 n) _ _)))
    exact mul_le_mul_right ((mul_le_mul_left hw _).trans_eq (one_mul _)) _
  have hgood : MeasurableSet {p : ℝ × ContinuousPath (Fin d → ℝ) |
      0 < p.1 ∧ ENNReal.ofReal p.1 ≠ ContinuousPath.exitTime A p.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_eq_fun (ENNReal.measurable_ofReal.comp measurable_fst)
        ((measurable_closed_exit A hA).comp measurable_snd)).compl
  have hae : ∀ᵐ p ∂(μ.prod (K x)),
      0 < p.1 ∧ ENNReal.ofReal p.1 ≠ ContinuousPath.exitTime A p.2 := by
    apply (Measure.ae_prod_iff_ae_ae hgood).2
    apply (Measure.ae_ae_comm
      (p := fun t w => 0 < t ∧ ENNReal.ofReal t ≠ ContinuousPath.exitTime A w) hgood).2
    filter_upwards with w
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_ofReal_ne_exit A w] with t ht hne
    exact ⟨ht, hne⟩
  have hlim : ∀ᵐ p ∂(μ.prod (K x)),
      Tendsto (fun n => F n p) atTop (𝓝 (S.indicator B p)) := by
    filter_upwards [hae] with p hp
    have hw := penalty_weight_tendsto_of_ne A hA p.2 p.1 hp.1 hp.2
    have ht := ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (Real.exp (-α * p.1)))
      (ENNReal.Tendsto.mul_const (b := ENNReal.ofReal (f (p.2 (Real.toNNReal p.1))))
        hw (Or.inr ENNReal.ofReal_ne_top)) (Or.inr ENNReal.ofReal_ne_top)
    by_cases hs : ENNReal.ofReal p.1 < ContinuousPath.exitTime A p.2
    · simpa only [F, W, B, indicator_of_mem (show p ∈ S from hs),
        indicator_of_mem (show p.1 ∈ {t | ENNReal.ofReal t < ContinuousPath.exitTime A p.2} from hs),
        one_mul] using ht
    · simpa only [F, W, B, indicator_of_notMem (show p ∉ S from hs),
        indicator_of_notMem (show p.1 ∉ {t | ENNReal.ofReal t < ContinuousPath.exitTime A p.2} from hs),
        zero_mul, mul_zero] using ht
  have hconv := tendsto_lintegral_of_dominated_convergence B hF hbound
    (by rw [hfree]; exact hfin.ne) hlim
  simpa only [hpen, hkilled] using hconv

/-- Compact exit killing is the limit of bounded-potential form perturbations. -/
theorem compact_association (hm : IsLocallyFiniteMeasure m) (hpos : m.IsOpenPosMeasure)
    (D : Data d m) (A : Set (Fin d → ℝ)) (hA : IsCompact A)
    (α : ℝ) (hα : 0 < α)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hG : IsDomainResolvent D.form.toClosedForm
      (supportedDomain D.form.toClosedForm A) α G)
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfL : MemLp f 2 m) :
    (∀ᵐ x ∂m, killedOcc D.law A α f x < ⊤) ∧
    (fun x => (killedOcc D.law A α f x).toReal) =ᵐ[m] ⇑(G (hfL.toLp f)) := by
  classical
  have hq : ∀ n, Measurable (penalty A n) := fun n =>
    measurable_const.mul (measurable_const.indicator hA.measurableSet.compl)
  have hq0 : ∀ n x, 0 ≤ penalty A n x := fun n x =>
    mul_nonneg (Nat.cast_nonneg n) (indicator_nonneg (fun _ _ => zero_le_one) x)
  have hqb : ∀ n x, penalty A n x ≤ (n : ℝ) := by
    intro n x
    unfold penalty
    by_cases hx : x ∈ Aᶜ
    · rw [indicator_of_mem hx, mul_one]
    · rw [indicator_of_notMem hx, mul_zero]
      exact Nat.cast_nonneg n
  choose F hFdom hFform using fun n => exists_boundedPerturbation
    D.form.toClosedForm (penalty A n) (hq n) (hq0 n) (n : ℝ) (hqb n)
  choose Gn hGn using fun n => exists_isResolvent (F n) hα
  have hconv := penalized_resolvent_tendsto D.form.toClosedForm A hA.measurableSet
    α hα F hFdom hFform Gn hGn G hG (hfL.toLp f)
  have hassoc := fun n => potentialOcc_association hm hpos D (penalty A n)
    (hq n) (hq0 n) (n : ℝ) (hqb n) (F n) (hFdom n) (hFform n)
    α hα (Gn n) (hGn n) f hf hf0 hfL
  obtain ⟨R, hR⟩ := exists_isResolvent D.form.toClosedForm hα
  have hfreefin := (free_association hm hpos D α hα R hR f hf hf0 hfL).1
  have hkillfin : ∀ᵐ x ∂m, killedOcc D.law A α f x < ⊤ :=
    hfreefin.mono fun x hx => (killedOcc_le_free D.law A α f x).trans_lt hx
  refine ⟨hkillfin, ?_⟩
  obtain ⟨ns, hns, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  filter_upwards [hfreefin, hkillfin, hsub, ae_all_iff.2 (fun n => (hassoc n).2)]
    with x hfree hkill hx he
  have hpen := penaltyOcc_tendsto D.law D.markov A hA.isClosed α hα f hf hf0 x hfree
  have hlim := (ENNReal.tendsto_toReal hkill.ne).comp (hpen.comp hns.tendsto_atTop)
  exact tendsto_nhds_unique hlim (hx.congr fun k => (he (ns k)).symm)

end SubdiffusiveProcess.PartProcess
