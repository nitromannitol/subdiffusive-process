module

public import SubdiffusiveProcess.PartProcess.FreeResolvent
public import SubdiffusiveProcess.PartProcess.FeynmanKacResolvent
public import Homogenization.Sobolev.Truncation.WeakGradientLimit

@[expose] public section

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubMarkovKernelSemigroup
variable {d : ℕ} {m : Measure (Fin d → ℝ)}

theorem potentialOcc_mono (S : Data d m) (q : (Fin d → ℝ) → ℝ) (α : ℝ)
    {f g : (Fin d → ℝ) → ℝ} (hfg : ∀ y, f y ≤ g y) (x : Fin d → ℝ) :
    potentialOcc S.law q α f x ≤ potentialOcc S.law q α g x := by
  apply lintegral_mono
  intro t
  apply mul_le_mul_right
  apply lintegral_mono
  intro w
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hfg _)) _

theorem potentialOcc_tendsto_mono (S : Data d m) {q : (Fin d → ℝ) → ℝ}
    (hq : Measurable q) (α : ℝ) {fs : ℕ → (Fin d → ℝ) → ℝ}
    (hfs : ∀ n, Measurable (fs n)) (hmono : ∀ y, Monotone fun n => fs n y)
    {f : (Fin d → ℝ) → ℝ}
    (hlim : ∀ y, Tendsto (fun n => fs n y) atTop (𝓝 (f y))) (x : Fin d → ℝ) :
    Tendsto (fun n => potentialOcc S.law q α (fs n) x) atTop
      (𝓝 (potentialOcc S.law q α f x)) := by
  letI := S.markov
  have hA : Measurable fun p : ℝ × ContinuousPath (Fin d → ℝ) =>
      feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hw : Measurable fun p : ℝ × ContinuousPath (Fin d → ℝ) =>
      ENNReal.ofReal (Real.exp (-feynmanKacAdditiveFunctional q
        (Real.toNNReal p.1) p.2)) := (Real.measurable_exp.comp hA.neg).ennreal_ofReal
  have he : Measurable fun p : ℝ × ContinuousPath (Fin d → ℝ) =>
      p.2 (Real.toNNReal p.1) := SubdiffusiveProcess.E7.aux_n8_measurable_eval
  have hJ (n : ℕ) : Measurable fun t : ℝ =>
      ∫⁻ w, ENNReal.ofReal (Real.exp (-feynmanKacAdditiveFunctional q
        (Real.toNNReal t) w)) * ENNReal.ofReal (fs n (w (Real.toNNReal t))) ∂S.law x :=
    (hw.mul ((hfs n).comp he).ennreal_ofReal).lintegral_prod_right'
  have hW : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-α * t)) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact (hW.mul (hJ n)).aemeasurable
  · exact ae_of_all _ fun t n k hnk => mul_le_mul_right (lintegral_mono fun w =>
      mul_le_mul_right (ENNReal.ofReal_le_ofReal (hmono _ hnk)) _) _
  · apply ae_of_all
    intro t
    apply ENNReal.Tendsto.const_mul _ (Or.inr ENNReal.ofReal_ne_top)
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n
      exact (((hw.mul ((hfs n).comp he).ennreal_ofReal).comp
        (measurable_const.prodMk measurable_id))).aemeasurable
    · exact ae_of_all _ fun w n k hnk =>
        mul_le_mul_right (ENNReal.ofReal_le_ofReal (hmono _ hnk)) _
    · exact ae_of_all _ fun w =>
        ENNReal.Tendsto.const_mul
          ((ENNReal.continuous_ofReal.tendsto _).comp (hlim _))
          (Or.inr ENNReal.ofReal_ne_top)

/-- Truncations of a nonnegative input, and their potential occupations, converge in `L²`. -/
theorem potentialOcc_truncation_tendsto
    (hm : IsLocallyFiniteMeasure m) (hpos : m.IsOpenPosMeasure) (S : Data d m)
    {q : (Fin d → ℝ) → ℝ} (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    {α : ℝ} (hα : 0 < α) {f : (Fin d → ℝ) → ℝ}
    (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (hfL : MemLp f 2 m)
    (hs : ∀ n : ℕ, MemLp (fun y => min (f y) (n : ℝ)) 2 m)
    (hu : MemLp (fun x => (potentialOcc S.law q α f x).toReal) 2 m)
    (hus : ∀ n : ℕ, MemLp
      (fun x => (potentialOcc S.law q α (fun y => min (f y) (n : ℝ)) x).toReal) 2 m) :
    Tendsto (fun n => (hs n).toLp (fun y => min (f y) (n : ℝ))) atTop
      (𝓝 (hfL.toLp f)) ∧
    Tendsto (fun n => (hus n).toLp
      (fun x => (potentialOcc S.law q α (fun y => min (f y) (n : ℝ)) x).toReal)) atTop
      (𝓝 (hu.toLp (fun x => (potentialOcc S.law q α f x).toReal))) := by
  letI := S.markov
  have hmeas (n : ℕ) : Measurable fun y => min (f y) (n : ℝ) := hf.min measurable_const
  have hnonneg (n : ℕ) (y : Fin d → ℝ) : 0 ≤ min (f y) (n : ℝ) :=
    le_min (hf0 y) (Nat.cast_nonneg n)
  have hlim (y : Fin d → ℝ) :
      Tendsto (fun n : ℕ => min (f y) (n : ℝ)) atTop (𝓝 (f y)) := by
    obtain ⟨N, hN⟩ := exists_nat_ge (f y)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (min_eq_left (hN.trans (Nat.cast_le.2 hn))).symm
  constructor
  · apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hs _ hfL).2
    exact Homogenization.tendsto_eLpNorm_two_of_tendsto_ae_of_dominated
      (fun n => (hmeas n).aestronglyMeasurable) hfL hfL
      (fun n => ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg n y)]
        exact min_le_left _ _) (ae_of_all _ hlim)
  · apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hus _ hu).2
    have hfin := (potentialOcc_memLp hm hpos S q hq hq0 α hα f hf hf0 hfL).1
    apply Homogenization.tendsto_eLpNorm_two_of_tendsto_ae_of_dominated
      (fun n => (hus n).aestronglyMeasurable) hu hu
    · intro n
      filter_upwards [hfin] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_mono hx.ne (potentialOcc_mono S q α
        (fun y => min_le_left (f y) (n : ℝ)) x)
    · filter_upwards [hfin] with x hx
      exact (ENNReal.continuousAt_toReal hx.ne).tendsto.comp
        (potentialOcc_tendsto_mono S hq α hmeas
          (fun y n k hnk => min_le_min_left _ (Nat.cast_le.2 hnk)) hlim x)

end SubdiffusiveProcess.PartProcess
