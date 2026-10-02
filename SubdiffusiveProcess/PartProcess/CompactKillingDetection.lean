import SubdiffusiveProcess.PartProcess.Penalization
import SubdiffusiveProcess.PartProcess.CompactCoverExit

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess

def outsidePotential {d : ℕ} (A : Set (Fin d → ℝ)) : (Fin d → ℝ) → ℝ :=
  Aᶜ.indicator (fun _ => 1)

theorem outsidePotential_nonneg {d : ℕ} (A : Set (Fin d → ℝ)) (x : Fin d → ℝ) :
    0 ≤ outsidePotential A x := indicator_nonneg (fun _ _ => zero_le_one) x

theorem outsidePotential_le_one {d : ℕ} (A : Set (Fin d → ℝ)) (x : Fin d → ℝ) :
    outsidePotential A x ≤ 1 := by
  by_cases hx : x ∈ Aᶜ
  · exact (indicator_of_mem hx _).le
  · rw [outsidePotential, indicator_of_notMem hx]
    exact zero_le_one

theorem outsidePotential_measurable {d : ℕ} (A : Set (Fin d → ℝ)) (hA : IsClosed A) :
    Measurable (outsidePotential A) := measurable_const.indicator hA.measurableSet.compl

theorem penalty_functional_eq {d : ℕ} (A : Set (Fin d → ℝ)) (n : ℕ)
    (t : NNReal) (w : ContinuousPath (Fin d → ℝ)) :
    SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional (penalty A n) t w =
      (n : ℝ) * SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional (outsidePotential A) t w := by
  unfold SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional penalty outsidePotential
  exact intervalIntegral.integral_const_mul _ _

theorem outside_functional_eq_zero_before_exit {d : ℕ}
    (A : Set (Fin d → ℝ)) (w : ContinuousPath (Fin d → ℝ)) (t : NNReal)
    (ht : (t : ℝ≥0∞) < ContinuousPath.exitTime A w) :
    SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional (outsidePotential A) t w = 0 := by
  unfold SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional
  rw [intervalIntegral.integral_of_le t.coe_nonneg]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hst : Real.toNNReal s ≤ t := by
    rw [Real.toNNReal_le_iff_le_coe]
    exact hs.2
  have hmem := ContinuousPath.mem_of_lt_exitTime A w (Real.toNNReal s)
    ((ENNReal.coe_le_coe.2 hst).trans_lt ht)
  exact indicator_of_notMem (show w (Real.toNNReal s) ∉ Aᶜ from notMem_compl_iff.2 hmem) _

theorem outside_functional_pos_after_exit {d : ℕ}
    (A : Set (Fin d → ℝ)) (hA : IsClosed A) (w : ContinuousPath (Fin d → ℝ))
    (t : NNReal) (ht : ContinuousPath.exitTime A w < (t : ℝ≥0∞)) :
    0 < SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional (outsidePotential A) t w := by
  obtain ⟨_, ⟨s, rfl, hsbad⟩, hst⟩ := sInf_lt_iff.1 ht
  have hst' : s < t := ENNReal.coe_lt_coe.1 hst
  let O : Set NNReal := (w : NNReal → Fin d → ℝ) ⁻¹' Aᶜ ∩ Iio t
  have hO : IsOpen O := (hA.isOpen_compl.preimage w.continuous).inter isOpen_Iio
  obtain ⟨a, b, hab, hsub⟩ := hO.exists_Ioo_subset ⟨s, hsbad, hst'⟩
  let g : ℝ → ℝ := fun r => outsidePotential A (w (Real.toNNReal r))
  have hg : Measurable g := (outsidePotential_measurable A hA).comp
    (w.continuous.measurable.comp measurable_real_toNNReal)
  have hgi : IntervalIntegrable g volume 0 t := by
    rw [intervalIntegrable_iff, uIoc_of_le t.coe_nonneg]
    apply IntegrableOn.of_bound measure_Ioc_lt_top hg.aestronglyMeasurable.restrict 1
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (outsidePotential_nonneg A _)]
    exact outsidePotential_le_one A _
  have hsupport : Ioo (a : ℝ) (b : ℝ) ⊆ Function.support g ∩ Ioc 0 (t : ℝ) := by
    intro r hr
    have hr0 : 0 ≤ r := a.coe_nonneg.trans hr.1.le
    have hrt : Real.toNNReal r ∈ Ioo a b := by
      constructor
      · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]
        exact hr.1
      · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]
        exact hr.2
    have hbad : w (Real.toNNReal r) ∈ Aᶜ := (hsub hrt).1
    have hrone : g r = 1 := indicator_of_mem hbad _
    refine ⟨by rw [Function.mem_support, hrone]; exact one_ne_zero, ?_, ?_⟩
    · exact a.coe_nonneg.trans_lt hr.1
    · have hrlt : Real.toNNReal r < t := (hsub hrt).2
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0] at hrlt
      exact hrlt.le
  have hpos : 0 < volume (Function.support g ∩ Ioc 0 (t : ℝ)) := by
    have hvol : 0 < volume (Ioo (a : ℝ) (b : ℝ)) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.2 (sub_pos.2 (NNReal.coe_lt_coe.2 hab))
    exact hvol.trans_le (measure_mono hsupport)
  have ht0 : (0 : ℝ) < t := by
    have h := (zero_le s).trans_lt hst'
    exact NNReal.coe_pos.2 h
  exact (intervalIntegral.integral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun r => outsidePotential_nonneg A _) hgi).2 ⟨ht0, hpos⟩

theorem penalty_weight_tendsto_of_ne {d : ℕ}
    (A : Set (Fin d → ℝ)) (hA : IsClosed A) (w : ContinuousPath (Fin d → ℝ))
    (t : ℝ) (ht : 0 < t) (hne : ENNReal.ofReal t ≠ ContinuousPath.exitTime A w) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp
      (-SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional
        (penalty A n) (Real.toNNReal t) w))) atTop
      (𝓝 ({t : ℝ | ENNReal.ofReal t < ContinuousPath.exitTime A w}.indicator
        (fun _ => (1 : ℝ≥0∞)) t)) := by
  rcases lt_or_gt_of_ne hne with hbefore | hafter
  · rw [indicator_of_mem (show t ∈ {t | ENNReal.ofReal t < ContinuousPath.exitTime A w} from hbefore)]
    have hz := outside_functional_eq_zero_before_exit A w (Real.toNNReal t) hbefore
    simp only [penalty_functional_eq, hz, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact tendsto_const_nhds
  · rw [indicator_of_notMem
      (show t ∉ {t | ENNReal.ofReal t < ContinuousPath.exitTime A w} from not_lt_of_gt hafter)]
    have hc := outside_functional_pos_after_exit A hA w (Real.toNNReal t) hafter
    have hinfty : Tendsto (fun n : ℕ => (n : ℝ) *
        SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional
          (outsidePotential A) (Real.toNNReal t) w) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const' hc
    have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hinfty
    simpa only [penalty_functional_eq, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.tendsto_ofReal hexp

theorem ae_ofReal_ne_exit {d : ℕ} (A : Set (Fin d → ℝ))
    (w : ContinuousPath (Fin d → ℝ)) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ENNReal.ofReal t ≠ ContinuousPath.exitTime A w := by
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ (ContinuousPath.exitTime A w).toReal := by
    simp only [ae_iff, not_not, setOf_eq_eq_singleton, measure_singleton]
  filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_Ioi] with t ht hpos heq
  apply ht
  rw [← heq, ENNReal.toReal_ofReal hpos.le]

end SubdiffusiveProcess.PartProcess
