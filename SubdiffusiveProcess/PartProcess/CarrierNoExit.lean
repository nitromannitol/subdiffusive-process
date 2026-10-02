import SubdiffusiveProcess.PartProcess.CompactCoverExit
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7

theorem nonexit_of_equal_occupations {d : ℕ}
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) (hK : IsMarkovKernel K)
    (V : Set (Fin d → ℝ)) (hV : IsOpen V) (α : ℝ)
    (f : ℕ → (Fin d → ℝ) → ℝ) (hf : ∀ n, Measurable (f n))
    (hcover : ∀ z, ∃ n, 0 < f n z) (x : Fin d → ℝ)
    (hfinite : ∀ n, potentialOcc K 0 α (f n) x < ⊤)
    (heq : ∀ n, killedOcc K V α (f n) x = potentialOcc K 0 α (f n) x) :
    ∀ᵐ w ∂(K x), LifetimePath.exitTime V (LifetimePath.ofContinuousPath w) = ⊤ := by
  letI := hK
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let S : Set (ℝ × ContinuousPath (Fin d → ℝ)) :=
    {p | ENNReal.ofReal p.1 < ContinuousPath.exitTime V p.2}
  have hS : MeasurableSet S := measurableSet_lt
    (ENNReal.measurable_ofReal.comp measurable_fst)
    ((ContinuousPath.measurable_exitTime V hV).comp measurable_snd)
  let F : ℕ → ℝ × ContinuousPath (Fin d → ℝ) → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (Real.exp (-α * p.1)) * ENNReal.ofReal (f n (p.2 (Real.toNNReal p.1)))
  have hF : ∀ n, Measurable (F n) := fun n =>
    (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).measurable).mul
      (ENNReal.measurable_ofReal.comp ((hf n).comp aux_n8_measurable_eval))
  have htest : ∀ n t, Measurable (fun w : ContinuousPath (Fin d → ℝ) =>
      ENNReal.ofReal (f n (w (Real.toNNReal t)))) := fun n t =>
    ENNReal.measurable_ofReal.comp ((hf n).comp (ContinuousPath.measurable_coordinateProcess _))
  have hfree : ∀ n, ∫⁻ p, F n p ∂(μ.prod (K x)) = potentialOcc K 0 α (f n) x := by
    intro n
    rw [lintegral_prod _ (hF n).aemeasurable]
    unfold potentialOcc
    simp only [SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional,
      Pi.zero_apply, intervalIntegral.integral_zero, neg_zero, Real.exp_zero,
      ENNReal.ofReal_one, one_mul]
    apply lintegral_congr
    intro t
    change (∫⁻ w, ENNReal.ofReal (Real.exp (-α * t)) *
      ENNReal.ofReal (f n (w (Real.toNNReal t))) ∂K x) = _
    exact lintegral_const_mul _ (htest n t)
  have hkilled : ∀ n, ∫⁻ p, S.indicator (F n) p ∂(μ.prod (K x)) =
      killedOcc K V α (f n) x := by
    intro n
    rw [lintegral_prod _ ((hF n).indicator hS).aemeasurable, killedOcc_continuousPath]
    apply lintegral_congr
    intro t
    rw [← lintegral_indicator
      (measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime V hV))]
    rw [← lintegral_const_mul _ ((htest n t).indicator
      (measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime V hV)))]
    apply lintegral_congr
    intro w
    change S.indicator (F n) (t, w) = _
    by_cases h : ENNReal.ofReal t < ContinuousPath.exitTime V w
    · rw [Set.indicator_of_mem (show (t, w) ∈ S from h),
        Set.indicator_of_mem (show w ∈ {w | ENNReal.ofReal t < ContinuousPath.exitTime V w} from h)]
    · rw [Set.indicator_of_notMem (show (t, w) ∉ S from h),
        Set.indicator_of_notMem (show w ∉ {w | ENNReal.ofReal t < ContinuousPath.exitTime V w} from h),
        mul_zero]
  have H : ∀ n, ∀ᵐ w ∂(K x), ∀ᵐ t ∂μ,
      S.indicator (F n) (t, w) = F n (t, w) := by
    intro n
    have hcomp : S.indicator (F n) =ᵐ[μ.prod (K x)] F n :=
      ae_eq_of_ae_le_of_lintegral_le
        (Eventually.of_forall fun p => indicator_le_self S (F n) p)
        (by rw [hkilled n, heq n]; exact (hfinite n).ne)
        (hF n).aemeasurable (by rw [hfree n, hkilled n, heq n])
    exact (Measure.ae_ae_comm
      (p := fun t w => S.indicator (F n) (t, w) = F n (t, w))
      (measurableSet_eq_fun (f := S.indicator (F n)) (g := F n)
        ((hF n).indicator hS) (hF n))).1
      (Measure.ae_ae_of_ae_prod hcomp)
  filter_upwards [ae_all_iff.2 H] with w hw
  have hsurvive : ∀ᵐ t ∂μ, ENNReal.ofReal t < ContinuousPath.exitTime V w := by
    filter_upwards [ae_all_iff.2 hw] with t ht
    obtain ⟨n, hn⟩ := hcover (w (Real.toNNReal t))
    by_contra hbad
    have he := ht n
    rw [indicator_of_notMem (show (t, w) ∉ S from hbad)] at he
    have hpos : 0 < F n (t, w) := ENNReal.mul_pos
      (ne_of_gt (ENNReal.ofReal_pos.2 (Real.exp_pos _))) (ne_of_gt (ENNReal.ofReal_pos.2 hn))
    exact (ne_of_gt hpos) he.symm
  rw [LifetimePath.exitTime_ofContinuousPath]
  by_contra htop
  let a := (ContinuousPath.exitTime V w).toReal + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hμ : μ (Ioo a (a + 1)) ≠ 0 := by
    have hsub : Ioo a (a + 1) ⊆ Ioi (0 : ℝ) := fun t ht => ha.trans ht.1
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.2 hsub, Real.volume_Ioo]
    simp only [add_sub_cancel_left, ENNReal.ofReal_one, ne_eq, one_ne_zero, not_false_eq_true]
  obtain ⟨t, ht, hta⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hμ
    (ae_restrict_of_ae hsurvive)
  have hlt := (ENNReal.ofReal_lt_iff_lt_toReal (ha.trans ht.1).le htop).1 hta
  dsimp [a] at ht
  linarith [ht.1]

end SubdiffusiveProcess.PartProcess
