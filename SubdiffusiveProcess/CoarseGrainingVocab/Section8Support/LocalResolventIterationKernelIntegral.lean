module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKernel
@[expose] public section

/-!
# Integral formulas for killed resolvent kernels

The occupation formula is retained for integrable data and transported almost everywhere
by kernel subinvariance. All identities use the raw resolvent from the source vocabulary.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal ProbabilityTheory
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration

theorem integral_expMeasure (s : ℝ) (hs : 0 < s) (g : ℝ → ℝ) : (∫ t, g t ∂expMeasure s⁻¹) = s⁻¹ * ∫ t in Ioi (0:ℝ), Real.exp (-t/s) * g t := by
  have hr : 0 < s⁻¹ := inv_pos.mpr hs
  change (∫ t, g t ∂volume.withDensity (exponentialPDF s⁻¹)) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (exponentialPDF s⁻¹) from (measurable_exponentialPDFReal s⁻¹).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun t => show exponentialPDF s⁻¹ t < ∞ from ENNReal.ofReal_lt_top))]
  have hfun : (fun t => (exponentialPDF s⁻¹ t).toReal • g t) =
      (Ici (0:ℝ)).indicator (fun t => s⁻¹ * (Real.exp (-t/s) * g t)) := by
    funext t
    by_cases ht : 0 ≤ t
    · rw [exponentialPDF_of_nonneg ht, ENNReal.toReal_ofReal (by positivity),
        Set.indicator_of_mem (show t ∈ Ici (0:ℝ) from ht)]
      simp only [smul_eq_mul]
      rw [show -(s⁻¹ * t) = -t/s by ring]
      ring
    · rw [exponentialPDF_of_neg (lt_of_not_ge ht), ENNReal.toReal_zero,
        zero_smul, Set.indicator_of_notMem (show t ∉ Ici (0:ℝ) from ht)]
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul]
theorem integral_map_restrict {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] (κ : Kernel α β) (S : Set β) (hS : MeasurableSet S) (g : β → γ) (hg : Measurable g) (a : α) (f : γ → ℝ) (hf : Measurable f) : (∫ z, f z ∂((κ.restrict hS).map g) a) = ∫ z in S, f (g z) ∂κ a := by
  rw [Kernel.map_apply _ hg a, integral_map hg.aemeasurable hf.aestronglyMeasurable,
    Kernel.restrict_apply]

theorem resolventKernel_integral_product {d : ℕ} (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law] (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s) (f : Vec d → ℝ) (hf : Measurable f) (x : Vec d) : kernelIntegral (resolventKernel law U hU s hs) f x = ∫ q in {q : ℝ × Path d | ENNReal.ofReal q.1 < LifetimePath.exitTime U q.2}, f (position (Real.toNNReal q.1) q.2) ∂((expMeasure s⁻¹).prod (law x)) := by
  letI := exponential_probability s hs
  unfold kernelIntegral resolventKernel
  rw [Kernel.map_apply _ joint_position, integral_map joint_position.aemeasurable hf.aestronglyMeasurable,
    Kernel.restrict_apply, Kernel.prod_apply, Kernel.const_apply]

theorem occupation_integrable {d : ℕ} (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law] (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s) (f : Vec d → ℝ) (hf : Measurable f) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x, |f x| ≤ K) (x : Vec d) : Integrable ({q : ℝ × Path d | ENNReal.ofReal q.1 < LifetimePath.exitTime U q.2}.indicator (fun q => f (position (Real.toNNReal q.1) q.2))) ((expMeasure s⁻¹).prod (law x)) := by
  letI := exponential_probability s hs
  refine (integrable_const K).mono' (((hf.comp joint_position).indicator (survival_measurable U hU)).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun q => by
    by_cases hq : q ∈ {q : ℝ × Path d | ENNReal.ofReal q.1 < LifetimePath.exitTime U q.2}
    · rw [Set.indicator_of_mem hq]
      simpa only [Real.norm_eq_abs] using hb _
    · rw [Set.indicator_of_notMem hq]
      simpa using hK)

theorem subinvariant_of_rectangle_symmetry {α : Type*} [MeasurableSpace α] (μ : Measure α) (κ : Kernel α α) (hκ : IsSubMarkovKernel κ) (hsym : ∀ C D : Set α, MeasurableSet C → MeasurableSet D → (∫⁻ x in C, κ x D ∂μ) = ∫⁻ x in D, κ x C ∂μ) : κ ∘ₘ μ ≤ μ := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.bind_apply hB κ.aemeasurable]
  calc
    (∫⁻ x, κ x B ∂μ) = ∫⁻ x in Set.univ, κ x B ∂μ := by rw [Measure.restrict_univ]
    _ = ∫⁻ x in B, κ x Set.univ ∂μ := hsym Set.univ B MeasurableSet.univ hB
    _ ≤ ∫⁻ x in B, 1 ∂μ := lintegral_mono (fun x => hκ x)
    _ = μ B := by simp


theorem killedKernel_integral {d : ℕ} (law : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) (f : Vec d → ℝ) (hf : Measurable f) (x : Vec d) : kernelIntegral (killedKernel law U hU t) f x = ∫ w in {w : Path d | (t : ENNReal) < LifetimePath.exitTime U w}, f (position t w) ∂law x := by
  unfold kernelIntegral killedKernel
  rw [Kernel.map_apply _ (position_fixed_measurable t),
    integral_map (position_fixed_measurable t).aemeasurable hf.aestronglyMeasurable,
    Kernel.restrict_apply]

theorem kernelIntegral_indicator_one {α : Type*} [MeasurableSpace α] (κ : Kernel α α) (D : Set α) (hD : MeasurableSet D) (x : α) : kernelIntegral κ (D.indicator (fun _ : α => (1 : ℝ))) x = (κ x D).toReal := by
  unfold kernelIntegral
  rw [integral_indicator hD, setIntegral_const]
  simp [measureReal_def]

/-- The raw occupation integral agrees with the resolvent kernel whenever the latter is integrable. -/
theorem resolventKernel_integral_eq_of_integrable {d : ℕ}
    (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s)
    (f : Vec d → ℝ) (x : Vec d)
    (hf : Integrable f (resolventKernel law U hU s hs x)) :
    kernelIntegral (resolventKernel law U hU s hs) f x = killedResolvent law U s f x := by
  letI := exponential_probability s hs
  let P := (expMeasure s⁻¹).prod (law x)
  let S := {q : ℝ × Path d | ENNReal.ofReal q.1 < LifetimePath.exitTime U q.2}
  let z := fun q : ℝ × Path d => position (Real.toNNReal q.1) q.2
  have hS : MeasurableSet S := survival_measurable U hU
  have hz : Measurable z := joint_position
  have hmeasure : resolventKernel law U hU s hs x = (P.restrict S).map z := by
    unfold resolventKernel
    rw [Kernel.map_apply _ joint_position, Kernel.restrict_apply, Kernel.prod_apply,
      Kernel.const_apply]
  have hfmap : Integrable f ((P.restrict S).map z) := by rwa [hmeasure] at hf
  have hcomp : Integrable (fun q => f (z q)) (P.restrict S) :=
    (integrable_map_measure hfmap.1 hz.aemeasurable).mp hfmap
  have hind : Integrable (S.indicator (fun q => f (z q))) P :=
    (integrable_indicator_iff hS).mpr hcomp
  have hin : ∀ t : ℝ, (∫ w, (S.indicator (fun q => f (z q))) (t,w) ∂law x) =
      ∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w},
        f (position (Real.toNNReal t) w) ∂law x := by
    intro t
    change (∫ w, ({w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w}.indicator
      (fun w => f (position (Real.toNNReal t) w))) w ∂law x) = _
    have htime : Measurable (LifetimePath.exitTime U : Path d → ENNReal) := by
      simpa only using! (LifetimePath.isStoppingTime_exitTime U hU).measurable'
    simpa only using! (integral_indicator (μ := law x)
      (f := fun w => f (position (Real.toNNReal t) w))
      (measurableSet_lt measurable_const htime))
  change (∫ y, f y ∂resolventKernel law U hU s hs x) = _
  rw [hmeasure, integral_map hz.aemeasurable hfmap.1, ← integral_indicator hS]
  rw [integral_prod _ hind]
  simp only [hin]
  exact integral_expMeasure s hs _

/-- Subinvariance transfers the raw occupation formula to every integrable datum. -/
theorem resolventKernel_integral_ae {d : ℕ}
    (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s)
    (μ : Measure (Vec d)) (hμ : resolventKernel law U hU s hs ∘ₘ μ ≤ μ)
    (f : Vec d → ℝ) (hf : Integrable f μ) :
    kernelIntegral (resolventKernel law U hU s hs) f =ᵐ[μ] killedResolvent law U s f := by
  have hcomp := hf.mono_measure hμ
  filter_upwards [Measure.ae_integrable_of_integrable_comp hcomp] with x hx
  exact resolventKernel_integral_eq_of_integrable law U hU s hs f x hx

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
