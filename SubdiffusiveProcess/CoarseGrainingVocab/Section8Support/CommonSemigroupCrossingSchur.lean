module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import MarkovProcess.Kernel.LpFinite

@[expose] public section




set_option autoImplicit false
open MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal ProbabilityTheory
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossingSchur
variable {α : Type*} [MeasurableSpace α]
/-- Restrict a kernel from `F` to `E` and divide its mass by `K`. -/
def scaledCut (κ : Kernel α α) {E F : Set α} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (K : ℝ) : Kernel α α where
  toFun x := (ENNReal.ofReal K)⁻¹ • Kernel.piecewise hF (κ.restrict hE) 0 x
  measurable' := by
    apply Measure.measurable_measure.mpr
    intro B hB
    exact measurable_const.mul ((Kernel.piecewise hF (κ.restrict hE) 0).measurable_coe hB)

theorem scaledCut_apply (κ : Kernel α α) {E F : Set α} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (K : ℝ) (x : α) :
    scaledCut κ hE hF K x =
      (ENNReal.ofReal K)⁻¹ • (if x ∈ F then (κ x).restrict E else 0) := by
  rw [scaledCut, Kernel.coe_mk, Kernel.piecewise_apply]
  split_ifs <;> rfl

theorem inverse_mul_ofReal (K : ℝ) (hK : 0 < K) :
    (ENNReal.ofReal K)⁻¹ * ENNReal.ofReal K = 1 :=
  ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hK)) ENNReal.ofReal_ne_top

theorem scaledCut_subMarkov (κ : Kernel α α) {E F : Set α} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (K : ℝ) (hK : 0 < K)
    (hr : ∀ x ∈ F, κ x E ≤ ENNReal.ofReal K) :
    IsSubMarkovKernel (scaledCut κ hE hF K) := by
  intro x
  rw [scaledCut_apply]
  by_cases hx : x ∈ F
  · rw [ite_eq_left hx, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter]
    exact (mul_le_mul_right (hr x hx) _).trans_eq (inverse_mul_ofReal K hK)
  · rw [ite_eq_right hx, smul_zero, Measure.coe_zero, Pi.zero_apply]
    exact zero_le

theorem rectangle_bound (μ : Measure α) (κ : Kernel α α)
    {E F B : Set α} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hB : MeasurableSet B) (K : ℝ≥0∞)
    (hs : ∀ C D : Set α, MeasurableSet C → MeasurableSet D →
      (∫⁻ x in C, κ x D ∂μ) = ∫⁻ x in D, κ x C ∂μ)
    (hr : ∀ x ∈ E, κ x F ≤ K) :
    (∫⁻ x in F, κ x (B ∩ E) ∂μ) ≤ K * μ B := by
  rw [hs F (B ∩ E) hF (hB.inter hE)]
  calc
    (∫⁻ x in B ∩ E, κ x F ∂μ) ≤ ∫⁻ x in B ∩ E, K ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hB.inter hE)] with x hx
      exact hr x hx.2
    _ = K * μ (B ∩ E) := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    _ ≤ K * μ B := mul_le_mul_right (measure_mono Set.inter_subset_left) K

theorem scaledCut_subinvariant (μ : Measure α) (κ : Kernel α α)
    {E F : Set α} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (K : ℝ) (hK : 0 < K)
    (hs : ∀ C D : Set α, MeasurableSet C → MeasurableSet D →
      (∫⁻ x in C, κ x D ∂μ) = ∫⁻ x in D, κ x C ∂μ)
    (hr : ∀ x ∈ E, κ x F ≤ ENNReal.ofReal K) :
    scaledCut κ hE hF K ∘ₘ μ ≤ μ := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.bind_apply hB (Kernel.aemeasurable _)]
  have heq : (fun x => scaledCut κ hE hF K x B) =
      fun x => (ENNReal.ofReal K)⁻¹ * F.indicator (fun x => κ x (B ∩ E)) x := by
    funext x
    rw [scaledCut_apply, Measure.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ F
    · rw [ite_eq_left hx, Set.indicator_of_mem hx, Measure.restrict_apply hB]
    · rw [ite_eq_right hx, Set.indicator_of_notMem hx, Measure.coe_zero, Pi.zero_apply]
  rw [heq, lintegral_const_mul _ (Measurable.indicator (κ.measurable_coe (hB.inter hE)) hF),
    lintegral_indicator hF]
  calc
    (ENNReal.ofReal K)⁻¹ * (∫⁻ x in F, κ x (B ∩ E) ∂μ)
        ≤ (ENNReal.ofReal K)⁻¹ * (ENNReal.ofReal K * μ B) :=
      mul_le_mul_right (rectangle_bound μ κ hE hF hB _ hs hr) _
    _ = μ B := by rw [← mul_assoc, inverse_mul_ofReal K hK, one_mul]

theorem scaledCut_integral (κ : Kernel α α) {E F : Set α} (hE : MeasurableSet E)
    (hF : MeasurableSet F) (K : ℝ) (hK : 0 < K) (f : α → ℝ) (x : α) :
    kernelIntegral (scaledCut κ hE hF K) f x =
      K⁻¹ * F.indicator (fun x => ∫ y, E.indicator f y ∂κ x) x := by
  rw [kernelIntegral, scaledCut_apply, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hK.le]
  by_cases hx : x ∈ F
  · rw [ite_eq_left hx, Set.indicator_of_mem hx, integral_indicator hE]
    rfl
  · rw [ite_eq_right hx, Set.indicator_of_notMem hx, integral_zero_measure, mul_zero, smul_zero]

/-- Equal row and column bounds for a symmetric kernel give the L² Schur estimate. -/
theorem eLpNorm_schur (μ : Measure α) (κ : Kernel α α)
    {E F : Set α} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (K : ℝ) (hK : 0 < K)
    (hs : ∀ C D : Set α, MeasurableSet C → MeasurableSet D →
      (∫⁻ x in C, κ x D ∂μ) = ∫⁻ x in D, κ x C ∂μ)
    (hr : ∀ x ∈ E, κ x F ≤ ENNReal.ofReal K)
    (hc : ∀ x ∈ F, κ x E ≤ ENNReal.ofReal K)
    (f : α → ℝ) (hf : MemLp f 2 μ) :
    eLpNorm (F.indicator (fun x => ∫ y, E.indicator f y ∂κ x)) 2 μ ≤
      ENNReal.ofReal K * eLpNorm f 2 μ := by
  have hκ := scaledCut_subMarkov κ hE hF K hK hc
  have hκμ := scaledCut_subinvariant μ κ hE hF K hK hs hr
  have hnorm := eLpNorm_kernelIntegral_le hκ hκμ (p := (2 : NNReal)) (by norm_num) hf
  have hid : F.indicator (fun x => ∫ y, E.indicator f y ∂κ x) =
      K • kernelIntegral (scaledCut κ hE hF K) f := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul, scaledCut_integral κ hE hF K hK f x,
      ← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
  rw [hid, eLpNorm_const_smul, Real.enorm_eq_ofReal hK.le]
  exact mul_le_mul_right hnorm _

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The measurable embedding of live states into the cemetery space. -/
theorem inlEmbedding : MeasurableEmbedding (Sum.inl : α → α ⊕ Unit) :=
  ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩

omit [MeasurableSpace α] in
theorem sum_elim_zero_indicator (f : α → ℝ) :
    (range (Sum.inl : α → α ⊕ Unit)).indicator (Sum.elim f (fun _ => 0)) =
      Sum.elim f (fun _ => 0) := by
  funext z
  cases z with
  | inl x => exact Set.indicator_of_mem (Set.mem_range_self x) _
  | inr u =>
      exact Set.indicator_of_notMem (by rintro ⟨x, hx⟩; cases hx) _

theorem sum_elim_zero_aestronglyMeasurable (ν : Measure (α ⊕ Unit)) (f : α → ℝ)
    (hf : AEStronglyMeasurable f (ν.comap Sum.inl)) :
    AEStronglyMeasurable (Sum.elim f (fun _ => 0)) ν := by
  rw [← sum_elim_zero_indicator f, aestronglyMeasurable_indicator_iff
    (inlEmbedding.measurableSet_range)]
  rw [← inlEmbedding.map_comap ν]
  exact inlEmbedding.aestronglyMeasurable_map_iff.mpr hf

theorem integral_sum_elim_zero (ν : Measure (α ⊕ Unit)) (f : α → ℝ) :
    (∫ z, z.elim f (fun _ => 0) ∂ν) = ∫ y, f y ∂ν.comap Sum.inl := by
  calc
    (∫ z, z.elim f (fun _ => 0) ∂ν) =
        ∫ z, (range (Sum.inl : α → α ⊕ Unit)).indicator
          (Sum.elim f (fun _ => 0)) z ∂ν := by
      rw [sum_elim_zero_indicator]
    _ = ∫ z in range (Sum.inl : α → α ⊕ Unit), z.elim f (fun _ => 0) ∂ν :=
      integral_indicator inlEmbedding.measurableSet_range
    _ = ∫ y, f y ∂ν.comap Sum.inl := by
      rw [← inlEmbedding.map_comap ν,
        inlEmbedding.integral_map]
      rfl

theorem integral_map_sum_elim_zero (ν : Measure β) (v : β → α ⊕ Unit)
    (hv : Measurable v) (f : α → ℝ)
    (hf : AEStronglyMeasurable f ((ν.map v).comap Sum.inl)) :
    (∫ w, (v w).elim f (fun _ => 0) ∂ν) =
      ∫ y, f y ∂(ν.map v).comap Sum.inl := by
  rw [← integral_map hv.aemeasurable (sum_elim_zero_aestronglyMeasurable _ _ hf)]
  exact integral_sum_elim_zero _ _

/-- The live-state part of the coordinate marginal of a path kernel. -/
def coordinateKernel {d : ℕ} (law : Kernel (Vec d) (Path d)) (t : NNReal) :
    Kernel (Vec d) (Vec d) :=
  (law.map (LifetimePath.coordinate t)).comapRight inlEmbedding

theorem coordinateKernel_apply {d : ℕ} (law : Kernel (Vec d) (Path d)) (t : NNReal)
    (x : Vec d) (B : Set (Vec d)) (hB : MeasurableSet B) :
    coordinateKernel law t x B =
      law x {w | LifetimePath.coordinate t w ∈ Cemetery.alive '' B} := by
  rw [coordinateKernel, Kernel.comapRight_apply' _ _ _ hB,
    Kernel.map_apply' _ (LifetimePath.measurable_coordinate t) _ hB.inl_image]
  rfl

theorem coordinateKernel_integral {d : ℕ} (law : Kernel (Vec d) (Path d)) (t : NNReal)
    (x : Vec d) (f : Vec d → ℝ) (hf : AEStronglyMeasurable f (coordinateKernel law t x)) :
    (∫ w, (LifetimePath.coordinate t w).elim f (fun _ => 0) ∂law x) =
      ∫ y, f y ∂coordinateKernel law t x := by
  change (∫ w, (LifetimePath.coordinate t w).elim f (fun _ => 0) ∂law x) =
    ∫ y, f y ∂(law.map (LifetimePath.coordinate t) x).comap Sum.inl
  rw [Kernel.map_apply _ (LifetimePath.measurable_coordinate t)]
  apply integral_map_sum_elim_zero _ _ (LifetimePath.measurable_coordinate t) f
  simpa only [coordinateKernel, Kernel.comapRight_apply, Kernel.map_apply _
    (LifetimePath.measurable_coordinate t)] using hf



/-- Rectangle symmetry and two crossing-probability bounds imply the frozen
L² path-integral estimate. The argument needs no additional Markov or finiteness
assumption on the input kernel or reference measure. -/
theorem eLpNorm_pathIntegral_le {d : ℕ} (law : Kernel (Vec d) (Path d)) (t : NNReal)
    {E F : Set (Vec d)} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (K : ℝ) (hK : 0 < K) (μ : Measure (Vec d))
    (hs : ∀ B D : Set (Vec d), MeasurableSet B → MeasurableSet D →
      (∫⁻ x in B, law x {w | LifetimePath.coordinate t w ∈ Cemetery.alive '' D} ∂μ) =
        ∫⁻ x in D, law x {w | LifetimePath.coordinate t w ∈ Cemetery.alive '' B} ∂μ)
    (hr : ∀ x ∈ E, law x {w | LifetimePath.coordinate t w ∈ Cemetery.alive '' F} ≤
      ENNReal.ofReal K)
    (hc : ∀ x ∈ F, law x {w | LifetimePath.coordinate t w ∈ Cemetery.alive '' E} ≤
      ENNReal.ofReal K)
    (f : Vec d → ℝ) (hf : MemLp f 2 μ) :
    eLpNorm (F.indicator (fun x => ∫ w,
      (LifetimePath.coordinate t w).elim (E.indicator f) (fun _ => 0) ∂law x)) 2 μ ≤
        ENNReal.ofReal K * eLpNorm f 2 μ := by
  let κ := coordinateKernel law t
  have hsκ : ∀ B D : Set (Vec d), MeasurableSet B → MeasurableSet D →
      (∫⁻ x in B, κ x D ∂μ) = ∫⁻ x in D, κ x B ∂μ := by
    intro B D hB hD
    simp only [κ, coordinateKernel_apply law t _ D hD,
      coordinateKernel_apply law t _ B hB]
    exact hs B D hB hD
  have hrκ : ∀ x ∈ E, κ x F ≤ ENNReal.ofReal K := by
    intro x hx
    rw [coordinateKernel_apply law t x F hF]
    exact hr x hx
  have hcκ : ∀ x ∈ F, κ x E ≤ ENNReal.ofReal K := by
    intro x hx
    rw [coordinateKernel_apply law t x E hE]
    exact hc x hx
  have hκμ := scaledCut_subinvariant μ κ hE hF K hK hsκ hrκ
  have hfComp : AEStronglyMeasurable f (scaledCut κ hE hF K ∘ₘ μ) :=
    hf.aestronglyMeasurable.mono_measure hκμ
  have hfFiber : ∀ᵐ x ∂μ, AEStronglyMeasurable f (scaledCut κ hE hF K x) := by
    filter_upwards [Measure.ae_ae_of_ae_comp hfComp.ae_eq_mk] with x hx
    have hxEq : f =ᵐ[scaledCut κ hE hF K x] hfComp.mk f := hx
    exact hfComp.stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq.symm
  have hbridge : F.indicator (fun x => ∫ w,
        (LifetimePath.coordinate t w).elim (E.indicator f) (fun _ => 0) ∂law x) =ᵐ[μ]
      F.indicator (fun x => ∫ y, E.indicator f y ∂κ x) := by
    filter_upwards [hfFiber] with x hx
    by_cases hxF : x ∈ F
    · rw [Set.indicator_of_mem hxF, Set.indicator_of_mem hxF]
      rw [scaledCut_apply, ite_eq_left hxF] at hx
      have hxn : AEStronglyMeasurable f ((κ x).restrict E) :=
        hx.mono_ac (Measure.absolutelyContinuous_smul
          (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top))
      exact coordinateKernel_integral law t x (E.indicator f)
        ((aestronglyMeasurable_indicator_iff hE).mpr hxn)
    · rw [Set.indicator_of_notMem hxF, Set.indicator_of_notMem hxF]
  rw [eLpNorm_congr_ae hbridge]
  exact eLpNorm_schur μ κ hE hF K hK hsκ hrκ hcκ f hf

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossingSchur
