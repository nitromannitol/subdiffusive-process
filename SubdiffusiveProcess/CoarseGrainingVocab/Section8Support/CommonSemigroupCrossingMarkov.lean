module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

@[expose] public section

/-!
# Strong Markov identities for random sections

Joint measurability of lifetime-path coordinates and shifts allows the fixed-event
Strong Markov identity to extend to events in the product of the stopped sigma-field
and the ambient path sigma-field. Rectangle testing identifies a finite pushforward
measure with the corresponding composition-product measure restricted to that product
sigma-field. The resulting identity gives a conditional bound from almost-everywhere
bounds on the section probabilities.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing

/-- A fixed path is continuous at every time strictly before its lifetime. -/
theorem coordinate_continuous_at {d : ℕ} (w : Path d) (t : NNReal)
    (ht : (t : ENNReal) < w.lifetime) :
    ContinuousAt (fun s => LifetimePath.coordinate s w) t := by
  have hc : ContinuousOn (fun s => LifetimePath.coordinate s w)
      {s : NNReal | (s : ENNReal) < w.lifetime} :=
    continuousOn_iff_continuous_domRestrict.mpr (LifetimePath.continuous_coordinate_before w)
  exact hc.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds ht)

/-- The live-position projection is jointly measurable in time and path. -/
theorem measurable_position_uncurry {d : ℕ} :
    Measurable (fun p : NNReal × Path d => position p.1 p.2) := by
  classical
  let hs : StronglyMeasurable (id : NNReal → NNReal) := stronglyMeasurable_id
  let U (n : ℕ) (p : NNReal × Path d) :=
    if (p.1 : ENNReal) < p.2.lifetime then
      position (hs.approx n p.1) p.2 else 0
  have hlim : Tendsto U atTop (𝓝 fun p => position p.1 p.2) := by
    rw [tendsto_pi_nhds]
    intro p
    by_cases hp : (p.1 : ENNReal) < p.2.lifetime
    · have hc : ContinuousAt (fun s => position s p.2) p.1 :=
        (continuous_id.sumElim continuous_const).continuousAt.comp
          (coordinate_continuous_at p.2 p.1 hp)
      simpa only [U, ite_eq_left hp, Function.comp_def] using! hc.tendsto.comp (hs.tendsto_approx p.1)
    · simpa only [U, ite_eq_right hp, position,
        LifetimePath.coordinate_of_le _ _ (not_lt.mp hp), Sum.elim_inr] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Vec d)) atTop (𝓝 0))
  refine measurable_of_tendsto_metrizable (fun n => ?_) hlim
  have h_eval : Measurable (fun p : (hs.approx n).range × Path d =>
      position (↑p.1) p.2) := by
    rw [show (fun p : (hs.approx n).range × Path d => position (↑p.1) p.2) =
        (fun p : Path d × (hs.approx n).range => position (↑p.2) p.1) ∘
          Prod.swap from rfl,
      @measurable_swap_iff (Path d) (↥(hs.approx n).range)]
    exact measurable_from_prod_countable_left fun j =>
      (measurable_id.sumElim measurable_const).comp (LifetimePath.measurable_coordinate j)
  have h_approx : Measurable (fun p : NNReal × Path d =>
      position (hs.approx n p.1) p.2) := by
    exact h_eval.comp
      ((((hs.approx n).measurable.comp measurable_fst).subtype_mk
        (h := fun _ => SimpleFunc.mem_range_self _ _)).prodMk measurable_snd)
  exact Measurable.ite
    (measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_fst)
      (LifetimePath.measurable_lifetime.comp measurable_snd)) h_approx measurable_const

/-- The cemetery-valued coordinate is jointly measurable in time and path. -/
theorem measurable_coordinate_uncurry {d : ℕ} :
    Measurable (fun p : NNReal × Path d => LifetimePath.coordinate p.1 p.2) := by
  classical
  have hm : Measurable (fun p : NNReal × Path d =>
      if (p.1 : ENNReal) < p.2.lifetime then Cemetery.alive (position p.1 p.2)
      else Cemetery.delta) :=
    Measurable.ite
      (measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_fst)
        (LifetimePath.measurable_lifetime.comp measurable_snd))
      (measurable_inl.comp measurable_position_uncurry) measurable_const
  convert hm using 1
  funext p
  by_cases hp : (p.1 : ENNReal) < p.2.lifetime
  · simp only [ite_eq_left hp, position, LifetimePath.coordinate_of_lt _ _ hp, Sum.elim_inl, id_eq]
  · simp only [ite_eq_right hp, LifetimePath.coordinate_of_le _ _ (not_lt.mp hp)]

/-- The lifetime-path shift is jointly measurable in time and path. -/
theorem measurable_shift_uncurry {d : ℕ} :
    Measurable (fun p : NNReal × Path d => LifetimePath.shift p.1 p.2) := by
  apply Measurable.of_comap_le
  rw [LifetimePath.instMeasurableSpace, MeasurableSpace.comap_sup,
    MeasurableSpace.comap_iSup]
  apply sup_le
  · rw [MeasurableSpace.comap_comp]
    exact ((LifetimePath.measurable_lifetime.comp measurable_snd).sub
      (measurable_coe_nnreal_ennreal.comp measurable_fst)).comap_le
  · rw [iSup_le_iff]
    intro t
    rw [MeasurableSpace.comap_comp]
    have heq : LifetimePath.coordinate t ∘
        (fun p : NNReal × Path d => LifetimePath.shift p.1 p.2) =
        fun p : NNReal × Path d => LifetimePath.coordinate (p.1 + t) p.2 := by
      funext p
      exact LifetimePath.coordinate_shift p.1 t p.2
    rw [heq]
    exact (measurable_coordinate_uncurry.comp
      ((measurable_fst.add_const t).prodMk measurable_snd)).comap_le

/-- Rectangle identities against a smaller sigma-field extend to all measurable random sections.
The kernel needs only ambient measurability. -/
theorem measure_random_section_eq {α β : Type*} {m0 m : MeasurableSpace α} {mb : MeasurableSpace β}
    (hm : m ≤ m0) (μ : @Measure α m0) [IsFiniteMeasure μ]
    (κ : @Kernel α β m0 mb) [IsMarkovKernel κ]
    (φ : α → β) (hφ : @Measurable α β m0 mb φ)
    (htest : ∀ B D, MeasurableSet[m] B → MeasurableSet[mb] D →
      μ (B ∩ φ ⁻¹' D) = ∫⁻ a in B, κ a D ∂μ)
    (E : Set (α × β)) (hE : MeasurableSet[m.prod mb] E) :
    μ ((fun a => (a, φ a)) ⁻¹' E) = ∫⁻ a, κ a (Prod.mk a ⁻¹' E) ∂μ := by
  have hpair : @Measurable α (α × β) m0 (m.prod mb) (fun a => (a, φ a)) :=
    (measurable_id'' hm).prodMk hφ
  have hprod : m.prod mb ≤ m0.prod mb := by
    have hi : @Measurable (α × β) (α × β) (m0.prod mb) (m.prod mb) id :=
      (measurable_id'' hm).prodMap measurable_id
    exact fun s hs => hi hs
  let ν : @Measure (α × β) (m.prod mb) := @Measure.map α (α × β) m0 (m.prod mb)
    (fun a => (a, φ a)) μ
  have heq : ν = (μ ⊗ₘ κ).trim hprod := by
    apply Measure.ext_prod
    intro B D hB hD
    rw [show ν (B ×ˢ D) = μ ((fun a => (a, φ a)) ⁻¹' (B ×ˢ D)) from
        Measure.map_apply hpair (hB.prod hD),
      trim_measurableSet_eq hprod (hB.prod hD),
      Measure.compProd_apply_prod (hm _ hB) hD]
    exact htest B D hB hD
  calc
    μ ((fun a => (a, φ a)) ⁻¹' E) = ν E := (Measure.map_apply hpair hE).symm
    _ = ((μ ⊗ₘ κ).trim hprod) E := congrArg (fun η => η E) heq
    _ = (μ ⊗ₘ κ) E := trim_measurableSet_eq hprod hE
    _ = ∫⁻ a, κ a (Prod.mk a ⁻¹' E) ∂μ := Measure.compProd_apply (hprod _ hE)

/-- The normalization clause of `StrongMarkov` gives a Markov kernel. -/
theorem is_markov_kernel_of_strong_markov {d : ℕ} {law : Kernel (Vec d) (Path d)}
    (hSM : StrongMarkov law) : IsMarkovKernel law :=
  ⟨fun x => ⟨hSM.1 x⟩⟩

/-- The fixed-event Strong Markov identity, expressed as a probability identity. -/
theorem strong_markov_set_eq {d : ℕ} {law : Kernel (Vec d) (Path d)}
    (hSM : StrongMarkov law) (x : Vec d) (T : Path d → ENNReal)
    (hT : IsStoppingTime LifetimePath.canonicalFiltration T)
    (B : Set (Path d)) (hB : MeasurableSet[hT.measurableSpace] B)
    (D : Set (Path d)) (hD : MeasurableSet D) :
    law x ((B ∩ {w | T w < w.lifetime}) ∩
      (fun w => LifetimePath.shift (T w).toNNReal w) ⁻¹' D) =
      ∫⁻ w in B ∩ {w | T w < w.lifetime}, law (position (T w).toNNReal w) D ∂law x := by
  have hshift : Measurable (fun w => LifetimePath.shift (T w).toNNReal w) :=
    measurable_shift_uncurry.comp (hT.measurable'.ennreal_toNNReal.prodMk measurable_id)
  have hind : (fun w => D.indicator (fun _ : Path d => (1 : ENNReal))
      (LifetimePath.shift (T w).toNNReal w)) =
      ((fun w => LifetimePath.shift (T w).toNNReal w) ⁻¹' D).indicator
        (fun _ => (1 : ENNReal)) := by
    funext w
    exact (Set.indicator_comp_right _).symm
  have h := hSM.2.2 x T hT B hB (D.indicator (fun _ => (1 : ENNReal)))
    (measurable_const.indicator hD)
  rw [hind, lintegral_indicator (hD.preimage hshift), lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, one_mul, Set.univ_inter,
    Measure.restrict_apply (hD.preimage hshift), Set.inter_comm] at h
  simpa only [lintegral_indicator hD, lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul] using h

/-- Strong Markov disintegration for an event depending on the stopped path and its future. -/
theorem strong_markov_random_section_eq {d : ℕ} {law : Kernel (Vec d) (Path d)}
    (hSM : StrongMarkov law) (x : Vec d) (T : Path d → ENNReal)
    (hT : IsStoppingTime LifetimePath.canonicalFiltration T)
    (event : Set (Path d × Path d))
    (hevent : MeasurableSet[hT.measurableSpace.prod inferInstance] event)
    (B : Set (Path d)) (hB : MeasurableSet[hT.measurableSpace] B) :
    law x (B ∩ {w | T w < w.lifetime ∧
      (w, LifetimePath.shift (T w).toNNReal w) ∈ event}) =
      ∫⁻ w in B ∩ {w | T w < w.lifetime},
        law (position (T w).toNNReal w) {v | (w, v) ∈ event} ∂law x := by
  let : IsMarkovKernel law := is_markov_kernel_of_strong_markov hSM
  have hp : Measurable (fun w => position (T w).toNNReal w) :=
    measurable_position_uncurry.comp (hT.measurable'.ennreal_toNNReal.prodMk measurable_id)
  have hs : Measurable (fun w => LifetimePath.shift (T w).toNNReal w) :=
    measurable_shift_uncurry.comp (hT.measurable'.ennreal_toNNReal.prodMk measurable_id)
  let A : Set (Path d) := B ∩ {w | T w < w.lifetime}
  let μ := (law x).restrict A
  let κ := law.comap (fun w => position (T w).toNNReal w) hp
  have htest : ∀ D E, MeasurableSet[hT.measurableSpace] D → MeasurableSet E →
      μ (D ∩ (fun w => LifetimePath.shift (T w).toNNReal w) ⁻¹' E) =
        ∫⁻ w in D, κ w E ∂μ := by
    intro D E hD hE
    have hD' : MeasurableSet D := hT.measurableSpace_le _ hD
    change (law x).restrict A (D ∩ (fun w => LifetimePath.shift (T w).toNNReal w) ⁻¹' E) =
      ∫⁻ w in D, law (position (T w).toNNReal w) E ∂(law x).restrict A
    rw [Measure.restrict_apply (hD'.inter (hE.preimage hs)), Measure.restrict_restrict hD']
    have h1 : (D ∩ (fun w => LifetimePath.shift (T w).toNNReal w) ⁻¹' E) ∩ A =
        ((B ∩ D) ∩ {w | T w < w.lifetime}) ∩
          (fun w => LifetimePath.shift (T w).toNNReal w) ⁻¹' E := by
      dsimp only [A]
      ext w
      simp only [Set.mem_inter_iff]
      tauto
    have h2 : D ∩ A = (B ∩ D) ∩ {w | T w < w.lifetime} := by
      dsimp only [A]
      ext w
      simp only [Set.mem_inter_iff]
      tauto
    rw [h1, h2]
    exact strong_markov_set_eq hSM x T hT (B ∩ D) (hB.inter hD) E hE
  have h := measure_random_section_eq hT.measurableSpace_le μ κ
    (fun w => LifetimePath.shift (T w).toNNReal w) hs htest event hevent
  dsimp only [μ] at h
  have hpair : Measurable[inferInstance, hT.measurableSpace.prod inferInstance]
      (fun w => (w, LifetimePath.shift (T w).toNNReal w)) :=
    (measurable_id'' hT.measurableSpace_le).prodMk hs
  have hpre : MeasurableSet ((fun w =>
      (w, LifetimePath.shift (T w).toNNReal w)) ⁻¹' event) := hevent.preimage hpair
  rw [Measure.restrict_apply hpre] at h
  have heq : (fun w => (w, LifetimePath.shift (T w).toNNReal w)) ⁻¹' event ∩ A =
      B ∩ {w | T w < w.lifetime ∧
        (w, LifetimePath.shift (T w).toNNReal w) ∈ event} := by
    dsimp only [A]
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, mem_ofPred_eq]
    tauto
  rw [heq] at h
  simpa only [A, μ, κ, Kernel.comap_apply] using! h

/-- Almost-everywhere bounds on future section probabilities imply the stopped-event bound. -/
theorem strong_markov_random_section_le {d : ℕ} {law : Kernel (Vec d) (Path d)}
    (hSM : StrongMarkov law) (x : Vec d) (T : Path d → ENNReal)
    (hT : IsStoppingTime LifetimePath.canonicalFiltration T)
    (event : Set (Path d × Path d))
    (hevent : MeasurableSet[hT.measurableSpace.prod inferInstance] event)
    (R : ENNReal)
    (hbound : ∀ᵐ w ∂law x, T w < w.lifetime →
      law (position (T w).toNNReal w) {v | (w, v) ∈ event} ≤ R)
    (B : Set (Path d)) (hB : MeasurableSet[hT.measurableSpace] B) :
    law x (B ∩ {w | T w < w.lifetime ∧
      (w, LifetimePath.shift (T w).toNNReal w) ∈ event}) ≤
      R * law x (B ∩ {w | T w < w.lifetime}) := by
  rw [strong_markov_random_section_eq hSM x T hT event hevent B hB]
  have hTmeas : Measurable T := by simpa only using! hT.measurable'
  have hA : MeasurableSet (B ∩ {w | T w < w.lifetime}) :=
    (hT.measurableSpace_le _ hB).inter
      (measurableSet_lt hTmeas LifetimePath.measurable_lifetime)
  calc
    _ ≤ ∫⁻ _w in B ∩ {w | T w < w.lifetime}, R ∂law x := by
      apply lintegral_mono_ae
      rw [ae_restrict_iff' hA]
      filter_upwards [hbound] with w hw hmem
      exact hw hmem.2
    _ = R * law x (B ∩ {w | T w < w.lifetime}) := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing
