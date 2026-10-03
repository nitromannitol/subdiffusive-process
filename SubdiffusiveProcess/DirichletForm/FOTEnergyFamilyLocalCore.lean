module

public import SubdiffusiveProcess.DirichletForm.FOTCoreMeasure

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

theorem family_core_carrier {E : ClosedForm m} {U : Set X} {u : Lp ℝ 2 m}
    (hu : E.MemCoreOn U u) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ U ∧ ∀ᵐ x ∂m, x ∉ K → u x = 0 := by
  obtain ⟨f, hf, hfc, hfU, hfae⟩ := hu.hasCoreRep
  refine ⟨tsupport f, hfc, hfU, ?_⟩
  filter_upwards [hfae] with x hx hxf
  rw [hx]
  exact image_eq_zero_of_notMem_tsupport hxf

/-- The core defining identity and strong locality annihilate local zeroes. -/
theorem CoreMeasure.zero_on_open {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : CoreMeasure F U) {u : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) {O : Set X} (hO : IsOpen O)
    (hz : ∀ᵐ x ∂m, x ∈ O → u x = 0) : Γ.measure u O = 0 := by
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu⟩
  letI : (Γ.measure u).Regular := Γ.regular u hu
  have hcompact : ∀ K : Set X, K ⊆ U ∩ O → IsCompact K → Γ.measure u K = 0 := by
    intro K hKU hK
    obtain ⟨C, hC⟩ := h.core
    obtain ⟨φ, f, V, hφ, hf, hfc, hfUO, hφae, hf01, hV, hKV, hfV⟩ :=
      hC.exists_cutoff F hK (h.isOpen.inter hO) hKU inter_subset_left
    obtain ⟨uc, huc, hucc, hucU, huae⟩ := hu.hasCoreRep
    obtain ⟨uφ, huφ, huφae⟩ := exists_memCoreOn_mul_comp F U hu.memCore hφ huae hφae
      (Φ := id) contDiff_id
    obtain ⟨u2, hu2, hu2ae⟩ := exists_memCoreOn_mul_comp F U hu.memCore hu huae huae
      (Φ := id) contDiff_id
    have hprod : ⇑uφ =ᵐ[m] fun x => uc x * f x := by
      filter_upwards [huφae] with x hx
      simpa only [id_eq, mul_comm] using hx
    have hsq : ⇑u2 =ᵐ[m] fun x => uc x ^ 2 := by
      filter_upwards [hu2ae] with x hx
      simpa only [id_eq, pow_two] using hx
    have huφzero : uφ = 0 := by
      apply Lp.ext
      filter_upwards [hprod, huae, hz, Lp.coeFn_zero ℝ 2 m] with x hx hy hz' h0
      rw [hx, h0, Pi.zero_apply]
      by_cases hxO : x ∈ O
      · rw [← hy, hz' hxO, zero_mul]
      · have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hxf => hxO (hfUO hxf).2)
        rw [hf0, mul_zero]
    have hφcarrier : ∃ L : Set X, IsCompact L ∧ L ⊆ U ∩ O ∧
        ∀ᵐ x ∂m, x ∉ L → φ x = 0 := by
      refine ⟨tsupport f, hfc, hfUO, ?_⟩
      filter_upwards [hφae] with x hx hxf
      rw [hx]
      exact image_eq_zero_of_notMem_tsupport hxf
    have hu2zero : ∀ᵐ x ∂m, x ∈ O → u2 x = 0 := by
      filter_upwards [hsq, huae, hz] with x hx hy hz' hxO
      rw [hx, ← hy, hz' hxO, zero_pow two_ne_zero]
    have hformzero := h.stronglyLocal u2 hu2.1 φ hφ.1 (family_core_carrier hu2)
      0 O hO hφcarrier hu2zero
    have hint : ∫ x, f x ∂Γ.measure u = 0 := by
      rw [Γ.defining u φ hu hφ uc f huc hf huae hφae uφ u2 huφ.1 hu2.1 hprod hsq,
        huφzero, F.toClosedForm.form_zero_right hu.1, hformzero, mul_zero, sub_zero]
    have hfi : Integrable f (Γ.measure u) := (integrable_const (1 : ℝ)).mono'
      hf.measurable.aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf01 x).1]
        exact (hf01 x).2)
    have hle : (Γ.measure u K).toReal ≤ 0 := by
      rw [← hint]
      calc
        _ = ∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂Γ.measure u := by
          simpa only [measureReal_def] using!
            (integral_indicator_one (μ := Γ.measure u) hK.measurableSet).symm
        _ ≤ _ := by
          apply integral_mono_ae ((integrable_const 1).indicator hK.measurableSet) hfi
          refine Eventually.of_forall fun x => ?_
          by_cases hx : x ∈ K
          · rw [indicator_of_mem hx, hfV x (hKV hx)]
          · rw [indicator_of_notMem hx]
            exact (hf01 x).1
    exact (ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hle ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top _ _)
  have hUO : Γ.measure u (U ∩ O) = 0 := by
    rw [(h.isOpen.inter hO).measure_eq_iSup_isCompact (Γ.measure u)]
    simp only [ENNReal.iSup_eq_zero]
    exact hcompact
  apply le_antisymm _ bot_le
  calc
    Γ.measure u O ≤ Γ.measure u (U ∩ O) + Γ.measure u Uᶜ :=
      (measure_mono (fun x hx => by
        by_cases hxU : x ∈ U
        · exact Or.inl ⟨hxU, hx⟩
        · exact Or.inr hxU)).trans (measure_union_le _ _)
    _ = 0 := by rw [hUO, Γ.carried u hu, zero_add]

end DirichletForm.FOTConstruction
