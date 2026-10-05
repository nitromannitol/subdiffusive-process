module

public import SubdiffusiveProcess.DirichletForm.FOTCoreMeasureSupport

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal CompactlySupported BoundedContinuousFunction

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
variable {m : Measure X} {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}

omit [LocallyCompactSpace X] in
/-- Regularity is preserved by finite sums of finite regular measures. -/
theorem regular_add {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [_t2 : T2Space X] [_lc : LocallyCompactSpace X] [_borel : BorelSpace X]
    (μ ν : Measure X) [μ.Regular] [ν.Regular]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : (μ + ν).Regular := by
  have hir : Measure.InnerRegularWRT (μ + ν) IsCompact IsOpen := by
    intro O hO r hr
    let D := {K : Set X // K ⊆ O ∧ IsCompact K}
    have : Nonempty D := ⟨⟨∅, empty_subset O, isCompact_empty⟩⟩
    have hsup (ρ : Measure X) [ρ.Regular] : ρ O = ⨆ K : D, ρ K.1 := by
      apply le_antisymm
      · rw [hO.measure_eq_iSup_isCompact ρ]
        exact iSup_le fun K => iSup_le fun hKO => iSup_le fun hK =>
          le_iSup_of_le (⟨K, hKO, hK⟩ : D) le_rfl
      · exact iSup_le fun K => measure_mono K.property.1
    rw [Measure.add_apply, hsup μ, hsup ν, ENNReal.iSup_add] at hr
    simp_rw [ENNReal.add_iSup] at hr
    obtain ⟨K, hr⟩ := lt_iSup_iff.mp hr
    obtain ⟨L, hr⟩ := lt_iSup_iff.mp hr
    refine ⟨K.1 ∪ L.1, union_subset K.property.1 L.property.1,
      K.property.2.union L.property.2, ?_⟩
    rw [Measure.add_apply]
    exact hr.trans_le (add_le_add (measure_mono subset_union_left)
      (measure_mono subset_union_right))
  have : (μ + ν).WeaklyRegular :=
    (hir.mono (fun _ h => h) (fun _ h => h.isClosed)).weaklyRegular_of_finite (μ + ν)
  exact ⟨hir⟩

omit [T2Space X] [LocallyCompactSpace X] in
/-- Uniform core density determines integrals of all continuous tests supported in the open set. -/
theorem integral_eq_of_core_tests {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [_t2 : T2Space X] [_lc : LocallyCompactSpace X] [_borel : BorelSpace X] {m : Measure X}
    {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}
    (h : Data F U) (μ ν : Measure X)
    [μ.Regular] [ν.Regular] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (he : ∀ f : tests F U, (∫ x, f.1 x ∂μ) = ∫ x, f.1 x ∂ν)
    (f : C_c(X, ℝ)) (hfU : tsupport f ⊆ U) :
    (∫ x, f x ∂μ) = ∫ x, f x ∂ν := by
  have hb (ε : ℝ) (hε : 0 < ε) :
      |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ ε * ((μ univ).toReal + (ν univ).toReal) := by
    obtain ⟨C, hcore⟩ := h.core
    obtain ⟨w, hw, g, hg, hgc, hgU, hwae, hgf⟩ :=
      hcore.denseUniform f f.continuous f.hasCompactSupport hfU ε hε
    let gc : C_c(X, ℝ) := ⟨⟨g, hg⟩, hgc⟩
    let gt : tests F U := ⟨bounded gc, hgc, hgU, w, (hcore.memCoreOn w hw).1, hwae⟩
    have hm : |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ ε * (μ univ).toReal := by
      change |(∫ x, f x ∂μ) - ∫ x, gc x ∂μ| ≤ _
      rw [← integral_sub (f.integrable (μ := μ)) (gc.integrable (μ := μ))]
      rw [← Real.norm_eq_abs]
      change ‖∫ x, _ ∂_‖ ≤ ε * Measure.real _ univ
      apply norm_integral_le_of_norm_le_const
      exact Eventually.of_forall fun x => by
        change |f x - g x| ≤ ε
        rw [abs_sub_comm]
        exact (hgf x).le
    have hn : |(∫ x, g x ∂ν) - ∫ x, f x ∂ν| ≤ ε * (ν univ).toReal := by
      change |(∫ x, gc x ∂ν) - ∫ x, f x ∂ν| ≤ _
      rw [← integral_sub (gc.integrable (μ := ν)) (f.integrable (μ := ν))]
      rw [← Real.norm_eq_abs]
      change ‖∫ x, _ ∂_‖ ≤ ε * Measure.real _ univ
      apply norm_integral_le_of_norm_le_const
      exact Eventually.of_forall fun x => (hgf x).le
    have hegt : (∫ x, g x ∂μ) = ∫ x, g x ∂ν := he gt
    calc
      |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| =
          |((∫ x, f x ∂μ) - ∫ x, g x ∂μ) + ((∫ x, g x ∂ν) - ∫ x, f x ∂ν)| := by
            rw [hegt]; congr 1; ring
      _ ≤ |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| + |(∫ x, g x ∂ν) - ∫ x, f x ∂ν| := abs_add_le _ _
      _ ≤ ε * (μ univ).toReal + ε * (ν univ).toReal := add_le_add hm hn
      _ = ε * ((μ univ).toReal + (ν univ).toReal) := by ring
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let A := (μ univ).toReal + (ν univ).toReal
  have hA : 0 ≤ A := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  let δ := ε / (A + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : δ * (A + 1) = ε := div_mul_cancel₀ ε (by positivity)
  have hsmall : δ * A ≤ ε := by nlinarith
  simpa only [zero_add] using (hb δ hδ).trans hsmall

/-- Relative continuous tests compare measures carried by the same open set. -/
theorem measure_le_of_relative_integrals (hU : IsOpen U) (μ ν : Measure X)
    [μ.Regular] [ν.Regular] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ Uᶜ = 0)
    (he : ∀ f : C_c(X, ℝ), tsupport f ⊆ U → (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν)
    {O : Set X} (hO : IsOpen O) : μ O ≤ ν O := by
  rw [← measure_inter_conull hμ, (hO.inter hU).measure_eq_iSup_isCompact μ]
  refine iSup_le fun K => iSup_le fun hKO => iSup_le fun hK => ?_
  obtain ⟨f, hf1, hfc, hfs, h01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK (hO.inter hU) hKO
  let fc : C_c(X, ℝ) := ⟨f, hfc⟩
  have hlow : (μ K).toReal ≤ ∫ x, fc x ∂μ := by
    change μ.real K ≤ _
    rw [← integral_indicator_one (μ := μ) hK.measurableSet]
    apply integral_mono
    · exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
    · exact fc.integrable
    · intro x
      change K.indicator (fun _ => (1 : ℝ)) x ≤ f x
      by_cases hx : x ∈ K
      · simp [hx, hf1 hx]
      · simp [hx, (h01 x).1]
  have hhigh : (∫ x, fc x ∂ν) ≤ (ν O).toReal := by
    change _ ≤ ν.real O
    rw [← integral_indicator_one (μ := ν) hO.measurableSet]
    apply integral_mono fc.integrable
    · exact IntegrableOn.integrable_indicator integrableOn_const hO.measurableSet
    · intro x
      change f x ≤ O.indicator (fun _ => (1 : ℝ)) x
      by_cases hx : x ∈ tsupport fc
      · simp [(hfs hx).1, (h01 x).2]
      · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hz]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  apply (ENNReal.toReal_le_toReal (measure_ne_top μ K) (measure_ne_top ν O)).mp
  exact hlow.trans ((he fc (hfs.trans inter_subset_right)).trans hhigh)

theorem measure_eq_of_core_tests (h : Data F U) (μ ν : Measure X)
    [μ.Regular] [ν.Regular] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ Uᶜ = 0) (hν : ν Uᶜ = 0)
    (he : ∀ f : tests F U, (∫ x, f.1 x ∂μ) = ∫ x, f.1 x ∂ν) : μ = ν := by
  apply Measure.OuterRegular.ext_isOpen
  intro O hO
  apply le_antisymm
  · exact measure_le_of_relative_integrals h.isOpen μ ν hμ
      (fun f hf => (integral_eq_of_core_tests h μ ν he f hf).le) hO
  · exact measure_le_of_relative_integrals h.isOpen ν μ hν
      (fun f hf => (integral_eq_of_core_tests h μ ν he f hf).ge) hO

end SubdiffusiveProcess.DirichletForm.FOTConstruction.CoreRiesz
