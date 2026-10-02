import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationHeat

/-!
# Normalisation of a finite reference measure

The finite-iteration estimates of `LocalResolventIterationBootstrap` and
`LocalResolventIterationHeat` are stated for a probability measure.  The local
reference measure of Section 8 is the weighted measure restricted to a cube,
whose total mass is a positive finite number.  This file records the transfer
of the sub-Markov hypotheses and of the `L¹`/`L^∞` seminorms under the
normalisation `μ ↦ (μ univ)⁻¹ • μ`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal ProbabilityTheory
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationScaling

variable {α : Type*} [MeasurableSpace α]

/-- Composition with a kernel commutes with scaling the measure. -/
theorem comp_smul (c : ℝ≥0∞) (μ : Measure α) (κ : ProbabilityTheory.Kernel α α) :
    κ ∘ₘ (c • μ) = c • (κ ∘ₘ μ) := by
  refine Measure.ext fun B hB => ?_
  rw [Measure.bind_apply hB (ProbabilityTheory.Kernel.aemeasurable κ), Measure.smul_apply,
    smul_eq_mul, Measure.bind_apply hB (ProbabilityTheory.Kernel.aemeasurable κ),
    lintegral_smul_measure, smul_eq_mul]

/-- Subinvariance is preserved by scaling the reference measure. -/
theorem comp_smul_le (c : ℝ≥0∞) {μ : Measure α} {κ : ProbabilityTheory.Kernel α α}
    (h : κ ∘ₘ μ ≤ μ) : κ ∘ₘ (c • μ) ≤ c • μ := by
  rw [comp_smul]
  refine Measure.le_iff.mpr fun B hB => ?_
  simpa only [Measure.smul_apply, smul_eq_mul] using
    mul_le_mul_right (h B) c

/-- Rectangle symmetry is preserved by scaling the reference measure. -/
theorem rectangle_symmetry_smul (c : ℝ≥0∞) {μ : Measure α}
    {κ : ProbabilityTheory.Kernel α α}
    (h : ∀ C D : Set α, MeasurableSet C → MeasurableSet D →
      (∫⁻ x in C, κ x D ∂μ) = ∫⁻ x in D, κ x C ∂μ)
    (C D : Set α) (hC : MeasurableSet C) (hD : MeasurableSet D) :
    (∫⁻ x in C, κ x D ∂(c • μ)) = ∫⁻ x in D, κ x C ∂(c • μ) := by
  rw [Measure.restrict_smul, Measure.restrict_smul, lintegral_smul_measure,
    lintegral_smul_measure, h C D hC hD]

/-- The normalisation of a finite measure of positive finite mass. -/
def normalize (μ : Measure α) : Measure α := (μ Set.univ)⁻¹ • μ

/-- The normalisation of a measure of positive finite total mass is a probability measure. -/
theorem isProbabilityMeasure_normalize {μ : Measure α} (h0 : μ Set.univ ≠ 0)
    (htop : μ Set.univ ≠ ∞) : IsProbabilityMeasure (normalize μ) := by
  constructor
  rw [normalize, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

/-- Scaling by a nonzero constant does not change the essential supremum seminorm. -/
theorem eLpNorm_top_smul {c : ℝ≥0∞} (hc : c ≠ 0) (μ : Measure α) (f : α → ℝ) :
    eLpNorm f ∞ (c • μ) = eLpNorm f ∞ μ := by
  simp only [eLpNorm_exponent_top]
  exact eLpNormEssSup_smul_measure hc f

/-- Scaling multiplies the `L¹` seminorm by the same constant. -/
theorem eLpNorm_one_smul (c : ℝ≥0∞) (μ : Measure α) (f : α → ℝ) :
    eLpNorm f 1 (c • μ) = c * eLpNorm f 1 μ := by
  rw [eLpNorm_smul_measure_of_ne_top (by simp) f c]
  simp

/-- The `L¹` seminorm for the normalisation. -/
theorem eLpNorm_one_normalize (μ : Measure α) (f : α → ℝ) :
    eLpNorm f 1 (normalize μ) = (μ Set.univ)⁻¹ * eLpNorm f 1 μ :=
  eLpNorm_one_smul _ μ f

/-- The essential supremum seminorm for the normalisation. -/
theorem eLpNorm_top_normalize {μ : Measure α} (htop : μ Set.univ ≠ ∞) (f : α → ℝ) :
    eLpNorm f ∞ (normalize μ) = eLpNorm f ∞ μ :=
  eLpNorm_top_smul (ENNReal.inv_ne_zero.mpr htop) μ f

/-- Membership in `Lᵖ` is unchanged by the normalisation. -/
theorem memLp_normalize_iff {μ : Measure α} (h0 : μ Set.univ ≠ 0) (htop : μ Set.univ ≠ ∞)
    (p : ℝ≥0∞) (f : α → ℝ) : MemLp f p (normalize μ) ↔ MemLp f p μ := by
  have hc : (μ Set.univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr htop
  have hctop : (μ Set.univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr h0
  have hnorm : eLpNorm f p (normalize μ) = (μ Set.univ)⁻¹ ^ (1 / p).toReal * eLpNorm f p μ := by
    rw [normalize, eLpNorm_smul_measure_of_ne_zero hc f p μ, smul_eq_mul]
  have hpow0 : (μ Set.univ)⁻¹ ^ (1 / p).toReal ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hc) hctop).ne'
  have hpowtop : (μ Set.univ)⁻¹ ^ (1 / p).toReal ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hctop).ne
  have hac1 : normalize μ ≪ μ :=
    Measure.absolutelyContinuous_of_le_smul (c := (μ Set.univ)⁻¹) le_rfl
  have hac2 : μ ≪ normalize μ := by
    refine Measure.absolutelyContinuous_of_le_smul (c := μ Set.univ) ?_
    rw [normalize, smul_smul, ENNReal.mul_inv_cancel h0 htop, one_smul]
  constructor
  · intro hf
    refine ⟨hf.1.mono_ac hac2, ?_⟩
    have h := hf.2
    rw [hnorm] at h
    exact ENNReal.lt_top_of_mul_ne_top_right h.ne hpow0
  · intro hf
    refine ⟨hf.1.mono_ac hac1, ?_⟩
    rw [hnorm]
    exact ENNReal.mul_lt_top hpowtop.lt_top hf.2

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationScaling
