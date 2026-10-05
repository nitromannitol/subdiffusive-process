module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.OGammaSummable

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SubdiffusiveProcess

/-- The finite scalar Orlicz bound, with almost-everywhere premises, obtained from the pinned GMC triangle theorem. -/
theorem lintegral_exp_sq_finset_sum_le
    {α ι : Type*} [MeasurableSpace α] [DecidableEq ι]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (S : Finset ι) (X : ι → α → ℝ) (a : ι → ℝ)
    (hS : S.Nonempty)
    (hX : ∀ i ∈ S, MeasureTheory.AEStronglyMeasurable (X i) μ)
    (hX0 : ∀ i ∈ S, ∀ᵐ x ∂μ, 0 ≤ X i x)
    (ha : ∀ i ∈ S, 0 < a i)
    (hb : ∀ i ∈ S, (∫⁻ x, ENNReal.ofReal (Real.exp ((X i x / a i) ^ 2)) ∂μ) ≤ 2) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (((∑ i ∈ S, X i x) / (∑ i ∈ S, a i)) ^ 2)) ∂μ) ≤ 2 := by
  let I := {i // i ∈ S}
  let Y : I → α → ℝ := fun i x => max (X i x) 0
  let A : I → ℝ := fun i => a i
  have hA : ∀ i : I, 0 < A i := fun i => ha i i.property
  have hYm : ∀ i : I, AEMeasurable (Y i) μ := by
    intro i
    exact ((hX i i.property).aemeasurable.max aemeasurable_const)
  have hY0 : ∀ (i : I) (x : α), 0 ≤ Y i x := by
    intro i x
    exact le_max_right _ _
  have hYi : ∀ i : I, Integrable
      (fun x => Real.exp ((Y i x / A i) ^ 2)) μ := by
    intro i
    have hm : AEStronglyMeasurable
        (fun x => Real.exp ((Y i x / A i) ^ 2)) μ :=
      (((((hX i i.property).aemeasurable.max aemeasurable_const).div_const
        (A i)).pow_const 2).exp).aestronglyMeasurable
    have hnonneg : ∀ᵐ x ∂μ, 0 ≤ Real.exp ((Y i x / A i) ^ 2) :=
      Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
    refine ⟨hm, (hasFiniteIntegral_iff_ofReal hnonneg).2 ?_⟩
    have hle : (∫⁻ x, ENNReal.ofReal (Real.exp ((Y i x / A i) ^ 2)) ∂μ) ≤ 2 := by
      calc
        (∫⁻ x, ENNReal.ofReal (Real.exp ((Y i x / A i) ^ 2)) ∂μ)
            = ∫⁻ x, ENNReal.ofReal (Real.exp ((X i x / a i) ^ 2)) ∂μ := by
                apply lintegral_congr_ae
                filter_upwards [hX0 i i.property] with x hx
                simp [Y, A, max_eq_left hx]
        _ ≤ 2 := hb i i.property
    exact hle.trans_lt (by norm_num)
  have hYG : ∀ i : I, SubdiffusiveProcess.OGammaLE μ 2 (A i) (Y i) := by
    intro i
    apply (SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.ogammaLE_two_iff_of_nonneg
      (hA i) (hY0 i)).2
    refine ⟨hYi i, ?_⟩
    have heq := ofReal_integral_eq_lintegral_ofReal (hYi i)
      (Filter.Eventually.of_forall fun x => (Real.exp_pos ((Y i x / A i) ^ 2)).le)
    have hle : ENNReal.ofReal
        (∫ x, Real.exp ((Y i x / A i) ^ 2) ∂μ) ≤ ENNReal.ofReal 2 := by
      rw [heq]
      simpa using (show (∫⁻ x, ENNReal.ofReal (Real.exp ((Y i x / A i) ^ 2)) ∂μ) ≤ 2 from by
        calc
          (∫⁻ x, ENNReal.ofReal (Real.exp ((Y i x / A i) ^ 2)) ∂μ)
              = ∫⁻ x, ENNReal.ofReal (Real.exp ((X i x / a i) ^ 2)) ∂μ := by
                  apply lintegral_congr_ae
                  filter_upwards [hX0 i i.property] with x hx
                  simp [Y, A, max_eq_left hx]
          _ ≤ 2 := hb i i.property)
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 hle
  have hI : (Finset.univ : Finset I).Nonempty := by
    rcases hS with ⟨i, hi⟩
    exact ⟨⟨i, hi⟩, Finset.mem_univ _⟩
  have hsumG :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.ogammaLE_two_finset_sum
      (mu := μ) Y A hA hYm hY0 hYG hI
  have hAsum : (∑ i : I, A i) = ∑ i ∈ S, a i := by
    simpa [A] using! (Finset.sum_attach S a)
  have hYsum : ∀ᵐ x ∂μ, (∑ i : I, Y i x) = ∑ i ∈ S, X i x := by
    filter_upwards [(Finset.eventually_all S).2 hX0] with x hx
    calc
      (∑ i : I, Y i x) = ∑ i : I, X i x := by
        apply Finset.sum_congr rfl
        intro i _
        exact max_eq_left (hx i i.property)
      _ = ∑ i ∈ S, X i x :=
        (Finset.sum_subtype S (fun i => Iff.rfl) (fun i => X i x)).symm
  rw [hAsum] at hsumG
  obtain ⟨hsumInt, hsumBound⟩ :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.ogammaLE_two_iff_of_nonneg
      (Finset.sum_pos ha hS) (fun x => Finset.sum_nonneg fun i _ => hY0 i x)).1 hsumG
  have hbridge := ofReal_integral_eq_lintegral_ofReal hsumInt
    (Filter.Eventually.of_forall fun x =>
      (Real.exp_pos (((∑ i : I, Y i x) / (∑ i ∈ S, a i)) ^ 2)).le)
  calc
    (∫⁻ x, ENNReal.ofReal
        (Real.exp (((∑ i ∈ S, X i x) / (∑ i ∈ S, a i)) ^ 2)) ∂μ)
        = ∫⁻ x, ENNReal.ofReal
            (Real.exp (((∑ i : I, Y i x) / (∑ i ∈ S, a i)) ^ 2)) ∂μ := by
              apply lintegral_congr_ae
              filter_upwards [hYsum] with x hx
              rw [hx]
    _ = ENNReal.ofReal
          (∫ x, Real.exp (((∑ i : I, Y i x) / (∑ i ∈ S, a i)) ^ 2) ∂μ) := hbridge.symm
    _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hsumBound
    _ = 2 := by norm_num


end SubdiffusiveProcess
