import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.OGammaSummable

open MeasureTheory Set
open scoped ENNReal
noncomputable section

namespace SubdiffusiveProcess

/-- The countable scalar Orlicz bound, with one common measurable full-measure representative, obtained from the pinned GMC theorem. -/
theorem lintegral_exp_sq_tsum_le
    {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (X : ℕ → α → ℝ) (a : ℕ → ℝ)
    (hX : ∀ n, MeasureTheory.AEStronglyMeasurable (X n) μ)
    (hX0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ X n x)
    (ha : ∀ n, 0 < a n) (hsuma : Summable a)
    (hsumX : ∀ᵐ x ∂μ, Summable (fun n => X n x))
    (hb : ∀ n, (∫⁻ x, ENNReal.ofReal (Real.exp ((X n x / a n) ^ 2)) ∂μ) ≤ 2) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (((∑' n : ℕ, X n x) / (∑' n : ℕ, a n)) ^ 2)) ∂μ) ≤ 2 := by
  classical
  let Xm : ℕ → α → ℝ := fun n => (hX n).mk (X n)
  have hgood : ∀ᵐ x ∂μ,
      (∀ n, X n x = Xm n x) ∧ (∀ n, 0 ≤ X n x) ∧ Summable (fun n => X n x) := by
    filter_upwards [ae_all_iff.2 (fun n => (hX n).ae_eq_mk),
      ae_all_iff.2 hX0, hsumX] with x heq hnonneg hsum
    exact ⟨heq, hnonneg, hsum⟩
  let bad : Set α := {x | ¬ ((∀ n, X n x = Xm n x) ∧
    (∀ n, 0 ≤ X n x) ∧ Summable (fun n => X n x))}
  have hbad : μ bad = 0 := by
    rw [← ae_iff]
    exact hgood
  obtain ⟨nullSet, hbadsub, hnullmeas, hnull⟩ := exists_measurable_superset_of_null hbad
  let Y : ℕ → α → ℝ := fun n x => if x ∈ nullSet then 0 else Xm n x
  have hYmeas : ∀ n, Measurable (Y n) := by
    intro n
    exact Measurable.piecewise hnullmeas measurable_const (hX n).measurable_mk
  have hY0 : ∀ n x, 0 ≤ Y n x := by
    intro n x
    by_cases hx : x ∈ nullSet
    · simp [Y, hx]
    · simp only [Y, if_neg hx]
      have hxgood : (∀ n, X n x = Xm n x) ∧ (∀ n, 0 ≤ X n x) ∧
          Summable (fun n => X n x) := by
        by_contra h
        exact hx (hbadsub h)
      rw [← hxgood.1 n]
      exact hxgood.2.1 n
  have hYsum : ∀ x, Summable (fun n => Y n x) := by
    intro x
    by_cases hx : x ∈ nullSet
    · simpa [Y, hx] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    · have hxgood : (∀ n, X n x = Xm n x) ∧ (∀ n, 0 ≤ X n x) ∧
          Summable (fun n => X n x) := by
        by_contra h
        exact hx (hbadsub h)
      have heq : (fun n => Y n x) = fun n => X n x := by
        funext n
        simp only [Y, if_neg hx]
        exact (hxgood.1 n).symm
      rw [heq]
      exact hxgood.2.2
  have hnotnull : ∀ᵐ x ∂μ, x ∉ nullSet := by
    rw [ae_iff]
    simpa only [compl_setOf, not_not] using hnull
  have hYX : ∀ n, Y n =ᵐ[μ] X n := by
    intro n
    filter_upwards [hnotnull, hgood] with x hxnull hx
    simp only [Y, if_neg hxnull]
    exact (hx.1 n).symm
  have hYb : ∀ n, (∫⁻ x, ENNReal.ofReal (Real.exp ((Y n x / a n) ^ 2)) ∂μ) ≤ 2 := by
    intro n
    refine (lintegral_congr_ae ?_).trans_le (hb n)
    filter_upwards [hYX n] with x hx
    rw [hx]
  have hYgamma : ∀ n, SubdiffusiveProcess.OGammaLE μ 2 (a n) (Y n) := by
    intro n
    apply (SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.ogammaLE_two_iff_of_nonneg
      (ha n) (hY0 n)).2
    have hmeas : Measurable fun x => Real.exp ((Y n x / a n) ^ 2) :=
      (((hYmeas n).div_const _).pow_const 2).exp
    refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
    · rw [hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
      exact lt_of_le_of_lt (hYb n) (by norm_num)
    · have hi : Integrable (fun x => Real.exp ((Y n x / a n) ^ 2)) μ := by
        refine ⟨hmeas.aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_ofReal
          (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
        exact lt_of_le_of_lt (hYb n) (by norm_num)
      have hrw := ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
      have h2 : ENNReal.ofReal (∫ x, Real.exp ((Y n x / a n) ^ 2) ∂μ) ≤ ENNReal.ofReal 2 := by
        rw [hrw]
        simpa using hYb n
      exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h2
  have hYG := SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.ogammaLE_two_tsum
    Y a ha hsuma hYmeas hY0 hYgamma hYsum
  obtain ⟨hYGintegrable, hYGint⟩ :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.ogammaLE_two_iff_of_nonneg
      (hsuma.tsum_pos (fun n => (ha n).le) 0 (ha 0))
      (fun x => tsum_nonneg fun n => hY0 n x)).1 hYG
  have hYlin : (∫⁻ x, ENNReal.ofReal (Real.exp
      (((∑' n, Y n x) / (∑' n, a n)) ^ 2)) ∂μ) ≤ 2 := by
    have hrw := ofReal_integral_eq_lintegral_ofReal hYGintegrable
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    rw [← hrw]
    simpa using ENNReal.ofReal_le_ofReal hYGint
  refine (lintegral_congr_ae ?_).trans_le hYlin
  filter_upwards [hnotnull, hgood] with x hxnull hx
  have htsum : (∑' n, X n x) = ∑' n, Y n x := by
    apply tsum_congr
    intro n
    simp only [Y, if_neg hxnull]
    exact hx.1 n
  rw [htsum]

end SubdiffusiveProcess
