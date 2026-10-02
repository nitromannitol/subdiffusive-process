import SubdiffusiveProcess.Assumptions.OGammaBridge
import SubdiffusiveProcess.CoarseGrainingVocab.OGammaToolkit

/-! One-sided expectation/tail bridges and two-sided tail control. -/
open MeasureTheory Homogenization.IndependentSums
noncomputable section
namespace SubdiffusiveProcess.Probability.Orlicz
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma isBigOWith_gammaSigma_of_ogammaLE {s A : ℝ} (hs : 0 < s) (hA : 0 < A)
    {X : Ω → ℝ} (hX : SubdiffusiveProcess.OGammaLE μ s A X) :
    IsBigOWith μ (gammaSigma s) X ((1 + Real.log 2) ^ s⁻¹ * A) := by
  have hp : SubdiffusiveProcess.OGammaLE μ s A (fun ω => max (X ω) 0) := by
    simpa only [SubdiffusiveProcess.OGammaLE, max_assoc, max_self] using hX
  have h := SubdiffusiveProcess.OGammaBridge.isBigO_gammaSigma_of_ogammaLE hs hA
    (fun ω => le_max_right (X ω) 0) hp
  exact h.of_le fun ω => (le_max_left (X ω) 0).trans (le_abs_self _)

lemma ogammaLE_of_isBigOWith_gammaSigma {s A : ℝ} (hs : 0 < s) (hA : 0 < A)
    {X : Ω → ℝ} (hm : Measurable X) (hX : IsBigOWith μ (gammaSigma s) X A) :
    SubdiffusiveProcess.OGammaLE μ s ((4 : ℝ) ^ s⁻¹ * A) X := by
  have hpos : IsBigO μ (gammaSigma s) (fun ω => max (X ω) 0) A := by
    intro t ht
    apply (measureReal_mono (s₂ := {ω | A * t < X ω}) ?_ (measure_ne_top μ _)).trans (hX ht)
    intro ω hω
    change A * t < |max (X ω) 0| at hω
    rw [abs_of_nonneg (le_max_right _ _)] at hω
    rcases lt_max_iff.mp hω with h | h
    · exact h
    · exact False.elim (not_lt_of_ge (mul_nonneg hA.le (by linarith)) h)
  have h := SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma hs hA
    (hm.max measurable_const) hpos
  exact SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_of_ae_le
    (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hA) hs.le hm.aemeasurable
    (Filter.Eventually.of_forall fun ω => le_max_left (X ω) 0) h

omit [IsProbabilityMeasure μ] in
lemma isBigO_gammaSigma_of_two_sided {s A : ℝ} (hs : 1 ≤ s) (hA : 0 < A)
    {X : Ω → ℝ} (hm : AEMeasurable X μ) (hp : SubdiffusiveProcess.OGammaLE μ s A X)
    (hn : SubdiffusiveProcess.OGammaLE μ s A (fun ω => -X ω)) :
    IsBigO μ (gammaSigma s) X ((1 + Real.log 2) ^ s⁻¹ * (2 * A)) := by
  have hpos : SubdiffusiveProcess.OGammaLE μ s A (fun ω => max (X ω) 0) := by
    simpa only [SubdiffusiveProcess.OGammaLE, max_assoc, max_self] using hp
  have hneg : SubdiffusiveProcess.OGammaLE μ s A (fun ω => max (-X ω) 0) := by
    simpa only [SubdiffusiveProcess.OGammaLE, max_assoc, max_self] using hn
  have habs : ∀ x : ℝ, max x 0 + max (-x) 0 = |x| := by
    intro x
    rcases le_total 0 x with h | h
    · simp only [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h, add_zero]
    · simp only [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h, zero_add]
  have ho := SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_add hA hA hs
    (hm.max aemeasurable_const) (hm.neg.max aemeasurable_const) hpos hneg
  have ha : SubdiffusiveProcess.OGammaLE μ s (2 * A) (fun ω => |X ω|) := by
    simpa only [habs, two_mul] using ho
  have h := SubdiffusiveProcess.OGammaBridge.isBigO_gammaSigma_of_ogammaLE
    (lt_of_lt_of_le zero_lt_one hs) (mul_pos (by norm_num) hA) (fun ω => abs_nonneg (X ω)) ha
  simpa only [IsBigO, abs_abs] using h

end SubdiffusiveProcess.Probability.Orlicz
