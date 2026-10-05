module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubcubeAveraging

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow

open SubdiffusiveProcess.CoarseGrainingVocab MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ}

/-- **Slab mean split.**  A parent mean is controlled by the `L²` size of the
function on any positive-measure subwindow `S`, plus the parent oscillation
amplified by the volume ratio.  No boundary integral occurs. -/
theorem abs_averageOn_le_slab_add_oscillation
    {P S : Set (Vec d)} {f : Vec d → ℝ}
    (hSmeas : MeasurableSet S) (hsub : S ⊆ P)
    (hPtop : volume P ≠ ⊤) (hPpos : 0 < (volume P).toReal)
    (hSpos : 0 < (volume S).toReal)
    (hf : IntegrableOn f P)
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) P) :
    |averageOn P f| ≤ normalizedL2On S f +
      Real.sqrt ((volume P).toReal / (volume S).toReal) *
        normalizedL2On P (fun x ↦ f x - averageOn P f) := by
  have hfS : IntegrableOn f S := hf.mono_set hsub
  have hf2S : IntegrableOn (fun x ↦ f x ^ 2) S := hf2.mono_set hsub
  have hslab : |averageOn S f| ≤ normalizedL2On S f :=
    abs_volumeAverage_le_normalizedL2On hSmeas hSpos hfS hf2S
  have hcompare := abs_averageOn_subset_sub_averageOn_le
    (Q := P) (P := S) hSmeas hsub hPtop hPpos hSpos hf hf2
  have htriangle : |averageOn P f| ≤ |averageOn S f| +
      |averageOn S f - averageOn P f| := by
    have := abs_sub_abs_le_abs_sub (averageOn S f) (averageOn P f)
    cases abs_cases (averageOn S f - averageOn P f) with
    | inl h => cases abs_cases (averageOn S f) with
      | inl h2 => cases abs_cases (averageOn P f) with
        | inl h3 => linarith [h.1, h2.1, h3.1]
        | inr h3 => linarith [h.1, h2.1, h3.1]
      | inr h2 => cases abs_cases (averageOn P f) with
        | inl h3 => linarith [h.1, h2.1, h3.1]
        | inr h3 => linarith [h.1, h2.1, h3.1]
    | inr h => cases abs_cases (averageOn S f) with
      | inl h2 => cases abs_cases (averageOn P f) with
        | inl h3 => linarith [h.1, h2.1, h3.1]
        | inr h3 => linarith [h.1, h2.1, h3.1]
      | inr h2 => cases abs_cases (averageOn P f) with
        | inl h3 => linarith [h.1, h2.1, h3.1]
        | inr h3 => linarith [h.1, h2.1, h3.1]
  linarith [htriangle, hslab, hcompare]

/-- Squared form, ready for the radius row: the slab contributes the free
small factor and the oscillation carries the budgets. -/
theorem sq_averageOn_le_slab_add_oscillation
    {P S : Set (Vec d)} {f : Vec d → ℝ}
    (hSmeas : MeasurableSet S) (hsub : S ⊆ P)
    (hPtop : volume P ≠ ⊤) (hPpos : 0 < (volume P).toReal)
    (hSpos : 0 < (volume S).toReal)
    (hf : IntegrableOn f P)
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) P) :
    averageOn P f ^ 2 ≤
      2 * normalizedL2On S f ^ 2 +
        2 * ((volume P).toReal / (volume S).toReal) *
          normalizedL2On P (fun x ↦ f x - averageOn P f) ^ 2 := by
  have hmain := abs_averageOn_le_slab_add_oscillation hSmeas hsub hPtop hPpos
    hSpos hf hf2
  set a : ℝ := normalizedL2On S f with hadef
  set r : ℝ := Real.sqrt ((volume P).toReal / (volume S).toReal) with hrdef
  set b : ℝ := normalizedL2On P (fun x ↦ f x - averageOn P f) with hbdef
  have hratio : 0 ≤ (volume P).toReal / (volume S).toReal :=
    div_nonneg hPpos.le hSpos.le
  have hrsq : r ^ 2 = (volume P).toReal / (volume S).toReal := by
    rw [hrdef, Real.sq_sqrt hratio]
  have hsq : averageOn P f ^ 2 ≤ (a + r * b) ^ 2 := by
    have habs : |averageOn P f| ≤ a + r * b := hmain
    nlinarith [sq_abs (averageOn P f), abs_nonneg (averageOn P f), habs]
  have hexpand : (a + r * b) ^ 2 ≤ 2 * a ^ 2 + 2 * (r * b) ^ 2 := by
    nlinarith [sq_nonneg (a - r * b)]
  have hrb : (r * b) ^ 2 = ((volume P).toReal / (volume S).toReal) * b ^ 2 := by
    rw [mul_pow, hrsq]
  linarith [hsq, hexpand, hrb.le, hrb.ge]

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
