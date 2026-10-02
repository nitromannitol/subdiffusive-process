import SubdiffusiveProcess.Probability.RetainedResponseTransport
import SubdiffusiveProcess.Probability.ProductLpContraction

/-! Finite Lp contraction under product relabeling, and comparison of conditioning errors
for nested sigma fields. The latter costs a factor of two at arbitrary finite exponents. -/

open MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section9

variable {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B] [mD : MeasurableSpace D]
    {μ : Measure A} {ν : Measure B} {P : Measure D}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure P]

/-- Finite Lp contraction for the first coordinate of an actual product decomposition. -/
theorem condExp_equiv_fst_eLpNorm_le (e : D ≃ᵐ A × B)
    (he : MeasurePreserving e P (μ.prod ν)) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {f : D → ℝ} (hf : Integrable f P) :
    eLpNorm (P[f | (inferInstance : MeasurableSpace A).comap (fun x => (e x).1)]) p P ≤
      eLpNorm f p P := by
  have hfi := (he.symm e).integrable_comp_of_integrable hf
  have hce : P[f | (inferInstance : MeasurableSpace A).comap (fun x => (e x).1)] =ᵐ[P]
      ((μ.prod ν)[f ∘ e.symm | (inferInstance : MeasurableSpace A).comap Prod.fst]) ∘ e := by
    simpa only [MeasurableSpace.comap_comp, Function.comp_def, e.symm_apply_apply] using
      SubdiffusiveProcess.condExp_comp_measurableEquiv e he measurable_fst.comap_le hfi
  rw [eLpNorm_congr_ae hce,
    eLpNorm_comp_measurePreserving integrable_condExp.aestronglyMeasurable he]
  refine (SubdiffusiveProcess.condExp_prod_fst_eLpNorm_le hp hpt hfi).trans_eq ?_
  exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (he.symm e)

/-- A finer product conditioning error is at most twice the coarser conditioning error. -/
theorem condExp_equiv_fst_error_le_twice (e : D ≃ᵐ A × B)
    (he : MeasurePreserving e P (μ.prod ν))
    {m : MeasurableSpace D}
    (hm : m ≤ (inferInstance : MeasurableSpace A).comap (fun x => (e x).1))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : D → ℝ} (hf : Integrable f P) :
    eLpNorm (f - P[f | (inferInstance : MeasurableSpace A).comap (fun x => (e x).1)]) p P ≤
      2 * eLpNorm (f - P[f | m]) p P := by
  letI : MeasurableSpace D := mD
  have hemeas : @Measurable D A mD inferInstance (fun x : D => (e x).1) :=
    measurable_fst.comp e.measurable
  let m2 := (inferInstance : MeasurableSpace A).comap (fun x => (e x).1)
  letI : MeasurableSpace D := mD
  have hm2 : m2 ≤ mD := hemeas.comap_le
  have hm1 : m ≤ mD := hm.trans hm2
  have hs1 : StronglyMeasurable[m] (P[f | m]) := stronglyMeasurable_condExp
  have hi1 : Integrable (P[f | m]) P := integrable_condExp
  have hid : P[P[f | m] | m2] = P[f | m] :=
    condExp_of_stronglyMeasurable (μ := P) hm2 (hs1.mono hm) hi1
  have hsub : P[f - P[f | m] | m2] =ᵐ[P] P[f | m2] - P[f | m] := by
    have h := condExp_sub hf hi1 m2
    rwa [hid] at h
  have hs1' : AEStronglyMeasurable (P[f | m]) P := (hs1.mono hm1).aestronglyMeasurable
  have hs2' : AEStronglyMeasurable (P[f | m2]) P :=
    (stronglyMeasurable_condExp.mono hm2).aestronglyMeasurable
  have hgap : eLpNorm (P[f | m2] - P[f | m]) p P ≤ eLpNorm (f - P[f | m]) p P := by
    rw [← eLpNorm_congr_ae hsub]
    exact condExp_equiv_fst_eLpNorm_le e he hp hpt (hf.sub hi1)
  have hrepr : f - P[f | m2] = (f - P[f | m]) - (P[f | m2] - P[f | m]) := by
    ext x
    simp only [Pi.sub_apply]
    ring
  change eLpNorm (f - P[f | m2]) p P ≤ _
  rw [hrepr]
  calc
    _ ≤ eLpNorm (f - P[f | m]) p P + eLpNorm (P[f | m2] - P[f | m]) p P :=
      eLpNorm_sub_le (hf.aestronglyMeasurable.sub hs1') (hs2'.sub hs1') hp
    _ ≤ eLpNorm (f - P[f | m]) p P + eLpNorm (f - P[f | m]) p P :=
      add_le_add le_rfl hgap
    _ = 2 * eLpNorm (f - P[f | m]) p P := (two_mul _).symm

end SubdiffusiveProcess.Section9
