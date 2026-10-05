module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Conditional expectations on three independent blocks

The probability-space identity in source `lem:band` (Lemma 31, before B1).
The carriers are genuine product probability spaces; every projection is
Mathlib's conditional expectation onto the indicated coordinate sigma-field.
Equalities are almost everywhere, so no conditional version is evaluated at
an exceptional conditioning value. The coordinate formula follows from
Fubini and the set-integral characterization of conditional expectation.

This file also proves B1 for exponents one and two. `ProductLpContraction`
extends the norm estimate to every finite p ≥ 1, and `LayerProductBlocks`
regroups the integer-indexed environment. Quantitative resampling estimates
and passage through completion remain separate dependencies.
-/

open MeasureTheory
open scoped MeasureTheory

namespace SubdiffusiveProcess

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Conditioning on the first coordinate integrates out the second coordinate. -/
theorem condExp_prod_fst_integral {f : A × B → ℝ} (hf : Integrable f (μ.prod ν)) :
    (μ.prod ν)[f | (inferInstance : MeasurableSpace A).comap Prod.fst] =ᵐ[μ.prod ν]
      fun p => ∫ b, f (p.1, b) ∂ν := by
  have hm : (inferInstance : MeasurableSpace A).comap (Prod.fst : A × B → A) ≤
      (inferInstance : MeasurableSpace (A × B)) :=
    (measurable_fst : Measurable (Prod.fst : A × B → A)).comap_le
  let h : A → ℝ := fun a => ∫ b, f (a, b) ∂ν
  have hh : Integrable h μ := hf.integral_prod_left
  have hg : Integrable (fun p : A × B => h p.1) (μ.prod ν) := hh.comp_fst ν
  have hgm : AEStronglyMeasurable[(inferInstance : MeasurableSpace A).comap Prod.fst]
      (fun p : A × B => h p.1) (μ.prod ν) := by
    refine ⟨fun p => hh.aestronglyMeasurable.mk h p.1, ?_, ?_⟩
    · exact hh.aestronglyMeasurable.stronglyMeasurable_mk.comp_measurable
        (comap_measurable Prod.fst)
    · exact Measure.quasiMeasurePreserving_fst.ae_eq_comp hh.aestronglyMeasurable.ae_eq_mk
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hf
  · intro s hs hfin
    exact hg.integrableOn
  · intro s hs hfin
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hset : Prod.fst ⁻¹' t = t ×ˢ (Set.univ : Set B) := by ext p; simp
    rw [hset, setIntegral_prod _ hg.integrableOn, setIntegral_prod _ hf.integrableOn]
    simp [h]
  · exact hgm

/-- Conditional expectation is compatible with a measure-preserving relabeling. -/
theorem condExp_comp_measurableEquiv {X Y : Type*}
    {m : MeasurableSpace Y} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    {ξ : Measure X} {ζ : Measure Y} [IsFiniteMeasure ξ] [IsFiniteMeasure ζ]
    (e : X ≃ᵐ Y) (he : MeasurePreserving e ξ ζ)
    (hm : m ≤ mY)
    {f : Y → ℝ} (hf : Integrable f ζ) :
    ξ[f ∘ e | m.comap e] =ᵐ[ξ] (ζ[f | m]) ∘ e := by
  have hle : m.comap e ≤ mX := (MeasurableSpace.comap_mono hm).trans e.measurable.comap_le
  have hfc : Integrable (f ∘ e) ξ := he.integrable_comp_of_integrable hf
  have hgc : Integrable ((ζ[f | m]) ∘ e) ξ :=
    he.integrable_comp_of_integrable integrable_condExp
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle hfc
  · intro s hs hfin
    exact hgc.integrableOn
  · intro s hs hfin
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have het := he.restrict_preimage (hm t ht)
    change (∫ x in e ⁻¹' t, (ζ[f | m]) (e x) ∂ξ) =
      ∫ x in e ⁻¹' t, f (e x) ∂ξ
    rw [het.integral_comp' _, het.integral_comp' _]
    exact setIntegral_condExp hm hf ht
  · exact (stronglyMeasurable_condExp.comp_measurable
      (comap_measurable e)).aestronglyMeasurable

/-- Integrate the discarded coordinate after a measure-preserving product decomposition. -/
theorem condExp_equiv_fst_integral {X : Type*} [MeasurableSpace X]
    {ξ : Measure X} [IsProbabilityMeasure ξ]
    (e : X ≃ᵐ A × B) (he : MeasurePreserving e ξ (μ.prod ν))
    {f : X → ℝ} (hf : Integrable f ξ) :
    ξ[f | (inferInstance : MeasurableSpace A).comap (fun x => (e x).1)] =ᵐ[ξ]
      fun x => ∫ b, f (e.symm ((e x).1, b)) ∂ν := by
  have hfi : Integrable (f ∘ e.symm) (μ.prod ν) :=
    (he.symm e).integrable_comp_of_integrable hf
  have hce := condExp_comp_measurableEquiv e he
    (measurable_fst : Measurable (Prod.fst : A × B → A)).comap_le hfi
  have hav := he.quasiMeasurePreserving.ae_eq_comp (condExp_prod_fst_integral hfi)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e.symm_apply_apply] using
    hce.trans hav

variable {C : Type*} [MeasurableSpace C] {τ : Measure C} [IsProbabilityMeasure τ]

/-- Put the middle block first, retaining the two discarded blocks as a product. -/
def middleBlockEquiv : (A × B) × C ≃ᵐ B × (A × C) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A)
    (MeasurableEquiv.refl C)).trans MeasurableEquiv.prodAssoc

/-- Regrouping independent probability coordinates preserves their product law. -/
theorem measurePreserving_middleBlockEquiv :
    MeasurePreserving (middleBlockEquiv : (A × B) × C ≃ᵐ B × (A × C))
      ((μ.prod ν).prod τ) (ν.prod (μ.prod τ)) := by
  exact (measurePreserving_prodAssoc ν μ τ).comp
    (Measure.measurePreserving_swap.prod (MeasurePreserving.id τ))

/-- Keep the middle and right blocks and average out the left block. -/
theorem condExp_prod_middle_right {f : (A × B) × C → ℝ}
    (hf : Integrable f ((μ.prod ν).prod τ)) :
    ((μ.prod ν).prod τ)[f |
      (inferInstance : MeasurableSpace (B × C)).comap (fun p => (p.1.2, p.2))]
      =ᵐ[(μ.prod ν).prod τ] fun p => ∫ a, f ((a, p.1.2), p.2) ∂μ := by
  let e : (A × B) × C ≃ᵐ (B × C) × A :=
    MeasurableEquiv.prodAssoc.trans (MeasurableEquiv.prodComm : A × (B × C) ≃ᵐ (B × C) × A)
  have he : MeasurePreserving e ((μ.prod ν).prod τ) ((ν.prod τ).prod μ) :=
    Measure.measurePreserving_swap.comp (measurePreserving_prodAssoc μ ν τ)
  exact condExp_equiv_fst_integral e he hf

/-- Keep only the middle block and average over the product of the others. -/
theorem condExp_prod_middle {f : (A × B) × C → ℝ}
    (hf : Integrable f ((μ.prod ν).prod τ)) :
    ((μ.prod ν).prod τ)[f |
      (inferInstance : MeasurableSpace B).comap (fun p => p.1.2)]
      =ᵐ[(μ.prod ν).prod τ] fun p => ∫ ac, f ((ac.1, p.1.2), ac.2) ∂μ.prod τ := by
  exact condExp_equiv_fst_integral middleBlockEquiv measurePreserving_middleBlockEquiv hf

/-- The sigma-field generated by the left and middle coordinates. -/
@[instance_reducible]
def leftMiddleSigma : MeasurableSpace ((A × B) × C) :=
  (inferInstance : MeasurableSpace (A × B)).comap Prod.fst

/-- The sigma-field generated by the middle and right coordinates. -/
@[instance_reducible]
def middleRightSigma : MeasurableSpace ((A × B) × C) :=
  (inferInstance : MeasurableSpace (B × C)).comap (fun p => (p.1.2, p.2))

/-- The sigma-field generated by the retained middle coordinate. -/
@[instance_reducible]
def middleSigma : MeasurableSpace ((A × B) × C) :=
  (inferInstance : MeasurableSpace B).comap (fun p => p.1.2)

/-- Fubini applies on almost every middle-coordinate fiber. -/
theorem integrable_middle_fiber_ae {f : (A × B) × C → ℝ}
    (hf : Integrable f ((μ.prod ν).prod τ)) :
    ∀ᵐ p ∂(μ.prod ν).prod τ,
      Integrable (fun ac : A × C => f ((ac.1, p.1.2), ac.2)) (μ.prod τ) := by
  have hi : Integrable (f ∘ middleBlockEquiv.symm) (ν.prod (μ.prod τ)) :=
    (measurePreserving_middleBlockEquiv.symm middleBlockEquiv).integrable_comp_of_integrable hf
  have hp : MeasurePreserving (fun p : (A × B) × C => p.1.2)
      ((μ.prod ν).prod τ) ν := measurePreserving_snd.comp measurePreserving_fst
  exact hp.quasiMeasurePreserving.ae hi.prod_right_ae

/-- Removing the left and right blocks, in that order, retains exactly the middle block. -/
theorem condExp_leftMiddle_condExp_middleRight {f : (A × B) × C → ℝ}
    (hf : Integrable f ((μ.prod ν).prod τ)) :
    ((μ.prod ν).prod τ)[((μ.prod ν).prod τ)[f | middleRightSigma] | leftMiddleSigma]
      =ᵐ[(μ.prod ν).prod τ] ((μ.prod ν).prod τ)[f | middleSigma] := by
  let g : (A × B) × C → ℝ := fun p => ∫ a, f ((a, p.1.2), p.2) ∂μ
  have hcg : ((μ.prod ν).prod τ)[f | middleRightSigma] =ᵐ[(μ.prod ν).prod τ] g :=
    condExp_prod_middle_right hf
  have hg : Integrable g ((μ.prod ν).prod τ) := integrable_condExp.congr hcg
  refine (condExp_congr_ae hcg).trans ((condExp_prod_fst_integral hg).trans ?_)
  refine Filter.EventuallyEq.trans ?_ (condExp_prod_middle hf).symm
  filter_upwards [integrable_middle_fiber_ae hf] with p hp
  exact (integral_prod_symm _ hp).symm

/-- Removing the right and left blocks, in that order, retains exactly the middle block. -/
theorem condExp_middleRight_condExp_leftMiddle {f : (A × B) × C → ℝ}
    (hf : Integrable f ((μ.prod ν).prod τ)) :
    ((μ.prod ν).prod τ)[((μ.prod ν).prod τ)[f | leftMiddleSigma] | middleRightSigma]
      =ᵐ[(μ.prod ν).prod τ] ((μ.prod ν).prod τ)[f | middleSigma] := by
  let g : (A × B) × C → ℝ := fun p => ∫ c, f (p.1, c) ∂τ
  have hcg : ((μ.prod ν).prod τ)[f | leftMiddleSigma] =ᵐ[(μ.prod ν).prod τ] g :=
    condExp_prod_fst_integral hf
  have hg : Integrable g ((μ.prod ν).prod τ) := integrable_condExp.congr hcg
  refine (condExp_congr_ae hcg).trans ((condExp_prod_middle_right hg).trans ?_)
  refine Filter.EventuallyEq.trans ?_ (condExp_prod_middle hf).symm
  filter_upwards [integrable_middle_fiber_ae hf] with p hp
  exact (integral_prod _ hp).symm

/-- The band-error decomposition for the actual conditional expectations. -/
theorem product_condExp_error_decomposition {f : (A × B) × C → ℝ}
    (hf : Integrable f ((μ.prod ν).prod τ)) :
    (f - ((μ.prod ν).prod τ)[f | middleSigma]) =ᵐ[(μ.prod ν).prod τ]
      (f - ((μ.prod ν).prod τ)[f | leftMiddleSigma]) +
        ((μ.prod ν).prod τ)[f - ((μ.prod ν).prod τ)[f | middleRightSigma] |
          leftMiddleSigma] := by
  filter_upwards [condExp_leftMiddle_condExp_middleRight hf,
    condExp_sub hf (integrable_condExp (m := middleRightSigma)) leftMiddleSigma]
    with p hcomm hsub
  simp only [Pi.sub_apply, Pi.add_apply] at hsub ⊢
  rw [hsub, hcomm]
  exact (sub_add_sub_cancel (f p) _ _).symm

/-- The L¹ version of the finite-band error inequality (B1). -/
theorem product_condExp_error_eLpNorm_one_le {f : (A × B) × C → ℝ}
    (hf : Integrable f ((μ.prod ν).prod τ)) :
    eLpNorm (f - ((μ.prod ν).prod τ)[f | middleSigma]) 1 ((μ.prod ν).prod τ) ≤
      eLpNorm (f - ((μ.prod ν).prod τ)[f | leftMiddleSigma]) 1 ((μ.prod ν).prod τ) +
      eLpNorm (f - ((μ.prod ν).prod τ)[f | middleRightSigma]) 1 ((μ.prod ν).prod τ) := by
  rw [eLpNorm_congr_ae (product_condExp_error_decomposition hf)]
  refine (eLpNorm_add_le le_rfl).trans ?_
  exact add_le_add le_rfl
    (eLpNorm_condExp_le_eLpNorm (μ := (μ.prod ν).prod τ) (m := leftMiddleSigma)
      (f - ((μ.prod ν).prod τ)[f | middleRightSigma]) le_rfl)

/-- The L² version of (B1), with no abstract-projection hypotheses. -/
theorem product_condExp_error_eLpNorm_two_le {f : (A × B) × C → ℝ}
    (hf : MemLp f 2 ((μ.prod ν).prod τ)) :
    eLpNorm (f - ((μ.prod ν).prod τ)[f | middleSigma]) 2 ((μ.prod ν).prod τ) ≤
      eLpNorm (f - ((μ.prod ν).prod τ)[f | leftMiddleSigma]) 2 ((μ.prod ν).prod τ) +
      eLpNorm (f - ((μ.prod ν).prod τ)[f | middleRightSigma]) 2 ((μ.prod ν).prod τ) := by
  have hfi : Integrable f ((μ.prod ν).prod τ) := hf.integrable (by norm_num)
  rw [eLpNorm_congr_ae (product_condExp_error_decomposition hfi)]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  exact add_le_add le_rfl
    (eLpNorm_condExp_le_eLpNorm (μ := (μ.prod ν).prod τ) (m := leftMiddleSigma)
      (f - ((μ.prod ν).prod τ)[f | middleRightSigma]) (by norm_num))

end SubdiffusiveProcess
