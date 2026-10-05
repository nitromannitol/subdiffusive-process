module

public import SubdiffusiveProcess.DirichletForm.EnergyMeasure

@[expose] public section

open MeasureTheory Set
noncomputable section
namespace SubdiffusiveProcess.WeightedLimitIdentification

/-- Signed integration ignores a measurable set on all of whose measurable
subsets the signed measure vanishes. The finite Jordan parts are both null. -/
theorem signedIntegralOn_congr_off_null {X : Type*} [MeasurableSpace X]
    (ν : SignedMeasure X) (S : Set X) (hS : MeasurableSet S)
    (h0 : ∀ B, MeasurableSet B → B ⊆ S → ν B = 0) (f g : X → ℝ)
    (hfg : ∀ x ∉ S, f x = g x) (B : Set X) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B f = _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B g := by
  set j := ν.toJordanDecomposition with hj
  have hν : ∀ A, MeasurableSet A → ν A = (j.posPart A).toReal - (j.negPart A).toReal := by
    intro A hA
    conv_lhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition ν]
    rw [JordanDecomposition.toSignedMeasure, sub_apply,
      Measure.toSignedMeasure_apply_measurable hA, Measure.toSignedMeasure_apply_measurable hA]
    rfl
  obtain ⟨T, hT, hpT, hnT⟩ := j.mutuallySingular
  have hpos : j.posPart S = 0 := by
    have h1 : j.posPart (S ∩ T) = 0 := measure_mono_null inter_subset_right hpT
    have h2 : j.posPart (S \ T) = 0 := by
      have hn : j.negPart (S \ T) = 0 := measure_mono_null (fun x hx => hx.2) hnT
      have h := hν (S \ T) (hS.diff hT)
      rw [h0 _ (hS.diff hT) Set.sdiff_subset, hn, ENNReal.toReal_zero, sub_zero] at h
      exact ((ENNReal.toReal_eq_zero_iff _).1 h.symm).resolve_right (measure_ne_top _ _)
    rw [← MeasureTheory.measure_inter_add_sdiff S hT, h1, h2, add_zero]
  have hneg : j.negPart S = 0 := by
    have h1 : j.negPart (S \ T) = 0 := measure_mono_null (fun x hx => hx.2) hnT
    have h2 : j.negPart (S ∩ T) = 0 := by
      have hp : j.posPart (S ∩ T) = 0 := measure_mono_null inter_subset_right hpT
      have h := hν (S ∩ T) (hS.inter hT)
      rw [h0 _ (hS.inter hT) inter_subset_left, hp, ENNReal.toReal_zero, zero_sub,
        zero_eq_neg] at h
      exact ((ENNReal.toReal_eq_zero_iff _).1 h).resolve_right (measure_ne_top _ _)
    rw [← MeasureTheory.measure_inter_add_sdiff S hT, h1, h2, add_zero]
  have hpae : ∀ᵐ x ∂j.posPart, f x = g x := by
    have : ∀ᵐ x ∂j.posPart, x ∉ S := measure_eq_zero_iff_ae_notMem.1 hpos
    filter_upwards [this] with x hx using hfg x hx
  have hnae : ∀ᵐ x ∂j.negPart, f x = g x := by
    have : ∀ᵐ x ∂j.negPart, x ∉ S := measure_eq_zero_iff_ae_notMem.1 hneg
    filter_upwards [this] with x hx using hfg x hx
  simp only [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn]
  rw [integral_congr_ae (ae_restrict_of_ae hpae), integral_congr_ae (ae_restrict_of_ae hnae)]

/-- Integration over a measurable carrier equals integration over the whole
space, for every integrand; no arbitrary extension outside the carrier matters. -/
theorem signedIntegralOn_univ_eq_of_support {X : Type*} [MeasurableSpace X]
    (nu : SignedMeasure X) (Q : Set X) (hQ : MeasurableSet Q)
    (h0 : ∀ B, MeasurableSet B → B ⊆ Qᶜ → nu B = 0) (f : X → ℝ) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn nu Set.univ f =
      _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn nu Q f := by
  classical
  calc
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn nu Set.univ f =
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn nu Set.univ (Q.indicator f) := by
      apply signedIntegralOn_congr_off_null nu Qᶜ hQ.compl h0
      intro x hx
      simp only [mem_compl_iff, not_not] at hx
      exact (indicator_of_mem hx f).symm
    _ = _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn nu Q f := by
      simp only [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn, Measure.restrict_univ,
        integral_indicator hQ]

end SubdiffusiveProcess.WeightedLimitIdentification
