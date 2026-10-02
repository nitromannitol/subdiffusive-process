import SubdiffusiveProcess.Paper.prop_conc_weighted_measure_identification
import SubdiffusiveProcess.DirichletForm.KilledDomainOrder

/-! Bounded Borel masks preserve the common domain, killed traces, and coercivity of the actual form.
The result supplies deterministic variational data and does not claim a stochastic influence estimate. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal
namespace Paper
noncomputable section

/-- The weighted local form together with the identities needed for relative variation. -/
structure aux_prop_conc_masked_form_data_Data
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (K C : ℝ) where
  form : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))
  Gamma : DirichletForm.EnergyMeasure form.toClosedForm
  domain_eq : form.domain = E.domain
  core : ∃ S, DirichletForm.IsCoreOn form.toClosedForm (Q : Set (SpatialCoordinates d)) S
  locality : DirichletForm.IsStronglyLocal form.toClosedForm
  diagonal : ∀ u ∈ E.domain, form.form u u = ∫ x, Real.exp (g x) ∂(GammaE.measure u)
  bounds : ∀ u ∈ E.domain,
    Real.exp (-K) * E.form u u ≤ form.form u u ∧ form.form u u ≤ Real.exp K * E.form u u
  weight : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
    Gamma.measure u A = ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u)
  cross : ∀ u ∈ E.domain, ∀ v ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
    Gamma.cross u v A = DirichletForm.signedIntegralOn (GammaE.cross u v) A (fun x => Real.exp (g x))
  killed_eq : ∀ A : Set (SpatialCoordinates d), form.toClosedForm.killedCoreClosure A = E.toClosedForm.killedCoreClosure A
  coercive : ∀ u ∈ form.domain, ‖u‖ ^ 2 ≤ (Real.exp K * C) * form.form u u

/-- Every bounded measurable mask supplies a weighted form with the same trace spaces and controlled coercivity. -/
theorem prop_conc_masked_form_data
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ S, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) S)
    (hloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (K : ℝ) (hK : ∀ x, |g x| ≤ K)
    (C : ℝ) (hC : 0 < C) (hcoerc : ∀ u ∈ E.domain, ‖u‖ ^ 2 ≤ C * E.form u u) :
    Nonempty (aux_prop_conc_masked_form_data_Data Q E GammaE g K C) := by
  have hreg := aux_prop_conc_core_measure_data_isRegular_of_core Q E.toClosedForm hcore
  have halg : DirichletForm.IsCoreAlgebra E.toClosedForm :=
    ⟨hreg, DirichletForm.mul_mem E, DirichletForm.comp_mem E,
      DirichletForm.mul_comp_mem E, DirichletForm.mul_mem_of_bounded E⟩
  obtain ⟨Eg, Gammag, hdom, hform, _hregg, hcoreg, hlocg, _hcross⟩ :=
    lem_borel_weights_form E GammaE g hg K hK hreg hcore hloc halg
  have hexp : ∀ x, |Real.exp (g x)| ≤ Real.exp K := fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hK x))
  have hdiag : ∀ u ∈ E.domain, Eg.form u u = ∫ x, Real.exp (g x) ∂(GammaE.measure u) := by
    intro u hu
    rw [hform u hu u hu, DirichletForm.aux_signedIntegralOn_cross_self E.toClosedForm
      GammaE u hu (fun x => Real.exp (g x)) ⟨hg.exp, ⟨Real.exp K, hexp⟩⟩, Measure.restrict_univ]
  have hweight : DirichletForm.IsWeightedForm E.toClosedForm Eg.toClosedForm GammaE
      (fun x => Real.exp (g x)) := ⟨hdom, hdiag, hform⟩
  have hbounds : ∀ u ∈ E.domain,
      Real.exp (-K) * E.form u u ≤ Eg.form u u ∧ Eg.form u u ≤ Real.exp K * E.form u u := by
    intro u hu
    letI finiteGamma : IsFiniteMeasure (GammaE.measure u) := ⟨GammaE.measure_univ_lt_top u hu⟩
    apply hweight.form_mem_Icc hu (aux_lem_borel_weights_closed_core_integrable hg.exp hexp)
    · intro x
      exact Real.exp_le_exp.mpr ((abs_le.mp (hK x)).1)
    · intro x
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hK x))
  obtain ⟨hmeasure, hcross⟩ := prop_conc_weighted_measure_identification Q E Eg GammaE Gammag
    hcore hcoreg hloc hdom.symm g hg K hK hdiag
  refine ⟨⟨Eg, Gammag, hdom, hcoreg, hlocg, hdiag, hbounds, hmeasure, hcross, ?_, ?_⟩⟩
  · intro A
    exact (DirichletForm.ClosedForm.killedCoreClosure_eq_of_form_bounds E.toClosedForm
      Eg.toClosedForm hdom.symm (Real.exp (-K)) (Real.exp K) (Real.exp_pos _) (Real.exp_pos _).le hbounds A).symm
  · intro u hu
    have huE : u ∈ E.domain := hdom ▸ hu
    have hle := mul_le_mul_of_nonneg_left (hbounds u huE).1 (Real.exp_pos K).le
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hle
    calc
      ‖u‖ ^ 2 ≤ C * E.form u u := hcoerc u huE
      _ ≤ C * (Real.exp K * Eg.form u u) := mul_le_mul_of_nonneg_left hle hC.le
      _ = (Real.exp K * C) * Eg.form u u := by ring

end
end Paper
