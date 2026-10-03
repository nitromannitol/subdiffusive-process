module

public import SubdiffusiveProcess.Paper.prop_conc_masked_form_data
public import SubdiffusiveProcess.Paper.prop_conc_projected_local_minimizers
public import SubdiffusiveProcess.DirichletForm.LocalResponsePair

@[expose] public section

/-! Borel masking supplies the two additional local minimizers in the same affine trace class.
This constructs the deterministic inputs to relative variation and contains no stochastic estimate. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
namespace Paper
noncomputable section

/-- The two weighted forms and their local minimizers for one common Borel potential. -/
structure aux_prop_conc_masked_response_pair_Data
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm) (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (q : Set (SpatialCoordinates d)) (D : Submodule ℝ (DomainL2 Q))
    (P : DirichletForm.LocalResponsePair (V := Fin d → ℝ) E.toClosedForm F.toClosedForm GammaE GammaF q D)
    (g : SpatialCoordinates d → ℝ) (K CE CF : ℝ) where
  Edata : aux_prop_conc_masked_form_data_Data Q E GammaE g K CE
  Fdata : aux_prop_conc_masked_form_data_Data Q F GammaF g K CF
  uEg : (Fin d → ℝ) →ₗ[ℝ] DomainL2 Q
  uFg : (Fin d → ℝ) →ₗ[ℝ] DomainL2 Q
  QEg : QuadraticForm ℝ (Fin d → ℝ)
  QFg : QuadraticForm ℝ (Fin d → ℝ)
  memEg : ∀ p, uEg p ∈ Edata.form.domain
  memFg : ∀ p, uFg p ∈ Fdata.form.domain
  traceEg : ∀ p, uEg p - (P.boundary p : DomainL2 Q) ∈ D
  traceFg : ∀ p, uFg p - (P.boundary p : DomainL2 Q) ∈ D
  minEg : ∀ p, ∀ v ∈ Edata.form.domain, v - (P.boundary p : DomainL2 Q) ∈ D →
    (Edata.Gamma.measure (uEg p) q).toReal ≤ (Edata.Gamma.measure v q).toReal
  minFg : ∀ p, ∀ v ∈ Fdata.form.domain, v - (P.boundary p : DomainL2 Q) ∈ D →
    (Fdata.Gamma.measure (uFg p) q).toReal ≤ (Fdata.Gamma.measure v q).toReal
  responseEg : ∀ p, QEg p = (Edata.Gamma.measure (uEg p) q).toReal
  responseFg : ∀ p, QFg p = (Fdata.Gamma.measure (uFg p) q).toReal

/-- A bounded Borel mask produces both local response families on the original common trace space. -/
theorem prop_conc_masked_response_pair
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm) (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q) (D : Submodule ℝ (DomainL2 Q))
    (P : DirichletForm.LocalResponsePair (V := Fin d → ℝ) E.toClosedForm F.toClosedForm GammaE GammaF q D)
    (hEc : ∃ S, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) S)
    (hFc : ∃ S, DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) S)
    (hEl : DirichletForm.IsStronglyLocal E.toClosedForm) (hFl : DirichletForm.IsStronglyLocal F.toClosedForm)
    (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (horder : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v ∧ F.form v v ≤ M * E.form v v)
    (CE CF : ℝ) (hCE : 0 < CE) (hCF : 0 < CF)
    (hcoE : ∀ v ∈ E.domain, ‖v‖ ^ 2 ≤ CE * E.form v v)
    (hcoF : ∀ v ∈ F.domain, ‖v‖ ^ 2 ≤ CF * F.form v v)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (K : ℝ) (hK : ∀ x, |g x| ≤ K) :
    Nonempty (aux_prop_conc_masked_response_pair_Data Q E F GammaE GammaF q D P g K CE CF) := by
  let DE := Classical.choice (prop_conc_masked_form_data Q E GammaE hEc hEl g hg K hK CE hCE hcoE)
  let DF := Classical.choice (prop_conc_masked_form_data Q F GammaF hFc hFl g hg K hK CF hCF hcoF)
  have hcan : E.toClosedForm.killedCoreClosure q = D :=
    (DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _).eq_of_isKilledDomain P.killed
  have hkillEF := DirichletForm.ClosedForm.killedCoreClosure_eq_of_form_bounds
    E.toClosedForm F.toClosedForm P.domain_eq m M hm hM horder q
  have hcanE : DE.form.toClosedForm.killedCoreClosure q = D := (DE.killed_eq q).trans hcan
  have hcanF : DF.form.toClosedForm.killedCoreClosure q = D :=
    (DF.killed_eq q).trans (hkillEF.symm.trans hcan)
  have hkE : DirichletForm.IsKilledDomain DE.form.toClosedForm q D := by
    rw [← hcanE]
    exact DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _
  have hkF : DirichletForm.IsKilledDomain DF.form.toClosedForm q D := by
    rw [← hcanF]
    exact DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _
  let b := E.domain.subtype.comp P.boundary
  let bE : (Fin d → ℝ) →ₗ[ℝ] DE.form.domain := b.codRestrict DE.form.domain
    (fun p => DE.domain_eq.symm ▸ (P.boundary p).property)
  let bF : (Fin d → ℝ) →ₗ[ℝ] DF.form.domain := b.codRestrict DF.form.domain
    (fun p => DF.domain_eq.symm ▸ (P.domain_eq ▸ (P.boundary p).property))
  obtain ⟨uEg, QEg, hmemE, htraceE, _horthoE, hminE, hresponseE⟩ :=
    prop_conc_projected_local_minimizers DE.form.toClosedForm DE.Gamma q hq D hkE
      (Real.exp K * CE) (mul_pos (Real.exp_pos _) hCE) DE.coercive bE
  obtain ⟨uFg, QFg, hmemF, htraceF, _horthoF, hminF, hresponseF⟩ :=
    prop_conc_projected_local_minimizers DF.form.toClosedForm DF.Gamma q hq D hkF
      (Real.exp K * CF) (mul_pos (Real.exp_pos _) hCF) DF.coercive bF
  exact ⟨⟨DE, DF, uEg, uFg, QEg, QFg, hmemE, hmemF, htraceE, htraceF,
    hminE, hminF, hresponseE, hresponseF⟩⟩

end
end Paper
