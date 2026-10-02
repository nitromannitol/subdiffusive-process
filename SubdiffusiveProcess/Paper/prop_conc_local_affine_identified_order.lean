import SubdiffusiveProcess.Paper.prop_conc_local_affine_order

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped BigOperators

namespace Paper
noncomputable section

theorem aux_thm_prop_domain_eq_of_energy
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (hE : ∀ u, E.energy u = limitFormEnergy G u) :
    (E.domain : Set (DomainL2 Q)) = limitFormDomain G := by
  ext u
  change u ∈ E.domain ↔ limitFormEnergy G u < ⊤
  rw [← hE]
  exact (E.energy_lt_top_iff u).symm


theorem aux_thm_prop_form_eq_toReal_energy
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (u : DomainL2 Q) (hu : u ∈ E.domain) :
    E.form u u = (limitFormEnergy G u).toReal := by
  rw [← hE, E.energy_of_mem hu, EReal.toReal_coe]


/-- The approved R1 identification data for one actual observation cell.
The ambient killed form supplies the domain and continuous trace class;
only Gamma on q is minimized, and the matrix is normalized by |q|. -/
structure aux_prop_conc_LocalAffineIdentification
    {d : ℕ} (Q : Opens (SpatialCoordinates d)) (q : Set (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (A : Matrix (Fin d) (Fin d) ℝ) where
  contained : closure q ⊆ (Q : Set (SpatialCoordinates d))
  form : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))
  energy_eq : ∀ u, form.toClosedForm.energy u = limitFormEnergy G u
  core : ∃ C, DirichletForm.IsCoreOn form.toClosedForm (Q : Set (SpatialCoordinates d)) C
  gamma : DirichletForm.EnergyMeasure form.toClosedForm
  boundary_minimum : ∀ p : Fin d → ℝ,
    IsGLB (aux_thm_prop_boundary_energy_set Q form.toClosedForm gamma q
      (fun x => ∑ i, p i * x i)) ((volume q).toReal * (p ⬝ᵥ A.mulVec p))

/-- Once the actual local identification is supplied, operator-energy order
implies local matrix order. No total padded energy is equated to a response. -/
theorem prop_conc_local_affine_identified_order
    {d : ℕ} (Q : Opens (SpatialCoordinates d)) (q : Set (SpatialCoordinates d))
    (hq : MeasurableSet q) (hvol : 0 < (volume q).toReal)
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q) (AE AF : Matrix (Fin d) (Fin d) ℝ)
    (E : aux_prop_conc_LocalAffineIdentification Q q GE AE)
    (F : aux_prop_conc_LocalAffineIdentification Q q GF AF)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hdom : limitFormDomain GE = limitFormDomain GF)
    (horder : ∀ u ∈ limitFormDomain GE,
      m * (limitFormEnergy GE u).toReal ≤ (limitFormEnergy GF u).toReal ∧
      (limitFormEnergy GF u).toReal ≤ M * (limitFormEnergy GE u).toReal) :
    ∀ p : Fin d → ℝ,
      m * (p ⬝ᵥ AE.mulVec p) ≤ p ⬝ᵥ AF.mulVec p ∧
      p ⬝ᵥ AF.mulVec p ≤ M * (p ⬝ᵥ AE.mulVec p) := by
  have hEd := aux_thm_prop_domain_eq_of_energy E.form.toClosedForm GE E.energy_eq
  have hFd := aux_thm_prop_domain_eq_of_energy F.form.toClosedForm GF F.energy_eq
  have hEF : E.form.domain = F.form.domain := by
    apply SetLike.coe_injective
    exact hEd.trans (hdom.trans hFd.symm)
  apply aux_thm_prop_affine_matrix_order Q E.form F.form hEF E.core F.core
    E.gamma F.gamma m M hm hM ?_ q hq hvol AE AF E.boundary_minimum F.boundary_minimum
  intro u hu
  have huG : u ∈ limitFormDomain GE := hEd ▸ hu
  have huF : u ∈ F.form.domain := hEF ▸ hu
  rw [aux_thm_prop_form_eq_toReal_energy E.form.toClosedForm GE E.energy_eq u hu,
    aux_thm_prop_form_eq_toReal_energy F.form.toClosedForm GF F.energy_eq u huF]
  exact horder u huG

end
end Paper

