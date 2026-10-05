module

public import SubdiffusiveProcess.WeightedLimitIdentification.EqualBaseEnergyMeasures
public import SubdiffusiveProcess.Paper.limit_form_package_side
public import SubdiffusiveProcess.Paper.prop_conc_core_measure_data

@[expose] public section








open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.WeightedLimitIdentification
open _root_.SubdiffusiveProcess.Paper

structure RegularBaseData {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) where
  form : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))
  gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure form.toClosedForm
  energy_eq : ∀ u : DomainL2 Q, form.energy u = limitFormEnergy G u
  regular : _root_.SubdiffusiveProcess.DirichletForm.IsRegular form.toClosedForm
  locality : _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal form.toClosedForm
  algebra : _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra form.toClosedForm
  core : ∃ C : Set (DomainL2 Q), _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn form.toClosedForm (Q : Set _) C
  support : ∀ u ∈ form.domain, gamma.measure u (Q : Set _)ᶜ = 0

theorem regular_base_data_of_limit_side
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (L : aux_limit_form_package_limit_side d hd z r hr S G a)
    (hloc : _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal L.form.toClosedForm) :
    Nonempty (RegularBaseData (centeredCube z r hr) G) := by
  refine ⟨⟨L.form, L.gamma, L.energy_eq,
    aux_limit_form_package_isRegular_of_core _ L.form.toClosedForm L.core,
    hloc, prop_conc_core_measure_data _ L.form L.core, L.core, ?_⟩⟩
  obtain ⟨C, hC⟩ := L.core
  exact fun u hu => aux_limit_form_package_energy_measure_support L.gamma
    (centeredCube z r hr).isOpen.measurableSet hC hu

/-- Transport changes only the inverse in the dual identification; the actual form
and all regularity/locality/Gamma data are retained. -/
def RegularBaseData.ofQuadraticEq
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {G F : DomainL2 Q →L[ℝ] DomainL2 Q}
    (D : RegularBaseData Q G)
    (hquad : ∀ f : DomainL2 Q, inner ℝ f (G f) = inner ℝ f (F f)) :
    RegularBaseData Q F where
  form := D.form
  gamma := D.gamma
  energy_eq := fun u => (D.energy_eq u).trans (dual_energy_eq_of_quadratic_eq G F hquad u)
  regular := D.regular
  locality := D.locality
  algebra := D.algebra
  core := D.core
  support := D.support

end SubdiffusiveProcess.WeightedLimitIdentification
