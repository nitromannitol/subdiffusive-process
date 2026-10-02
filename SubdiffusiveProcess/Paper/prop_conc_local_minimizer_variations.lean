import SubdiffusiveProcess.Paper.lem_relvar_localized_weighted_minimizer_difference
import SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer

/-! Local minimizers are minimal under all variations in the killed form domain.
The variation need not have a continuous representative. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

/-- Pairing with a killed variation localizes the full form to the observation cell. -/
theorem aux_prop_conc_local_minimizer_variations_cross
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    {mu : Measure X} (E : DirichletForm.ClosedForm mu)
    (Gamma : DirichletForm.EnergyMeasure E) (U : Set X) (hU : IsOpen U)
    (D : Submodule ℝ (Lp ℝ 2 mu)) (hD : DirichletForm.IsKilledDomain E U D)
    (u v : Lp ℝ 2 mu) (hu : u ∈ E.domain) (hv : v ∈ D) :
    Gamma.cross u v U = E.form u v := by
  have hvE := hD.le_domain hv
  have hvzero := aux_lem_relvar_localized_weighted_minimizer_difference_killed_measure_compl
    Gamma U hU D hD hv
  have hc := Gamma.abs_cross_le u hu v hvE Uᶜ hU.measurableSet.compl
  rw [hvzero, ENNReal.toReal_zero, Real.sqrt_zero, mul_zero] at hc
  have hcomp : Gamma.cross u v Uᶜ = 0 := abs_nonpos_iff.mp hc
  have hsplit := VectorMeasure.of_union (v := Gamma.cross u v)
    disjoint_compl_right hU.measurableSet hU.measurableSet.compl
  rw [Set.union_compl_self, Gamma.cross_univ u hu v hvE, hcomp, add_zero] at hsplit
  exact hsplit.symm

/-- An actual local affine minimizer minimizes its cell energy over every killed-domain variation. -/
theorem prop_conc_local_minimizer_variations
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (E : _root_.DirichletForm (volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (p : Fin d → ℝ) (L K t : ℝ)
    (u : DirichletForm.LocalAffineMinimizer z r hr h3r E Gamma p L K t) :
    ∀ v ∈ E.domain,
      v - u.u ∈ E.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d)) →
      (Gamma.measure u.u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (Gamma.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  intro v hv hdiff
  have hw : v - u.u ∈ E.domain := E.domain.sub_mem hv u.mem
  have hzero : Gamma.cross u.u (v - u.u) (centeredCube z r hr : Set (SpatialCoordinates d)) = 0 := by
    rw [aux_prop_conc_local_minimizer_variations_cross E.toClosedForm Gamma _
      (centeredCube z r hr).isOpen _ (DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _)
      u.u (v - u.u) u.mem hdiff]
    exact u.orthogonal _ hdiff
  have hdiag := Gamma.cross_add_self_apply u.mem hw (centeredCube z r hr : Set (SpatialCoordinates d))
  rw [add_sub_cancel, Gamma.cross_self v hv _ (centeredCube z r hr).isOpen.measurableSet,
    Gamma.cross_self u.u u.mem _ (centeredCube z r hr).isOpen.measurableSet,
    Gamma.cross_self (v - u.u) hw _ (centeredCube z r hr).isOpen.measurableSet, hzero] at hdiag
  linarith only [hdiag, (ENNReal.toReal_nonneg : 0 ≤
    (Gamma.measure (v - u.u) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)]

end
end Paper
