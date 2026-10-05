module

public import SubdiffusiveProcess.Paper.prop_conc_orthogonal_boundary_minimum
public import SubdiffusiveProcess.DirichletForm.LocalAffineFamily

@[expose] public section

/-! The coordinate minimizers identify the stated affine response for every slope.
The result uses the observation-cell energy measure and its frozen boundary minimum. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Linear extension of the actual coordinate minimizers realizes every stated affine boundary minimum. -/
theorem prop_conc_linear_family_minimum
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (L : Fin d → ℝ) (K t : ℝ)
    (u : ∀ i : Fin d, _root_.SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer z r hr h3r E Gamma (Pi.single i 1) (L i) K t)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ p : Fin d → ℝ,
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) E.toClosedForm Gamma
        (centeredCube z r hr : Set (SpatialCoordinates d)) (fun x => ∑ i, p i * x i))
        ((volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal * (p ⬝ᵥ A.mulVec p))) :
    ∀ p : Fin d → ℝ,
      (Gamma.measure (_root_.SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer.linearFamily u p)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal * (p ⬝ᵥ A.mulVec p) ∧
      ∀ v ∈ E.domain,
        v - _root_.SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer.linearFamily u p ∈
          E.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d)) →
        (Gamma.measure (_root_.SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer.linearFamily u p)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          (Gamma.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  intro p
  let b := _root_.SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer.linearFamily u p
  have hb := b.property
  have hortho := _root_.SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer.linearFamily_orthogonal u p
  have hleast := prop_conc_orthogonal_boundary_minimum hd z r hr h3r E Gamma hcore b hb
    (_root_.SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer.linearRepresentative u p) (fun x => ∑ i, p i * x i)
    (_root_.SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer.linearRepresentative_continuous u p)
    (_root_.SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer.linearFamily_coeFn u p)
    (_root_.SubdiffusiveProcess.DirichletForm.LocalAffineMinimizer.linearRepresentative_boundary u p) hortho
  refine ⟨hleast.isGLB.unique (hA p), ?_⟩
  intro v hv hdiff
  have hD := _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure E.toClosedForm
    (centeredCube z r hr : Set (SpatialCoordinates d))
  apply Gamma.local_minimum_of_cross_eq_zero _ (centeredCube z r hr).isOpen.measurableSet
    _ hD.le_domain b hb _ v hv hdiff
  intro w hw
  rw [aux_prop_conc_local_minimizer_variations_cross E.toClosedForm Gamma _
    (centeredCube z r hr).isOpen _ hD b w hb hw]
  exact hortho w hw

end
end SubdiffusiveProcess.Paper
