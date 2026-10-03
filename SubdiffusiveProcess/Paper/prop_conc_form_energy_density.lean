module

public import SubdiffusiveProcess.Paper.prop_killed_inverse_form_density
public import SubdiffusiveProcess.Sobolev.CountableSmoothSources

@[expose] public section

/-! Smooth-source form density on each actual cube.
The countable source catalogue is constructed from L2 density; no local energy measure is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff
namespace Paper
noncomputable section

/-- The spectral limit domain has form-dense smooth-source responses on every cube. -/
theorem prop_conc_form_energy_density
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hroot : ∃ Rroot : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
      (∀ x y : DomainL2 (centeredCube z r hr),
        inner ℝ (Rroot x) y = inner ℝ x (Rroot y)) ∧
      (∀ x : DomainL2 (centeredCube z r hr), 0 ≤ inner ℝ x (Rroot x)) ∧
      Rroot.comp Rroot = G ∧ limitFormDomain G = Set.range Rroot)
    (EForm : _root_.DirichletForm
        (volume.restrict ((centeredCube z r hr) : Set (SpatialCoordinates d))))
    (hEForm : ∀ w : DomainL2 (centeredCube z r hr),
      EForm.toClosedForm.energy w = limitFormEnergy G w)
    (hHNC : DirichletForm.HasNormalContractions EForm)
 :
    ∀ u ∈ limitFormDomain G, ∀ ε : ℝ, 0 < ε →
      ∃ f : DomainL2 (centeredCube z r hr),
        (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧
          HasCompactSupport fc ∧ tsupport fc ⊆ ((centeredCube z r hr) : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict ((centeredCube z r hr) : Set (SpatialCoordinates d))] fc) ∧
        ‖u - G f‖ ≤ ε ∧ limitFormEnergy G (u - G f) ≤ ((ε : ℝ) : EReal) := by
  obtain ⟨D, hDc, hDd, hDs⟩ := SmoothSources.exists_countable_dense_smooth_submodule z r hr
  exact prop_killed_inverse_form_density G hroot EForm hEForm hHNC D hDc hDd hDs

end
end Paper
