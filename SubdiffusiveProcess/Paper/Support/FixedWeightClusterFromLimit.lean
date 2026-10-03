module

public import SubdiffusiveProcess.Paper.Support.WeightedControlsExistence
public import SubdiffusiveProcess.Paper.Support.WeightedFullConvergence

@[expose] public section








open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.AuditRepairs
open Paper

theorem fixed_weight_cluster_of_limit_side
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    {G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (L : aux_limit_form_package_limit_side d hd z r hr S G a)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (b : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (T : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hT : ∀ n f, T n f =
      (responseSolution S (b n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) :
    ∃ F0 : aux_limit_form_package_form_cluster (centeredCube z r hr) S b,
      Tendsto T atTop (𝓝 F0.operator) ∧
      F0.form.domain = L.form.domain ∧
      (∀ u ∈ limitFormDomain G,
        limitFormEnergy F0.operator u = (∫ x, rho x ∂L.gamma.measure u : ℝ)) := by
  obtain ⟨⟨A, B⟩⟩ : Nonempty (aux_limit_form_package_analytic_controls d hd z r hr S a ×
      aux_limit_form_package_analytic_controls d hd z r hr S b) :=
    @aux_mfd_prop_21_controls_from_limit_side d hd z r hr S a G L rho hcont hpos b hweight
  obtain ⟨F0, hconv, hdom, _, hdiag⟩ :=
    @aux_mfd_prop_21_full_weighted_cluster d hd z r hr S hS a b A B
      L.response G L.response_eq L.response_tendsto L.form L.energy_eq L.core L.gamma
      rho hcont hpos hweight T hT
  exact ⟨F0, hconv, hdom, hdiag⟩

end SubdiffusiveProcess.AuditRepairs
