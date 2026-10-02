import SubdiffusiveProcess.Paper.Support.WeightedClusterIdentification





open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.AuditRepairs
open Paper

/-- Opaque existence interface for the constructed weighted controls; every
geometric/family parameter is explicit in the underlying application. -/
theorem aux_mfd_prop_21_weighted_controls_nonempty
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x) :
    Nonempty (aux_limit_form_package_analytic_controls d hd z r hr S b) :=
  ⟨@aux_mfd_prop_21_weighted_controls d hd z r hr S a b A rho hcont hpos hweight⟩

/-- Construct both control witnesses behind a proved interface from the
actual unweighted limit-side package. No weighted limit is an input. -/
theorem aux_mfd_prop_21_controls_from_limit_side
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    {G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (L : aux_limit_form_package_limit_side d hd z r hr S G a)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (b : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x) :
    Nonempty (aux_limit_form_package_analytic_controls d hd z r hr S a ×
      aux_limit_form_package_analytic_controls d hd z r hr S b) := by
  obtain ⟨A⟩ : Nonempty (aux_limit_form_package_analytic_controls d hd z r hr S a) :=
    aux_limit_form_package_controls_of_bounds hd z r hr S G a L.bounds
  obtain ⟨B⟩ : Nonempty (aux_limit_form_package_analytic_controls d hd z r hr S b) :=
    @aux_mfd_prop_21_weighted_controls_nonempty d hd z r hr S a b A rho hcont hpos hweight
  exact ⟨⟨A, B⟩⟩

end SubdiffusiveProcess.AuditRepairs
