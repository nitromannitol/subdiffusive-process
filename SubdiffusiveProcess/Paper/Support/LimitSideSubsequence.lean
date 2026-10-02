import SubdiffusiveProcess.AuditRepairs.SignedIntegralSupport
import SubdiffusiveProcess.Paper.limit_form_package_side
import SubdiffusiveProcess.Paper.represented_bounds_subseq





open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.AuditRepairs
open Paper

/-- A strict subsequence retains the actual unweighted form, core and energy
measure. The represented bounds are transported by their proved supplier. -/
noncomputable def aux_mfd_prop_21_limit_side_subsequence
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    {G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (L : aux_limit_form_package_limit_side d hd z r hr S G a)
    (sigma : ℕ → ℕ) (hsigma : StrictMono sigma) :
    aux_limit_form_package_limit_side d hd z r hr S G (fun n => a (sigma n)) where
  response := fun n => L.response (sigma n)
  response_eq := fun n => L.response_eq (sigma n)
  response_tendsto := L.response_tendsto.comp hsigma.tendsto_atTop
  bounds := represented_bounds_subseq d hd z r hr S a G L.bounds sigma hsigma.tendsto_atTop
  form := L.form
  energy_eq := L.energy_eq
  core := L.core
  gamma := L.gamma

/-- The limit-side energy measure is supported in the open cube, including
for arbitrary elements of the full form domain. -/
theorem aux_mfd_prop_21_gamma_support
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    {G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (L : aux_limit_form_package_limit_side d hd z r hr S G a)
    {u : DomainL2 (centeredCube z r hr)} (hu : u ∈ L.form.domain) :
    L.gamma.measure u (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0 := by
  obtain ⟨C, hC⟩ := L.core
  exact aux_limit_form_package_energy_measure_support L.gamma
    (centeredCube z r hr).isOpen.measurableSet hC hu

/-- The bilinear Q-integral in the full proposition is exactly the univ
integral consumed by cor_energy_measures. -/
theorem aux_mfd_prop_21_cross_integral_univ
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    {G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (L : aux_limit_form_package_limit_side d hd z r hr S G a)
    {u v : DomainL2 (centeredCube z r hr)} (hu : u ∈ L.form.domain) (hv : v ∈ L.form.domain)
    (rho : SpatialCoordinates d → ℝ) :
    DirichletForm.signedIntegralOn (L.gamma.cross u v) Set.univ rho =
      DirichletForm.signedIntegralOn (L.gamma.cross u v)
        (centeredCube z r hr : Set (SpatialCoordinates d)) rho := by
  apply signedIntegralOn_univ_eq_of_support _ _ (centeredCube z r hr).isOpen.measurableSet
  intro T hT hTQ
  have hZero := measure_mono_null hTQ (aux_mfd_prop_21_gamma_support L hu)
  have hBound := L.gamma.abs_cross_le u hu v hv T hT
  rw [hZero, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at hBound
  exact abs_nonpos_iff.mp hBound

end SubdiffusiveProcess.AuditRepairs
