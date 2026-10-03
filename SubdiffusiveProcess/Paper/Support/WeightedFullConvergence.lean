module

public import SubdiffusiveProcess.Paper.Support.WeightedSubsequenceClusters
public import SubdiffusiveProcess.Paper.prop_21_full_cluster_convergence

@[expose] public section





open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.AuditRepairs
open Paper

/-- All identified clusters yield the full weighted inverse limit. This
source application takes analytic controls, not any weighted-limit premise. -/
theorem aux_mfd_prop_21_full_weighted_cluster
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (B : aux_limit_form_package_analytic_controls d hd z r hr S b)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (T : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hT : ∀ n f, T n f =
      (responseSolution S (b n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) :
    ∃ F0 : aux_limit_form_package_form_cluster (centeredCube z r hr) S b,
      Tendsto T atTop (𝓝 F0.operator) ∧
      F0.form.domain = E.domain ∧
      limitFormDomain F0.operator = limitFormDomain G ∧
      (∀ u ∈ limitFormDomain G,
        limitFormEnergy F0.operator u = (∫ x, rho x ∂(Gamma.measure u) : ℝ)) := by
  obtain ⟨F0⟩ := aux_limit_form_package_form_cluster_exists hS B
    (fun n => inputs_classical_e6_response_hcontract d z r hr S hS (b n))
  have hId0 := aux_mfd_prop_21_identify_cluster hS A B GN G hGN hConv
    E hE hcore Gamma rho hcont hpos hweight F0
  have hclusters : ∀ tau : ℕ → ℕ, StrictMono tau →
      ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
        ∃ F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
          Tendsto (fun n => T (tau (sigma n))) atTop (𝓝 F) ∧
          (∀ u, limitFormEnergy F u = limitFormEnergy F0.operator u) ∧
          (∀ x y, inner ℝ (F x) y = inner ℝ x (F y)) ∧
          (∀ x, 0 ≤ inner ℝ x (F x)) := by
    intro tau htau
    obtain ⟨F, hFConv, hDom, hEnergy⟩ := aux_mfd_prop_21_extract_identified_subsequence
      hS A B GN G hGN hConv E hE hcore Gamma rho hcont hpos hweight T hT tau htau
    exact ⟨F.sigma, F.sigma_strict, F.operator, hFConv,
      aux_mfd_prop_21_dual_energies_equal (d := d) (Q := centeredCube z r hr) G F.operator F0.operator hDom hId0.2.1
        (fun u => ∫ x, rho x ∂(Gamma.measure u)) hEnergy hId0.2.2,
      F.symmetric, F.positive⟩
  exact ⟨F0, prop_21_full_cluster_convergence (d := d) (Q := centeredCube z r hr) T F0.operator
    F0.symmetric F0.positive hclusters, hId0.1, hId0.2.1, hId0.2.2⟩

end SubdiffusiveProcess.AuditRepairs
