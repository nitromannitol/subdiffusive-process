module

public import SubdiffusiveProcess.Paper.goodext_controlled_regular
public import SubdiffusiveProcess.Paper.goodext_controlled_energy_measure_convergence
public import SubdiffusiveProcess.Sobolev.GradientEnergyMeasureIntegral

@[expose] public section

/-! Cluster domination for every subsequence of a controlled coefficient bank.
The prescribed closed form and its prescribed energy measure are retained.
-/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- Every bounded-energy L2 limit along any retained subsequence has energy measure dominated by each weak cluster. -/
theorem goodext_controlled_cluster_bank
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (c : ℕ → SpatialCoordinates d → ℝ) (hc : ∀ n, Continuous (c n))
    (hell : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lam ≤ c n x ∧ c n x ≤ Lam)
    (hrep : ∀ n, (a n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c n)
    (t alpha : ℝ) (ha : 0 < alpha)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr c t alpha)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : DirichletForm.ClosedForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcont : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0)
    (Gamma : DirichletForm.EnergyMeasure E) :
    ∀ (rho : ℕ → ℕ), StrictMono rho →
    ∀ (u : DomainL2 (centeredCube z r hr)) (uN : ℕ → S.space) (E0 : ℝ)
      (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
      nu Set.univ < (⊤ : ENNReal) →
      nu (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0 →
      StrictMono sigma →
      Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
      (∀ n, responseForm S (a (rho n)) (uN n) (uN n) ≤ E0) →
      (∀ phi : SpatialCoordinates d → ℝ,
        ContinuousOn phi (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        Tendsto (fun n => ∫ x, phi x ∂gradientEnergyMeasure (a (rho (sigma n)))
          (sobolevGradient (uN (sigma n)).val)) atTop (𝓝 (∫ x, phi x ∂nu))) →
      u ∈ E.domain ∧ ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        Gamma.measure u B ≤ nu B := by
  obtain ⟨F, hFE, hNC, hcore, hregular⟩ := goodext_controlled_regular hd z r hr S hS a A
    c hc hell hrep t alpha ha hcell GN G hGN hConv E hE hcont
  cases hFE
  intro rho hrho u uN E0 nu sigma hnufin hnusupp hsigma hL2 hBound hMeasure
  have hPass := goodext_controlled_energy_measure_convergence hS
    (aux_prop_conc_controlled_forms_controls_reindex A rho)
    (fun n => GN (rho n)) G (fun n f => hGN (rho n) f)
    (hConv.comp hrho.tendsto_atTop) F hE hcore Gamma
  apply hPass.2.1 u uN E0 nu sigma hnufin hnusupp hsigma hL2 hBound
  intro phi hphi
  simpa only [gradientEnergyMeasure] using! hMeasure phi hphi

end Paper
