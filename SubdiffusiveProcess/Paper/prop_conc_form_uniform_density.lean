import SubdiffusiveProcess.Paper.prop_conc_smooth_domain_approximation
import SubdiffusiveProcess.DirichletForm.ThresholdApproximation
import SubdiffusiveProcess.Sobolev.UniformSmoothSources

/-! Uniform density of continuous compactly supported representatives in the actual limit domain.
The exact Dirichlet realization and normal contractions suffice; no strong
locality or energy measure is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff
namespace Paper
noncomputable section

/-- Actual harmonic mesh limits and normal contractions yield uniform core density for every supplied limit form. -/
theorem prop_conc_form_uniform_density
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
          ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
        (N : ℕ → ℕ),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
        (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)),
      (∀ n f, GN n f =
        (responseSolution (killedResponseSpace hP)
          (cutoffPositiveCoefficient M H om (N n) z hr)
          ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) → ∀ E : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      (∀ u, E.toClosedForm.energy u = limitFormEnergy G u) →
      DirichletForm.HasNormalContractions E →
      ∀ phi : SpatialCoordinates d → ℝ, Continuous phi → HasCompactSupport phi →
        tsupport phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ eps : ℝ, 0 < eps →
      ∃ w ∈ E.toClosedForm.domain, ∃ g : SpatialCoordinates d → ℝ,
        Continuous g ∧ HasCompactSupport g ∧
        tsupport g ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        ((w : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g) ∧
        ∀ x, |g x - phi x| < eps := by
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_smooth_domain_approximation d hd I Pin X W Cp Sob
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hP N
  filter_upwards [hs M Rm Sreg It H hIR hdelta z r hr hP N] with om hom
  intro GN G hGN hG E hE hNC phi hphi hcompact hsupp eps heps
  obtain ⟨psi, hpsi, hpsic, hpsis, hpsia⟩ := SmoothSources.exists_uniform_smooth_approximation
    phi hphi hcompact _ hsupp (eps / 4) (by positivity)
  obtain ⟨u, hu, uc, huc, hurep, huapp⟩ := hom GN G hGN hG psi hpsi hpsic hpsis
    (eps / 8) (by positivity)
  have huE : u ∈ E.toClosedForm.domain := (E.toClosedForm.energy_lt_top_iff u).mp (by
    rw [hE u]
    exact hu)
  obtain ⟨w, hw, g, hgc, hgs, hgQ, hrep, happ⟩ :=
    LimitFormCore.compact_approximation_of_continuous_domain z hr E hNC u huE uc huc hurep
      psi hpsic hpsis (eps / 4) (by positivity) (by
        intro x hx
        have heq : eps / 8 = (eps / 4) / 2 := by ring
        exact (huapp x hx).trans_eq heq)
  refine ⟨w, hw, g, hgc, hgs, hgQ, hrep, ?_⟩
  intro x
  have htri := abs_sub_le (g x) (psi x) (phi x)
  have h1 := happ x
  have h2 := hpsia x
  linarith only [htri, h1, h2, heps]

end
end Paper
