module

public import SubdiffusiveProcess.Paper.prop_conc_form_realized
public import SubdiffusiveProcess.Paper.prop_conc_form_energy_density
public import SubdiffusiveProcess.Paper.prop_conc_form_continuous_all_cubes
public import SubdiffusiveProcess.Paper.prop_conc_form_uniform_density
public import SubdiffusiveProcess.DirichletForm.ResolventContinuousCore

@[expose] public section

/-! Regular Dirichlet realizations of every supplied actual cutoff inverse limit.
Both core density clauses are constructed from upstream local data. Strong
locality, the energy measure, and its boundary minima are not asserted here. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Every supplied actual inverse limit has an exact regular Dirichlet form with a core on its cube. -/
theorem prop_conc_form_regular
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
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
      Tendsto GN atTop (𝓝 G) →
      ∃ E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
        (∀ u, E.toClosedForm.energy u = limitFormEnergy G u) ∧
        _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions E ∧
        ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm := by
  obtain ⟨deltaR, hdeltaR, hR⟩ := prop_conc_form_realized d hd I Pin X W Cp Sob
  obtain ⟨deltaC, hdeltaC, hC⟩ := prop_conc_form_continuous_all_cubes d hd I Pin X W Cp Sob
  obtain ⟨deltaU, hdeltaU, hU⟩ := prop_conc_form_uniform_density d hd I Pin X W Cp Sob
  refine ⟨min deltaR (min deltaC deltaU), lt_min hdeltaR (lt_min hdeltaC hdeltaU), ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hP N
  have hdR := hdelta.trans (min_le_left _ _)
  have hdC := (hdelta.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hdU := (hdelta.trans (min_le_right _ _)).trans (min_le_right _ _)
  filter_upwards [hR M Rm Sreg It H hIR hdR z r hr hP N,
    hC M Rm Sreg It H hIR hdC z r hr hP N,
    hU M Rm Sreg It H hIR hdU z r hr hP N] with om hreal hcont hunif
  intro GN G hGN hG
  obtain ⟨E, hE, hNC, hinj, R, hRsym, hRpos, hRR, hRdom⟩ := hreal GN G hGN hG
  have hdense := prop_conc_form_energy_density z r hr G ⟨R, hRsym, hRpos, hRR, hRdom⟩ E hE hNC
  have hcore := LimitFormCore.isCoreOn z r hr E hNC G R hE hRsym hinj hRR hRdom hdense
    (hcont GN G hGN hG) (hunif GN G hGN hG E hE hNC)
  exact ⟨E, hE, hNC, _, hcore, LimitFormCore.isRegular_of_isCoreOn z r hr _ _ hcore⟩

end
end SubdiffusiveProcess.Paper
