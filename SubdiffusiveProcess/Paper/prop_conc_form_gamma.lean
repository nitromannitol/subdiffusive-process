module

public import SubdiffusiveProcess.Paper.prop_conc_form_regular
public import SubdiffusiveProcess.Paper.prop_conc_form_data
public import SubdiffusiveProcess.Paper.prop_conc_actual_coercivity_cutoffs
public import SubdiffusiveProcess.Paper.inputs_classical_e5_relative_locality
public import SubdiffusiveProcess.Paper.inputs_classical_e5_energy

@[expose] public section

/-! Actual regular strongly local forms and energy measures for supplied inverse limits.
Locality is obtained from the constructed cutoff and coercivity bounds. The
energy-measure existence step is the separately frozen classical FOT theorem;
this module does not identify one-cell boundary minima. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Each supplied actual inverse limit has its exact regular strongly local form and an energy measure. -/
theorem prop_conc_form_gamma
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd) :
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
        (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) ∧
        _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm ∧
        _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal E.toClosedForm ∧
        Nonempty (_root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm) := by
  obtain ⟨deltaR, hdeltaR, hR⟩ := prop_conc_form_regular d hd I Pin X W Cp Sob
  obtain ⟨deltaC, hdeltaC, hC⟩ := prop_conc_actual_coercivity_cutoffs d hd I Pin X W Cp Sob
    ((d : ℝ) - 1 / 2) (3 / 4) (by linarith only []) (by linarith only [])
    (by norm_num) (by norm_num)
  refine ⟨min deltaR deltaC, lt_min hdeltaR hdeltaC, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr hP N
  filter_upwards [hR M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)) z r hr hP N,
    hC M Rm Sreg It H hIR (hdelta.trans (min_le_right _ _)) z r hr
      (killedResponseSpace hP) rfl N] with om hreg hcut
  intro GN G hGN hG
  obtain ⟨E, hE, hNC, C, hcore, hregular⟩ := hreg GN G hGN hG
  obtain ⟨seq, B, hseq, hB, hfrac, hcoer, _hcell, hcuts⟩ := hcut
  obtain ⟨hsym, hlower, hrec⟩ := aux_in_represented_mosco_free d hd M H om z r hr
    (killedResponseSpace hP) G (fun n => N (seq n)) (fun n => GN (seq n))
    (fun n f => hGN (seq n) f) (hG.comp hseq.tendsto_atTop)
  have hlocal := aux_prop_conc_form_data_qlocal d hd z r hr (killedResponseSpace hP) rfl
    (fun n => cutoffPositiveCoefficient M H om (N (seq n)) z hr) G
    hsym hlower hrec (fun _ => B) (fun _ => hB) B (fun _ => le_rfl) hfrac hcoer
    Interp ((d : ℝ) - 1 / 2) (by linarith only []) (by linarith only []) hcuts E.toClosedForm hE
  have hstrong := inputs_classical_e5_relative_locality d (centeredCube z r hr) E ⟨C, hcore⟩ hlocal
  exact ⟨E, hE, hNC, ⟨C, hcore⟩, hregular, hstrong,
    inputs_classical_e5_energy d (centeredCube z r hr) E hregular hstrong⟩

end
end SubdiffusiveProcess.Paper
