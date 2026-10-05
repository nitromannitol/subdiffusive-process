module

public import SubdiffusiveProcess.Paper.conv_represented_limit_forms
public import SubdiffusiveProcess.Paper.limit_form_package_convergence
public import SubdiffusiveProcess.Paper.goodext_controlled_response_recovery

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Represented bounds and actual inverse convergence supply source-energy recovery
for every regular realization of the prescribed limit energy. No energy-measure
convergence premise or choice of a particular form package is needed. -/
theorem limit_form_source_recovery_of_bounds
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f = (responseSolution S (a n)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hlim : Tendsto GN atTop (𝓝 G))
    (hBounds : in_represented_bounds_seq d hd z r hr S a G)
    (Form : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, Form.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn Form.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Form.toClosedForm)
    (f : DomainL2 (centeredCube z r hr)) :
    ∀ chi : SpatialCoordinates d → ℝ, Continuous chi → HasCompactSupport chi →
      Tendsto (fun n => ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        chi x * (a n).val x * ∑ i : Fin d, ((sobolevGradient
          (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val i) x) ^ 2)
        atTop (𝓝 (∫ x, chi x ∂(Gamma.measure (G f)))) := by
  obtain ⟨A⟩ := aux_limit_form_package_controls_of_bounds hd z r hr S G a hBounds
  have hPass := limit_form_package_convergence (inputs_BD_witness d) (inputs_BDQ_witness d)
    (inputs_EM_witness d) (inputs_classical_e6_response_hcontract d) hS A GN G
    hGN hlim Form hE hcore Gamma
  obtain ⟨hsym, hpos⟩ := aux_goodext_controlled_response_recovery_sym_pos S a
    GN G hGN hlim
  have hdom : G f ∈ Form.domain := by
    apply Form.toClosedForm.mem_domain_of_energy_lt_top
    have hval : limitFormEnergy G (G f) = ((inner ℝ f (G f) : ℝ) : EReal) :=
      iSup_quadraticDual_apply_image G hsym hpos f
    rw [hE, hval]
    exact EReal.coe_lt_top _
  have hrec := aux_goodext_controlled_response_recovery_sequence S a GN G
    hGN hlim f
  rw [← hE] at hrec
  intro chi hchi _hsupp
  have h := hPass.1 (G f)
    (fun n => responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL))
    hdom hrec chi hchi.continuousOn
  refine h.congr (fun n => ?_)
  exact gradientEnergyMeasure_integral (a n) (sobolevGradient
    (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val) chi

end SubdiffusiveProcess.Paper
