module

public import SubdiffusiveProcess.Paper.conv_represented_joint_bounds
public import SubdiffusiveProcess.Paper.limit_form_package_side
public import SubdiffusiveProcess.Paper.inputs_classical_e6_response_hcontract
public import SubdiffusiveProcess.Paper.inputs_BD_witness
public import SubdiffusiveProcess.Paper.inputs_BDQ_witness
public import SubdiffusiveProcess.Paper.inputs_EM_witness

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- One coefficient sequence has its regular strongly local form and energy measure. -/
theorem aux_conv_represented_limit_forms_side
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f = (responseSolution S (a n)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hlim : Tendsto GN atTop (𝓝 G))
    (hBounds : in_represented_bounds_seq d hd z r hr S a G) :
    ∃ L : aux_limit_form_package_limit_side d hd z r hr S G a,
      DirichletForm.IsStronglyLocal L.form.toClosedForm := by
  obtain ⟨L⟩ := limit_form_package_side hd z r hr S hS a
    (fun n => inputs_classical_e6_response_hcontract d z r hr S hS (a n))
    G GN hGN hlim hBounds (inputs_BD_witness d) (inputs_BDQ_witness d)
    (inputs_EM_witness d)
  have hlocal := aux_limit_form_package_form_core_locality d hd z r hr S hS G a
    GN hGN hlim hBounds L.form.toClosedForm L.energy_eq
  exact ⟨L, (inputs_BD_witness d z r hr L.form).isStronglyLocal_of_onCore
    (aux_limit_form_package_isRegular_of_core (centeredCube z r hr)
      L.form.toClosedForm L.core)
    (inputs_BDQ_witness d z r hr L.form L.core hlocal)⟩

/-- Both actual candidate inverse limits have regular strongly local forms and energy measures
on every determining cube. No form or locality premise is required. -/
theorem conv_represented_limit_forms (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hjoint : aux_conv_represented_env_interface_joint d model H Ω P field envE envF z r hr
      Sspace GNE GNF GE GF NE NF)
    (hBounds : aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr
      Sspace GE GF NE NF) :
    ∀ᵐ omega ∂P, ∀ i,
      (∃ L : aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i)
        (GE i omega) (fun n => Lane4.cutoffPositiveCoefficient model H (envE n omega)
          (NE n) (z i) (hr i)), DirichletForm.IsStronglyLocal L.form.toClosedForm) ∧
      (∃ L : aux_limit_form_package_limit_side d hd (z i) (r i) (hr i) (Sspace i)
        (GF i omega) (fun n => Lane4.cutoffPositiveCoefficient model H (envF n omega)
          (NF n) (z i) (hr i)), DirichletForm.IsStronglyLocal L.form.toClosedForm) := by
  rcases hjoint with ⟨_, _, _, _, _, _, _, _, hS, hGN, hlim⟩
  filter_upwards [hBounds, hGN, hlim] with omega hB hG hL i
  constructor
  · exact aux_conv_represented_limit_forms_side d hd (z i) (r i) (hr i) (Sspace i)
      (hS i) _ (GE i omega) (fun n => GNE i n omega) (fun n f => (hG i n f).1)
      (hL i).1 (hB i).1
  · exact aux_conv_represented_limit_forms_side d hd (z i) (r i) (hr i) (Sspace i)
      (hS i) _ (GF i omega) (fun n => GNF i n omega) (fun n f => (hG i n f).2)
      (hL i).2 (hB i).2

end Paper
