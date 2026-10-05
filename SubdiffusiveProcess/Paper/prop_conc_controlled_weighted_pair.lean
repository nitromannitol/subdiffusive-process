module

public import SubdiffusiveProcess.Paper.prop_conc_controlled_weighted_lower
public import SubdiffusiveProcess.Paper.inputs_classical_e5_locality
public import SubdiffusiveProcess.Paper.inputs_classical_e5_relative_locality
public import SubdiffusiveProcess.Paper.inputs_classical_e5_energy
public import SubdiffusiveProcess.Paper.inputs_contraction_witness

@[expose] public section

/-! Identify two supplied operator limits whose cutoff coefficients differ by a continuous positive weight.
This deterministic result supplies the weighted form identity; it makes no probabilistic assertion. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- A continuous positive coefficient weight transfers the actual analytic controls. -/
theorem aux_prop_conc_controlled_weighted_pair_controls
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x) :
    Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S b) := by
  obtain ⟨lo, hi, hlo, hhi, hb⟩ :=
    aux_prop_conc_controlled_local_orders_weight_bounds_on z r hr rho hcont hpos
  have hLower : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo * (a n).val x ≤ (b n).val x := by
    intro n
    filter_upwards [hweight n, aux_prop_locality_recovery_coeff_nonneg (a n),
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hax hxQ
    rw [hx]
    exact mul_le_mul_of_nonneg_right (hb x (subset_closure hxQ)).1 hax
  have hUpper : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (b n).val x ≤ hi * (a n).val x := by
    intro n
    filter_upwards [hweight n, aux_prop_locality_recovery_coeff_nonneg (a n),
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hax hxQ
    rw [hx]
    exact mul_le_mul_of_nonneg_right (hb x (subset_closure hxQ)).2 hax
  exact ⟨aux_prop_conc_controlled_forms_analytic_controls_reindex_weight A b id
    lo hi hlo hhi.le hLower hUpper⟩

/-- Two actual controlled limits differing by a continuous weight have the weighted energy and the same domain. -/
theorem prop_conc_controlled_weighted_pair
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a b : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (GN FN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hFN : ∀ n f, FN n f =
      (responseSolution S (b n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConvG : Tendsto GN atTop (𝓝 G)) (hConvF : Tendsto FN atTop (𝓝 F))
    (E EF : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x) :
    E.domain = EF.domain ∧
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EF.toClosedForm
        (centeredCube z r hr : Set (SpatialCoordinates d)) C) ∧
      ∀ u ∈ E.domain, EF.form u u = ∫ x, rho x ∂(Gamma.measure u) := by
  obtain ⟨B⟩ := aux_prop_conc_controlled_weighted_pair_controls A rho hcont hpos hweight
  have hA := prop_conc_controlled_forms hS A GN G hGN hConvG
  have hB := prop_conc_controlled_forms hS B FN F hFN hConvF
  obtain ⟨lo, hi, hlo, hhi, hb⟩ :=
    aux_prop_conc_controlled_local_orders_weight_bounds_on z r hr rho hcont hpos
  obtain ⟨hdom, hfcore⟩ := aux_prop_conc_controlled_local_orders_controlled_weight_core
    hA hB E.toClosedForm EF.toClosedForm hE hF hcore rho hweight lo hi hlo hhi.le
    (fun x hx => hb x (subset_closure hx))
  have hid := aux_prop_conc_controlled_weighted_lower_controlled_weighted_identify
    (fun z r hr F => ⟨inputs_classical_e5_locality d (centeredCube z r hr) F⟩)
    (fun z r hr F hC hL =>
      (inputs_classical_e5_relative_locality d (centeredCube z r hr) F hC hL).onCore)
    (fun z r hr F => ⟨inputs_classical_e5_energy d (centeredCube z r hr) F⟩)
    (inputs_contraction_witness d) hS A B hA hB E EF hE hF hcore Gamma
    rho hcont hpos hweight
  refine ⟨hdom, hfcore, ?_⟩
  intro u hu
  have huG : u ∈ limitFormDomain G :=
    (aux_thm_prop_domain_eq_of_energy E.toClosedForm G hE) ▸ hu
  have huF : u ∈ EF.domain := hdom ▸ hu
  have he := hid u huG
  rw [← hF u, EF.energy_of_mem huF] at he
  exact EReal.coe_injective he

end
end SubdiffusiveProcess.Paper
