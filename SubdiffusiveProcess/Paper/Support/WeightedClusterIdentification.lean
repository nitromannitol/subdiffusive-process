module

public import SubdiffusiveProcess.Paper.limit_form_package_weighted
public import SubdiffusiveProcess.Paper.inputs_BD_witness
public import SubdiffusiveProcess.Paper.inputs_BDQ_witness
public import SubdiffusiveProcess.Paper.inputs_EM_witness
public import SubdiffusiveProcess.Paper.inputs_classical_e6_response_hcontract

@[expose] public section





open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.AuditRepairs
open Paper

/-- Source application helper: identify an extracted weighted cluster using
the proved local recovery, energy-measure comparison and partition argument.
The domain and diagonal identification are conclusions, not cluster fields. -/
theorem aux_mfd_prop_21_identify_cluster
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
    (F : aux_limit_form_package_form_cluster (centeredCube z r hr) S b) :
    F.form.domain = E.domain ∧
      limitFormDomain F.operator = limitFormDomain G ∧
      (∀ u ∈ limitFormDomain G,
        limitFormEnergy F.operator u = (∫ x, rho x ∂(Gamma.measure u) : ℝ)) := by
  let A' := aux_limit_form_package_controls_reindex A F.sigma
  let B' := aux_limit_form_package_controls_reindex B F.sigma
  have hA' := limit_form_package_controls hS A' (fun n => GN (F.sigma n)) G
    (fun n => hGN (F.sigma n)) (hConv.comp F.sigma_strict.tendsto_atTop)
  have hB' : aux_limit_form_package_mosco_data (centeredCube z r hr) S
      (fun n => b (F.sigma n)) F.operator := ⟨F.symmetric, F.lower, F.recovery⟩
  obtain ⟨lo, hi, hlo, hhi, hb⟩ :=
    aux_limit_form_package_weight_bounds_on z r hr rho hcont hpos
  have hdom := aux_limit_form_package_controlled_weight_core hA' hB'
    E.toClosedForm F.form.toClosedForm hE F.energy_eq hcore rho
    (fun n => hweight (F.sigma n)) lo hi hlo hhi.le
    (fun x hx => hb x (subset_closure hx))
  refine ⟨hdom.1.symm, ?_, ?_⟩
  · rw [← aux_limit_form_package_domain_eq_of_energy F.form.toClosedForm F.operator F.energy_eq,
      ← aux_limit_form_package_domain_eq_of_energy E.toClosedForm G hE, hdom.1]
  · exact aux_limit_form_package_controlled_weighted_identify
      (inputs_BD_witness d) (inputs_BDQ_witness d) (inputs_EM_witness d)
      (inputs_classical_e6_response_hcontract d) hS A' B' hA' hB'
      E F.form hE F.energy_eq hcore Gamma rho hcont hpos
      (fun n => hweight (F.sigma n))

/-- The finite weighted coefficients preserve every analytic control by the
literal positive lower and upper weight bounds on the closed cube. -/
noncomputable def aux_mfd_prop_21_weighted_controls
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x) :
    aux_limit_form_package_analytic_controls d hd z r hr S b := by
  apply Classical.choice
  obtain ⟨lo, hi, hlo, hhi, hb⟩ :=
    aux_limit_form_package_weight_bounds_on z r hr rho hcont hpos
  refine ⟨aux_limit_form_package_analytic_controls_reindex_weight A b id lo hi hlo hhi.le ?_ ?_⟩
  · intro n
    filter_upwards [hweight n, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet,
      aux_prop_locality_recovery_coeff_nonneg (a n)] with x hx hxQ hax
    rw [hx]
    exact mul_le_mul_of_nonneg_right (hb x (subset_closure hxQ)).1 hax
  · intro n
    filter_upwards [hweight n, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet,
      aux_prop_locality_recovery_coeff_nonneg (a n)] with x hx hxQ hax
    rw [hx]
    exact mul_le_mul_of_nonneg_right (hb x (subset_closure hxQ)).2 hax

end SubdiffusiveProcess.AuditRepairs
