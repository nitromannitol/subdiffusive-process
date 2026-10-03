module

public import SubdiffusiveProcess.Paper.prop_conc_controlled_weighted_pair
public import SubdiffusiveProcess.Paper.prop_21_full_cluster_convergence
public import SubdiffusiveProcess.DirichletForm.EnergyMeasureCongruence

@[expose] public section

/-! Continuous positive weights preserve full convergence of the controlled inverse sequence.
The proof identifies every cluster by its extended energy, without postulating convergence of a deleted layer. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
namespace Paper
noncomputable section

/-- A weighted cluster has the same domain and the prescribed weighted diagonal energy. -/
theorem aux_prop_conc_controlled_weighted_convergence_cluster
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a b : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConvG : Tendsto GN atTop (𝓝 G))
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
    (C : aux_prop_conc_controlled_forms_form_cluster (centeredCube z r hr) S b) :
    E.domain = C.form.domain ∧
      (∃ D, DirichletForm.IsCoreOn C.form.toClosedForm
        (centeredCube z r hr : Set (SpatialCoordinates d)) D) ∧
      ∀ u ∈ E.domain, C.form.form u u = ∫ x, rho x ∂(Gamma.measure u) := by
  exact prop_conc_controlled_weighted_pair hd z r hr S hS
    (fun n => a (C.sigma n)) (fun n => b (C.sigma n))
    (aux_prop_conc_controlled_forms_controls_reindex A C.sigma)
    (fun n => GN (C.sigma n)) (fun n => C.operatorN (C.sigma n)) G C.operator
    (fun n => hGN (C.sigma n)) (fun n => C.operatorN_eq (C.sigma n))
    (hConvG.comp C.sigma_strict.tendsto_atTop) C.operator_tendsto E C.form hE C.energy_eq
    hcore Gamma rho hcont hpos (fun n => hweight (C.sigma n))

/-- Every continuous positive coefficient weight has a fully convergent actual inverse sequence. -/
theorem prop_conc_controlled_weighted_convergence
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a b : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConvG : Tendsto GN atTop (𝓝 G))
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
      fun x => rho x * (a n).val x) :
    ∃ (FN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
      (F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
      (EF : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∀ n f, FN n f =
        (responseSolution S (b n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) ∧
      Tendsto FN atTop (𝓝 F) ∧
      (∀ x y, inner ℝ (F x) y = inner ℝ x (F y)) ∧
      (∀ x, 0 ≤ inner ℝ x (F x)) ∧
      (∀ u, EF.energy u = limitFormEnergy F u) ∧
      E.domain = EF.domain ∧
      (∃ D, DirichletForm.IsCoreOn EF.toClosedForm
        (centeredCube z r hr : Set (SpatialCoordinates d)) D) ∧
      ∀ u ∈ E.domain, EF.form u u = ∫ x, rho x ∂(Gamma.measure u) := by
  obtain ⟨B⟩ := aux_prop_conc_controlled_weighted_pair_controls A rho hcont hpos hweight
  obtain ⟨C⟩ := aux_prop_conc_controlled_forms_form_cluster_exists hS B
    (fun n => inputs_contraction_witness d z r hr S hS (b n))
  have hC := aux_prop_conc_controlled_weighted_convergence_cluster hd z r hr S hS
    a b A GN G hGN hConvG E hE hcore Gamma rho hcont hpos hweight C
  refine ⟨C.operatorN, C.operator, C.form, C.operatorN_eq, ?_, C.symmetric,
    C.positive, C.energy_eq, hC.1, hC.2.1, hC.2.2⟩
  apply prop_21_full_cluster_convergence C.operatorN C.operator C.symmetric C.positive
  intro tau htau
  let Bt := aux_prop_conc_controlled_forms_controls_reindex B tau
  obtain ⟨D⟩ := aux_prop_conc_controlled_forms_form_cluster_exists hS Bt
    (fun n => inputs_contraction_witness d z r hr S hS (b (tau n)))
  have hD := aux_prop_conc_controlled_weighted_convergence_cluster hd z r hr S hS
    (fun n => a (tau n)) (fun n => b (tau n))
    (aux_prop_conc_controlled_forms_controls_reindex A tau)
    (fun n => GN (tau n)) G (fun n => hGN (tau n))
    (hConvG.comp htau.tendsto_atTop) E hE hcore Gamma rho hcont hpos
    (fun n => hweight (tau n)) D
  refine ⟨D.sigma, D.sigma_strict, D.operator, ?_, ?_, D.symmetric, D.positive⟩
  · have heq : (fun n => C.operatorN (tau (D.sigma n))) =
        (fun n => D.operatorN (D.sigma n)) := by
      funext n
      apply ContinuousLinearMap.ext
      intro f
      rw [C.operatorN_eq, D.operatorN_eq]
    rw [heq]
    exact D.operator_tendsto
  · intro u
    rw [← D.energy_eq, ← C.energy_eq]
    exact DirichletForm.ClosedForm.energy_eq_of_common_diagonal E.toClosedForm
      D.form.toClosedForm C.form.toClosedForm (fun v => ∫ x, rho x ∂(Gamma.measure v))
      hD.1 hC.1 hD.2.2 hC.2.2 u

end
end Paper
