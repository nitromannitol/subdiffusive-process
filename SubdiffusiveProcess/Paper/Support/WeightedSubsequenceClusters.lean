import SubdiffusiveProcess.Paper.Support.WeightedClusterIdentification





open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.AuditRepairs
open Paper

/-- Extract and identify an actual weighted cluster from an arbitrary strict
subsequence. Every analytic control is reindexed before extraction. -/
theorem aux_mfd_prop_21_extract_identified_subsequence
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
      (responseSolution S (b n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (tau : ℕ → ℕ) (htau : StrictMono tau) :
    ∃ F : aux_limit_form_package_form_cluster (centeredCube z r hr) S (fun n => b (tau n)),
      Tendsto (fun n => T (tau (F.sigma n))) atTop (𝓝 F.operator) ∧
      limitFormDomain F.operator = limitFormDomain G ∧
      (∀ u ∈ limitFormDomain G,
        limitFormEnergy F.operator u = (∫ x, rho x ∂(Gamma.measure u) : ℝ)) := by
  let At : aux_limit_form_package_analytic_controls d hd z r hr S (fun n => a (tau n)) :=
    aux_limit_form_package_controls_reindex A tau
  let Bt : aux_limit_form_package_analytic_controls d hd z r hr S (fun n => b (tau n)) :=
    aux_limit_form_package_controls_reindex B tau
  obtain ⟨F⟩ := aux_limit_form_package_form_cluster_exists hS Bt
    (fun n => inputs_classical_e6_response_hcontract d z r hr S hS (b (tau n)))
  have hId := aux_mfd_prop_21_identify_cluster hS At Bt
    (fun n => GN (tau n)) G (fun n => hGN (tau n))
    (hConv.comp htau.tendsto_atTop) E hE hcore Gamma rho hcont hpos
    (fun n => hweight (tau n)) F
  have hNative : F.operatorN = fun n => T (tau n) := by
    funext n
    ext f
    rw [F.operatorN_eq, hT]
  refine ⟨F, ?_, hId.2.1, hId.2.2⟩
  simpa only [hNative] using F.operator_tendsto

/-- Identified energies agree everywhere, including outside the common domain,
where both dual energies are top. -/
theorem aux_mfd_prop_21_dual_energies_equal
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G F F0 : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hDomF : limitFormDomain F = limitFormDomain G)
    (hDomF0 : limitFormDomain F0 = limitFormDomain G)
    (I : DomainL2 Q → ℝ)
    (hF : ∀ u ∈ limitFormDomain G, limitFormEnergy F u = (I u : EReal))
    (hF0 : ∀ u ∈ limitFormDomain G, limitFormEnergy F0 u = (I u : EReal)) :
    ∀ u, limitFormEnergy F u = limitFormEnergy F0 u := by
  intro u
  by_cases hu : u ∈ limitFormDomain G
  · exact (hF u hu).trans (hF0 u hu).symm
  · have huF : ¬limitFormEnergy F u < ⊤ := by
      change u ∉ limitFormDomain F
      rwa [hDomF]
    have huF0 : ¬limitFormEnergy F0 u < ⊤ := by
      change u ∉ limitFormDomain F0
      rwa [hDomF0]
    exact (le_antisymm le_top (not_lt.mp huF)).trans
      (le_antisymm le_top (not_lt.mp huF0)).symm

end SubdiffusiveProcess.AuditRepairs
