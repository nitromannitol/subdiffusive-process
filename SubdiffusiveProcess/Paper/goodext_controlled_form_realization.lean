import SubdiffusiveProcess.Paper.prop_conc_controlled_forms
import SubdiffusiveProcess.Paper.inputs_classical_killed_inverse_compact
import SubdiffusiveProcess.Paper.inputs_contraction_witness
import SubdiffusiveProcess.Paper.prop_killed_inverse_dirichlet_form
import SubdiffusiveProcess.DirichletForm.EnergyEquality
import SubdiffusiveProcess.Sobolev.ResponseInjectivity
import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy

/-! Exact Dirichlet realization of a supplied closed candidate form.
Analytic controls and actual inverse convergence provide the spectral and
contraction properties; no local boundary response is asserted here.
-/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- A response space with the killed variation subspace is the canonical killed response space. -/
theorem aux_goodext_controlled_form_realization_space_eq
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (hS : S.space = killedSobolevGraph Q)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) u‖) :
    S = killedResponseSpace hP := by
  cases S with
  | mk space weak closed poincare =>
    dsimp only at hS
    subst space
    rfl

/-- Controlled actual inverse convergence yields a Dirichlet form whose closed form is exactly the given one. -/
theorem goodext_controlled_form_realization
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) :
    ∃ F : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      F.toClosedForm = E ∧ DirichletForm.HasNormalContractions F ∧ Function.Injective G ∧
      ∃ R : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
        (∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) ∧
        (∀ x, 0 ≤ inner ℝ x (R x)) ∧ R.comp R = G ∧ limitFormDomain G = Set.range R := by
  haveI dimensionNonzero : NeZero d := ⟨by omega⟩
  have hm := prop_conc_controlled_forms hS A GN G hGN hConv
  have hpair (f : DomainL2 (centeredCube z r hr)) :
      Tendsto (fun n => inner ℝ f (GN n f)) atTop (𝓝 (inner ℝ f (G f))) :=
    tendsto_const_nhds.inner
      (((continuous_id.clm_apply continuous_const).tendsto G).comp hConv)
  have hinj : Function.Injective G := by
    apply injective_limit_of_volumeResponse_approximations S a G
      (A.sources : Set (DomainL2 (centeredCube z r hr))) A.sources_dense
    · intro f
      apply (hpair f).congr
      intro n
      rw [hGN n f, inverseResponse_eq_load]
      rfl
    · intro f hf eps heps
      exact A.mesh f (A.sources_smooth ⟨f, hf⟩) eps heps
  have hpos : ∀ x, 0 ≤ inner ℝ x (G x) := by
    intro x
    apply ge_of_tendsto' (hpair x)
    intro n
    rw [hGN n x]
    exact volumeResponse_pairing_nonneg S (a n) x
  have hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖ := by
    exact centeredCube_killedPoincare z hr
  have hSpace := aux_goodext_controlled_form_realization_space_eq S hS hP
  have hcompact : IsCompactOperator G := by
    apply isCompactOperator_of_tendsto hConv
    apply Eventually.of_forall
    intro n
    apply inputs_classical_killed_inverse_compact d hd z r hr hP (a n) (GN n)
    intro f
    rw [← hSpace]
    exact hGN n f
  have hroot := prop_killed_inverse_spectral_square_root G hcompact hm.symmetric hpos hinj
  obtain ⟨F0, hF0, hNC⟩ := prop_killed_inverse_dirichlet_form S a G hm.symmetric hpos
    hinj hroot ⟨hm.lower, hm.recovery⟩
    (fun n T hT u => inputs_contraction_witness d z r hr S hS (a n) T hT u)
  have heq : ∀ u, E.energy u = F0.toClosedForm.energy u := fun u => (hE u).trans (hF0 u).symm
  refine ⟨DirichletForm.ClosedForm.dirichletFormOfEnergyEq E F0 heq, rfl, ?_, hinj, hroot⟩
  exact DirichletForm.ClosedForm.hasNormalContractions_dirichletFormOfEnergyEq E F0 heq hNC

end Paper
