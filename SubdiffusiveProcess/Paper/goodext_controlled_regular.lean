module

public import SubdiffusiveProcess.Paper.goodext_controlled_form_realization
public import SubdiffusiveProcess.Paper.goodext_controlled_uniform_density
public import SubdiffusiveProcess.Paper.prop_conc_form_energy_density
public import SubdiffusiveProcess.DirichletForm.ResolventContinuousCore
public import SubdiffusiveProcess.Sobolev.ContinuousZeroExtension

@[expose] public section

/-! Regularity of the exact prescribed inverse-limit form for a controlled sequence.
Uniform mesh approximation supplies uniform core density; source continuity
and spectral density supply energy density. Local trace responses are separate.
-/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Controlled finite meshes and continuous source responses give a regular realization of the prescribed candidate form. -/
theorem goodext_controlled_regular
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (c : ℕ → SpatialCoordinates d → ℝ) (hc : ∀ n, Continuous (c n))
    (hell : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lam ≤ c n x ∧ c n x ≤ Lam)
    (hrep : ∀ n, (a n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c n)
    (t alpha : ℝ) (ha : 0 < alpha)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr c t alpha)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcont : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0) :
    ∃ F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      F.toClosedForm = E ∧ _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions F ∧
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E (centeredCube z r hr : Set (SpatialCoordinates d)) C) ∧
      _root_.SubdiffusiveProcess.DirichletForm.IsRegular E := by
  obtain ⟨F, hFE, hNC, hinj, R, hRsym, hRpos, hRR, hRdom⟩ :=
    goodext_controlled_form_realization hd z r hr S hS a A GN G hGN hConv E hE
  have hEF : ∀ u, F.toClosedForm.energy u = limitFormEnergy G u := by
    intro u
    rw [hFE]
    exact hE u
  have hresponse : ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto (fun n => inverseResponse S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL))
        atTop (𝓝 (inner ℝ f (G f))) := by
    intro f
    have hh : Tendsto (fun n => inner ℝ f (GN n f)) atTop (𝓝 (inner ℝ f (G f))) := tendsto_const_nhds.inner
      (((continuous_id.clm_apply continuous_const).tendsto G).comp hConv)
    apply hh.congr
    intro n
    rw [hGN n f, inverseResponse_eq_load]
    rfl
  have hsmooth := aux_goodext_controlled_uniform_density_smooth hd z r hr S hS a c hc hell
    hrep t alpha ha hcell G F.toClosedForm hEF hresponse
  have hglobal : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0 := by
    intro f hf
    obtain ⟨U, hUc, hUr, hUb⟩ := hcont f hf
    exact continuous_zero_extension_of_frontier_zero _ (G f) U hUc hUr hUb
  have hdense := prop_conc_form_energy_density z r hr G ⟨R, hRsym, hRpos, hRR, hRdom⟩ F hEF hNC
  have hcore := LimitFormCore.isCoreOn z r hr F hNC G R hEF hRsym hinj hRR hRdom hdense
    hglobal (goodext_controlled_uniform_density z r hr F hNC hsmooth)
  have hregular := LimitFormCore.isRegular_of_isCoreOn z r hr _ _ hcore
  rw [hFE] at hcore hregular
  exact ⟨F, hFE, hNC, ⟨_, hcore⟩, hregular⟩

end SubdiffusiveProcess.Paper
