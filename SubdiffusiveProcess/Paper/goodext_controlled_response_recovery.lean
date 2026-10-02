import SubdiffusiveProcess.Paper.goodext_controlled_regular
import SubdiffusiveProcess.Paper.goodext_controlled_energy_measure_convergence
import SubdiffusiveProcess.Sobolev.GradientEnergyMeasureIntegral

/-! The energy measures of the actual finite response solutions converge weakly to the
limiting energy measure of `G f`, for every energy measure of the limiting closed form.
Only the controlled finite-cutoff sequence is used; no local estimate is assumed. -/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal ContDiff

noncomputable section
namespace Paper

/-- The limiting response operator of a convergent sequence of finite response operators is
symmetric and nonnegative. -/
theorem aux_goodext_controlled_response_recovery_sym_pos
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q) (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hlim : Tendsto GN atTop (𝓝 G)) :
    (∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x)) := by
  have happ : ∀ x : DomainL2 Q, Tendsto (fun n => GN n x) atTop (𝓝 (G x)) :=
    fun x => ((continuous_id.clm_apply continuous_const).tendsto G).comp hlim
  constructor
  · intro x y
    have h1 : Tendsto (fun n => inner ℝ (GN n x) y) atTop
        (𝓝 (inner ℝ (G x) y)) := (happ x).inner tendsto_const_nhds
    have h2 : Tendsto (fun n => inner ℝ x (GN n y)) atTop
        (𝓝 (inner ℝ x (G y))) := tendsto_const_nhds.inner (happ y)
    have heq : ∀ n, inner ℝ (GN n x) y = inner ℝ x (GN n y) := by
      intro n
      rw [hGN, hGN, real_inner_comm]
      exact volumeResponse_pairing_symm S (a n) y x
    exact tendsto_nhds_unique (h1.congr heq) h2
  · intro x
    have h1 : Tendsto (fun n => inner ℝ x (GN n x)) atTop
        (𝓝 (inner ℝ x (G x))) := tendsto_const_nhds.inner (happ x)
    refine ge_of_tendsto' h1 (fun n => ?_)
    rw [hGN]
    exact volumeResponse_pairing_nonneg S (a n) x

/-- The finite response solutions of a fixed load form a recovery sequence for `G f`. -/
theorem aux_goodext_controlled_response_recovery_sequence
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q) (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hlim : Tendsto GN atTop (𝓝 G)) (f : DomainL2 Q) :
    Tendsto (fun n =>
      ((responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1,
        ((responseForm S (a n)
          (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL))
          (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)) : ℝ) : EReal)))
      atTop (𝓝 (G f, limitFormEnergy G (G f))) := by
  obtain ⟨hsym, hpos⟩ := aux_goodext_controlled_response_recovery_sym_pos S a GN G hGN hlim
  have happ : Tendsto (fun n => GN n f) atTop (𝓝 (G f)) :=
    ((continuous_id.clm_apply continuous_const).tendsto G).comp hlim
  have hval : limitFormEnergy G (G f) = ((inner ℝ f (G f) : ℝ) : EReal) :=
    iSup_quadraticDual_apply_image G hsym hpos f
  have hform : ∀ n, responseForm S (a n)
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL))
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)) =
        inner ℝ f (GN n f) := by
    intro n
    rw [responseSolution_spec, hGN]
    rfl
  have hL2 : Tendsto (fun n =>
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
      atTop (𝓝 (G f)) := by
    refine happ.congr (fun n => ?_)
    rw [hGN]
  have hen : Tendsto (fun n => ((responseForm S (a n)
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL))
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)) : ℝ) : EReal))
      atTop (𝓝 (limitFormEnergy G (G f))) := by
    rw [hval]
    have h := (continuous_coe_real_ereal.tendsto _).comp
      (tendsto_const_nhds.inner happ : Tendsto (fun n => inner ℝ f (GN n f)) atTop
        (𝓝 (inner ℝ f (G f))))
    refine h.congr (fun n => ?_)
    simp only [Function.comp_apply, hform n]
  exact hL2.prodMk_nhds hen

/-- For every energy measure of the limiting form, the finite energy measures of the actual
response solutions of the load `f` converge weakly to `Γ(G f)`. -/
theorem goodext_controlled_response_recovery
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
    (E : DirichletForm.ClosedForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcont : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0)
    (Gamma : DirichletForm.EnergyMeasure E) (f : DomainL2 (centeredCube z r hr)) :
    ∀ chi : SpatialCoordinates d → ℝ, Continuous chi → HasCompactSupport chi →
      Tendsto (fun n => ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        chi x * (a n).val x * ∑ i : Fin d, ((sobolevGradient
          (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val i) x) ^ 2)
        atTop (𝓝 (∫ x, chi x ∂(Gamma.measure (G f)))) := by
  obtain ⟨F, hFE, _hNC, hcore, _hregular⟩ := goodext_controlled_regular hd z r hr S hS a A
    c hc hell hrep t alpha ha hcell GN G hGN hConv E hE hcont
  cases hFE
  have hPass := goodext_controlled_energy_measure_convergence hS A GN G hGN hConv F hE hcore Gamma
  obtain ⟨hsym, hpos⟩ := aux_goodext_controlled_response_recovery_sym_pos S a GN G hGN hConv
  have hdom : G f ∈ F.toClosedForm.domain := by
    have hval : limitFormEnergy G (G f) = ((inner ℝ f (G f) : ℝ) : EReal) :=
      iSup_quadraticDual_apply_image G hsym hpos f
    apply DirichletForm.ClosedForm.mem_domain_of_energy_lt_top
    rw [hE, hval]
    exact EReal.coe_lt_top _
  have hrec := aux_goodext_controlled_response_recovery_sequence S a GN G hGN hConv f
  rw [← hE] at hrec
  intro chi hchi _hsupp
  have h := hPass.1 (G f)
    (fun n => responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL))
    hdom hrec chi hchi.continuousOn
  refine h.congr (fun n => ?_)
  exact gradientEnergyMeasure_integral (a n) (sobolevGradient
    (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val) chi

end Paper
