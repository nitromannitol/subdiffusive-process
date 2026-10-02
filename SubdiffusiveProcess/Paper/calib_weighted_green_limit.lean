import SubdiffusiveProcess.Paper.calib_volumeResponseOperator_sub_norm_le
import SubdiffusiveProcess.Paper.prop_conc_controlled_weighted_convergence
import SubdiffusiveProcess.Paper.limit_form_package_controls
import SubdiffusiveProcess.Sobolev.VolumeResponseOperator

/-! Weighted Green-operator limit for a coefficient sequence that is a fixed continuous weight times a controlled
sequence up to a factor `exp (± D_n)` with `D_n → 0`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology
noncomputable section
namespace Paper

/-- The analytic controls extracted from represented bounds are the analytic controls of the concentration
package (the two structures have the same fields). -/
def aux_calib_weighted_green_limit_controls {d : ℕ} {hd : 2 ≤ d}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a) :
    aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a where
  K := A.K
  K_pos := A.K_pos
  coercive := A.coercive
  interpolation := A.interpolation
  sources := A.sources
  sources_countable := A.sources_countable
  sources_dense := A.sources_dense
  sources_smooth := A.sources_smooth
  mesh := A.mesh
  t := A.t
  t_lower := A.t_lower
  t_upper := A.t_upper
  cutoffs := A.cutoffs

/-- **Weighted Green limit.** -/
theorem calib_weighted_green_limit
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a b b' : ℕ → PositiveCoefficient (centeredCube z r hr))
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
    (hb' : ∀ n, (b' n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (D : ℕ → ℝ) (hD0 : ∀ n, 0 ≤ D n) (hD : Tendsto D atTop (𝓝 0))
    (hlow : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      Real.exp (-D n) * (b' n).val x ≤ (b n).val x)
    (hup : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (b n).val x ≤ Real.exp (D n) * (b' n).val x) :
    ∃ (F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
      (EF : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      Tendsto (fun n => volumeResponseOperator S (b n)) atTop (𝓝 F) ∧
      (∀ x y, inner ℝ (F x) y = inner ℝ x (F y)) ∧
      (∀ x, 0 ≤ inner ℝ x (F x)) ∧
      (∀ u, EF.energy u = limitFormEnergy F u) ∧
      E.domain = EF.domain ∧
      (∃ C, DirichletForm.IsCoreOn EF.toClosedForm
        (centeredCube z r hr : Set (SpatialCoordinates d)) C) ∧
      ∀ u ∈ E.domain, EF.form u u = ∫ x, rho x ∂(Gamma.measure u) := by
  obtain ⟨FN, F, EF, hFN, hFconv, hFsym, hFpos, hEF, hdom, hFcore, hEFform⟩ :=
    prop_conc_controlled_weighted_convergence hd z r hr S hS a b' A GN G hGN hConvG E hE hcore
      Gamma rho hcont hpos hb'
  refine ⟨F, EF, ?_, hFsym, hFpos, hEF, hdom, hFcore, hEFform⟩
  have hFNeq : ∀ n, FN n = volumeResponseOperator S (b' n) := by
    intro n
    ext f
    rw [hFN n f, volumeResponseOperator_apply]
  have hbound : ∀ n, ‖volumeResponseOperator S (b n) - FN n‖ ≤
      2 * (Real.exp (D n) - 1) * ‖FN n‖ := by
    intro n
    rw [hFNeq n]
    exact calib_volumeResponseOperator_sub_norm_le S (b' n) (b n) (D n) (hD0 n) (hlow n) (hup n)
  have hzero : Tendsto (fun n => 2 * (Real.exp (D n) - 1) * ‖FN n‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => 2 * (Real.exp (D n) - 1)) atTop (𝓝 0) := by
      have h4 := ((Real.continuous_exp.tendsto 0).comp hD)
      rw [Real.exp_zero] at h4
      have h5 := (h4.sub_const 1).const_mul 2
      simp only [sub_self, mul_zero] at h5
      exact h5
    have h2 : Tendsto (fun n => ‖FN n‖) atTop (𝓝 ‖F‖) := hFconv.norm
    have := h1.mul h2
    rw [zero_mul] at this
    exact this
  have hsub : Tendsto (fun n => volumeResponseOperator S (b n) - FN n) atTop (𝓝 0) :=
    squeeze_zero_norm' (Eventually.of_forall hbound) hzero
  have h3 := hsub.add hFconv
  rw [zero_add] at h3
  simpa only [sub_add_cancel] using h3

end Paper
