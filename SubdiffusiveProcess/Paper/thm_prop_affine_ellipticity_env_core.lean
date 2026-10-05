module

public import SubdiffusiveProcess.Paper.thm_prop_affine_ellipticity_core

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Trace ellipticity of the limiting affine response for cutoff-dependent environments.
At every index the actual coefficient has the finite-cutoff chart bounds. Passing to the
response and normalized-ellipticity limits gives the same constant `cell^2/d` as for a
fixed environment. No convergence or joint law of the environments is needed here. -/
theorem thm_prop_affine_ellipticity_env_core
    {d : ℕ} (hd : 0 < d) (I : _root_.SubdiffusiveProcess.Paper.in_J d) (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (env : ℕ → BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (N : ℕ → ℕ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ p : Fin d → ℝ, Tendsto (fun n =>
      affineDirichletResponse (centeredCube_isBounded z hr) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n) (N n) z hr) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
      atTop (𝓝 (p ⬝ᵥ A.mulVec p)))
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (s : ℕ → ℝ)
    (cell loL hiL : ℝ) (hcell : 0 < cell)
    (hlo : Tendsto (fun n => I.lam z r hr
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n) (N n) z hr) z r sigma 2 / s n)
      atTop (𝓝 loL))
    (hhi : Tendsto (fun n => I.Lam z r hr
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n) (N n) z hr) z r sigma 2 / s n)
      atTop (𝓝 hiL))
    (hloL : cell ≤ loL) (hhiL : hiL ≤ cell⁻¹) :
    ∀ p : Fin d → ℝ, cell ^ 2 / (d : ℝ) * Matrix.trace A * (p ⬝ᵥ p) ≤ p ⬝ᵥ A.mulVec p := by
  let : NeZero d := ⟨hd.ne'⟩
  have hfin := fun n => aux_thm_prop_affine_ellipticity_core_finite I z r hr hP
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n) (N n) z hr)
    (cutoffCoefficient model H (env n) (N n))
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous model H (env n) (N n))
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos model H (env n) (N n))
    (FiniteStopping.cutoffCoefficient_ae model H (env n) (N n) z hr) sigma hsigma
  exact aux_thm_prop_affine_ellipticity_core_limit hd A cell hcell
    (fun n p => affineDirichletResponse (centeredCube_isBounded z hr) hP
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n) (N n) z hr) p /
      (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
    (fun n => I.lam z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n) (N n) z hr) z r sigma 2)
    (fun n => I.Lam z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n) (N n) z hr) z r sigma 2)
    s (fun n => I.lam_pos z r hr _ z r sigma 2) (fun n => I.Lam_pos z r hr _ z r sigma 2)
    (fun n p => (hfin n).1 p) (fun n => (hfin n).2) hA hlo hhi hloL hhiL

end
end SubdiffusiveProcess.Paper
