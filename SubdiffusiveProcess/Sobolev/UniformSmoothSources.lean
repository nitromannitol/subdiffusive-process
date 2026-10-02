import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.Algebra.Support

/-! Uniform smooth approximation preserving compact support inside an open set.
No form-domain or energy approximation is asserted. -/
open Set
namespace SubdiffusiveProcess.SmoothSources

/-- A continuous compactly supported function has uniformly close smooth approximations with smaller support. -/
theorem exists_uniform_smooth_approximation {d : ℕ}
    (phi : (Fin d → ℝ) → ℝ) (hc : Continuous phi) (hs : HasCompactSupport phi)
    (U : Set (Fin d → ℝ)) (hU : tsupport phi ⊆ U) (eps : ℝ) (heps : 0 < eps) :
    ∃ psi : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) psi ∧ HasCompactSupport psi ∧
      tsupport psi ⊆ U ∧ ∀ x, |psi x - phi x| < eps := by
  obtain ⟨psi, hpsi, happ, hsub⟩ := hc.exists_contDiff_approx ⊤
    (ε := fun _ => eps) continuous_const (fun _ => heps)
  refine ⟨psi, hpsi, hs.mono hsub, (closure_mono hsub).trans hU, ?_⟩
  intro x
  simpa only [Real.dist_eq] using happ x

end SubdiffusiveProcess.SmoothSources
