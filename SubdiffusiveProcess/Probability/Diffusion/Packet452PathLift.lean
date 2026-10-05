module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452ScopeChecks
public import SubdiffusiveProcess.Probability.Diffusion.Packet452CylinderReversal

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-- A difference of two members of the approximating sequence is `C²` with compact support. -/
theorem approxDiff_contDiff {U : Set (Vec d)} (u : H10Function U) (n m : ℕ) :
    ContDiff ℝ 2 (fun x => u.approx n x - u.approx m x) :=
  have h1 : ContDiff ℝ 2 (u.approx n) := (u.approx_smooth n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have h2 : ContDiff ℝ 2 (u.approx m) := (u.approx_smooth m).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  h1.sub h2

theorem approxDiff_hasCompactSupport {U : Set (Vec d)} (u : H10Function U) (n m : ℕ) :
    HasCompactSupport (fun x => u.approx n x - u.approx m x) :=
  (u.approx_hasCompactSupport n).sub (u.approx_hasCompactSupport m)

/-- **Step 1.**  The maximal estimate applied to `aₙ − aₘ`, with the derivative of the difference
already split. -/
theorem maximalEstimate_approxDiff (hmax : maximalEstimateGoal d) {U : Set (Vec d)}
    (u : H10Function U) (n m : ℕ) (T : ℝ≥0) :
    (∫⁻ x, ∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
        ENNReal.ofReal ((u.approx n (ω t) - u.approx m (ω t)) ^ 2))
        ∂(laplacianContinuousLaw d x) ∂volume)
      ≤ ENNReal.ofReal (32 * ((∫ x, (u.approx n x - u.approx m x) ^ 2)
          + (T : ℝ) * ∫ x, ∑ i : Fin d,
            (fderiv ℝ (u.approx n) x (Pi.single i 1)
              - fderiv ℝ (u.approx m) x (Pi.single i 1)) ^ 2)) := by
  have hdiffn : ∀ x : Vec d, DifferentiableAt ℝ (u.approx n) x := fun x =>
    ((u.approx_smooth n).differentiable (by simp)).differentiableAt
  have hdiffm : ∀ x : Vec d, DifferentiableAt ℝ (u.approx m) x := fun x =>
    ((u.approx_smooth m).differentiable (by simp)).differentiableAt
  have hgrad : ∀ (x : Vec d) (i : Fin d),
      fderiv ℝ (fun y => u.approx n y - u.approx m y) x (Pi.single i 1)
        = fderiv ℝ (u.approx n) x (Pi.single i 1)
          - fderiv ℝ (u.approx m) x (Pi.single i 1) := by
    intro x i
    rw [((hdiffn x).hasFDerivAt.fun_sub (hdiffm x).hasFDerivAt).fderiv]
    rfl
  have h := hmax (fun x => u.approx n x - u.approx m x) (approxDiff_contDiff u n m)
    (approxDiff_hasCompactSupport u n m) T
  simpa only [hgrad] using h

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
