import SubdiffusiveProcess.Probability.Diffusion.Packet452ScopeChecks
import SubdiffusiveProcess.Probability.Diffusion.GaussianDifferenceQuotient




set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}



def fullLaplacian (φ : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ i, iteratedFDeriv ℝ 2 φ x ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)]

/-- The Dirichlet energy density, the coordinate sum -- not the square of the ambient
(sup) norm of the gradient. -/
def energyDensity (φ : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ i, (fderiv ℝ φ x (Pi.single i (1:ℝ))) ^ 2

theorem fderiv_sq {φ : Vec d → ℝ} (hφ : ContDiff ℝ 2 φ) (x : Vec d) :
    fderiv ℝ (fun z => φ z ^ 2) x = (2 * φ x) • fderiv ℝ φ x := by
  have hd : DifferentiableAt ℝ φ x := (hφ.differentiable (by norm_num)).differentiableAt
  have h := hd.hasFDerivAt.pow 2
  simpa using h.fderiv

theorem fderiv_fderiv_sq_apply {φ : Vec d → ℝ} (hφ : ContDiff ℝ 2 φ) (x u v : Vec d) :
    fderiv ℝ (fderiv ℝ (fun z => φ z ^ 2)) x u v
      = 2 * φ x * (fderiv ℝ (fderiv ℝ φ) x u v)
        + 2 * (fderiv ℝ φ x u) * (fderiv ℝ φ x v) := by
  have hfd : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hfun : fderiv ℝ (fun z => φ z ^ 2) = fun z => (2 * φ z) • fderiv ℝ φ z :=
    funext fun z => fderiv_sq hφ z
  rw [hfun]
  have hc : HasFDerivAt (fun z : Vec d => 2 * φ z) ((2 : ℝ) • fderiv ℝ φ x) x := by
    simpa using ((hd x).hasFDerivAt.const_mul (2 : ℝ))
  have hf : HasFDerivAt (fun z : Vec d => fderiv ℝ φ z) (fderiv ℝ (fderiv ℝ φ) x) x :=
    (hfd x).hasFDerivAt
  have hprod := hc.fun_smul hf
  rw [hprod.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]

/-- **The generator product identity** of `ledger/reports/P-452-agent1.md` §2.2:
`Δ(φ²) - 2φΔφ = 2 ∑ᵢ (∂ᵢφ)²`. -/
theorem fullLaplacian_sq_sub {φ : Vec d → ℝ} (hφ : ContDiff ℝ 2 φ) (x : Vec d) :
    fullLaplacian (fun z => φ z ^ 2) x - 2 * φ x * fullLaplacian φ x
      = 2 * energyDensity φ x := by
  unfold fullLaplacian energyDensity
  have hterm : ∀ i : Fin d,
      iteratedFDeriv ℝ 2 (fun z => φ z ^ 2) x ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)]
        = 2 * φ x * iteratedFDeriv ℝ 2 φ x ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)]
          + 2 * (fderiv ℝ φ x (Pi.single i (1:ℝ))) ^ 2 := by
    intro i
    rw [iteratedFDeriv_two_eq_bilin, iteratedFDeriv_two_eq_bilin,
      fderiv_fderiv_sq_apply hφ]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.mul_sum]
  ring

/-! ## The constant `32` of (2.1) -/

/-- The three-term Cauchy-Schwarz used on `|φ(B₀)| + ½ sup|M| + sup|M̂|`. -/
theorem sq_three_term_le (a b c : ℝ) :
    (a + (1 / 2) * b + c) ^ 2 ≤ 3 * (a ^ 2 + (1 / 4) * b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - (1/2) * b), sq_nonneg (a - c), sq_nonneg ((1/2) * b - c)]

/-- **The constant assembly of (2.1).**  From the three-term bound and the two Doob bounds
`8 T E(φ)` on the integrated maximal squares of the forward and reversed martingales, the
integrated maximal square is at most `3‖φ‖₂² + 30 T E(φ)`, hence at most
`32(‖φ‖₂² + T E(φ))`.  The `32` is a convenient bound, not a sharp constant. -/
theorem maximal_estimate_constant {S N MB MC T E : ℝ}
    (hTE : 0 ≤ T * E) (hN : 0 ≤ N)
    (hS : S ≤ 3 * (N + (1 / 4) * MB + MC))
    (hMB : MB ≤ 8 * (T * E)) (hMC : MC ≤ 8 * (T * E)) :
    S ≤ 32 * (N + T * E) := by
  nlinarith [hS, hMB, hMC, hTE, hN]

/-- The intermediate form the report displays, `3‖φ‖₂² + 30 T E(φ)`. -/
theorem maximal_estimate_intermediate {S N MB MC T E : ℝ}
    (hS : S ≤ 3 * (N + (1 / 4) * MB + MC))
    (hMB : MB ≤ 8 * (T * E)) (hMC : MC ≤ 8 * (T * E)) :
    S ≤ 3 * N + 30 * (T * E) := by
  nlinarith [hS, hMB, hMC]

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
