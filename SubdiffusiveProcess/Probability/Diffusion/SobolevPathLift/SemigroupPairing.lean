module

public import SubdiffusiveProcess.Probability.Diffusion.LaplacianGenerator

@[expose] public section

/-!
# Continuity in time of the semigroup pairing `r ↦ ⟨f, P_r g⟩`

  §2.3 needs the pairings
`G(t) = ⟨φ, P_t φ⟩` and `K(v) = ⟨Δφ, P_v Δφ⟩` to be **continuous in time**: that is what makes the
two applications of the fundamental theorem of calculus legitimate (`intervalIntegral`'s FTC needs
interval integrability of the derivative, and continuity is the cheapest sufficient condition), and
it is the "`L²` continuity of `r ↦ ⟨φ, P_r φ⟩`".

**No `L²` theory is needed for it.**  The semigroup is already packaged as a strongly continuous
contraction semigroup on `C₀(Vec d, ℝ)` (`isFeller_laplacianSemigroup.c0Semigroup`, used in
`LaplacianGenerator.lean` for the generator), so `r ↦ P_r g` is continuous **in the sup norm**.
Pairing against a fixed `f ∈ L¹` is then a Lipschitz map `C₀(Vec d, ℝ) → ℝ` with constant
`∫ |f|`, by the trivial bound `|∫ f·u| ≤ (∫ |f|)·‖u‖_∞`.  Composing gives the continuity, with no
strong-`L²`-continuity argument, no dominated convergence over the Gaussian, and no heat-kernel
estimate: the `C₀` orbit continuity that the Feller property already supplies does all the work.

* `abs_c0_apply_le`, `integrable_mul_c0`, `abs_integral_mul_c0_le` -- the sup-norm bound.
* `lipschitzWith_pairing_c0` -- pairing against `f ∈ L¹` is Lipschitz on `C₀`.
* `continuous_semigroup_pairing` / `continuous_semigroup_pairing_real` -- the payoff, in the
  `NNReal` and `ℝ` time parametrizations.
* `continuous_semigroup_pairing_integral` -- the same, written with the raw kernel integral
  `∫ y, g y ∂(laplacianSemigroup d (Real.toNNReal r) x)`, which is the form the expansion in §2
  produces.

In the application `f` and `g` are both `φ` (or both `Δφ`), compactly supported and `C²`, hence
integrable and in `C₀`; the statements are kept asymmetric (`f` merely integrable, `g` in `C₀`)
because that is exactly what the proof uses.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-! ## Pairing against an `L¹` function is Lipschitz on `C₀` -/

/-- Pointwise bound by the `C₀` norm. -/
theorem abs_c0_apply_le (u : C₀(Vec d, ℝ)) (x : Vec d) : |u x| ≤ ‖u‖ := by
  simpa [Real.norm_eq_abs] using u.toBCF.norm_coe_le_norm x

theorem integrable_mul_c0 {f : Vec d → ℝ} (hf : Integrable f) (u : C₀(Vec d, ℝ)) :
    Integrable (fun x => f x * u x) :=
  hf.mul_bdd (map_continuous u).aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using abs_c0_apply_le u x)

theorem abs_integral_mul_c0_le {f : Vec d → ℝ} (hf : Integrable f) (u : C₀(Vec d, ℝ)) :
    |∫ x, f x * u x| ≤ (∫ x, |f x|) * ‖u‖ := by
  calc |∫ x, f x * u x| ≤ ∫ x, |f x * u x| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, |f x| * ‖u‖ := by
        refine integral_mono (integrable_mul_c0 hf u).abs (hf.abs.mul_const _) fun x => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_c0_apply_le u x) (abs_nonneg _)
    _ = (∫ x, |f x|) * ‖u‖ := integral_mul_const _ _

/-- **Pairing against a fixed `L¹` function is Lipschitz on `C₀`**, with constant `∫ |f|`.  This
is the only analytic input; everything else is the semigroup's own orbit continuity. -/
theorem lipschitzWith_pairing_c0 {f : Vec d → ℝ} (hf : Integrable f) :
    LipschitzWith (Real.toNNReal (∫ x, |f x|)) fun u : C₀(Vec d, ℝ) => ∫ x, f x * u x := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  have hcoe : ((Real.toNNReal (∫ x, |f x|) : ℝ≥0) : ℝ) = ∫ x, |f x| :=
    Real.coe_toNNReal _ (integral_nonneg fun x => abs_nonneg _)
  rw [Real.dist_eq, hcoe]
  have hsub : (∫ x, f x * u x) - ∫ x, f x * v x = ∫ x, f x * (u - v) x := by
    rw [← integral_sub (integrable_mul_c0 hf u) (integrable_mul_c0 hf v)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [mul_sub]
  rw [hsub]
  exact (abs_integral_mul_c0_le hf (u - v)).trans_eq (by rw [dist_eq_norm])

theorem continuous_pairing_c0 {f : Vec d → ℝ} (hf : Integrable f) :
    Continuous fun u : C₀(Vec d, ℝ) => ∫ x, f x * u x :=
  (lipschitzWith_pairing_c0 hf).continuous

/-! ## Continuity in time -/

/-- **The semigroup pairing is continuous in time.**  `r ↦ P_r g` is continuous in the sup norm
because the semigroup is strongly continuous on `C₀`; pairing against `f ∈ L¹` is Lipschitz. -/
theorem continuous_semigroup_pairing {f : Vec d → ℝ} (hf : Integrable f) (g : C₀(Vec d, ℝ)) :
    Continuous fun r : ℝ≥0 =>
      ∫ x, f x * (isFeller_laplacianSemigroup (d := d)).c0Semigroup r g x :=
  (continuous_pairing_c0 hf).comp
    (Semigroup.StronglyContinuousContractionSemigroup.continuous_operator_apply _
      continuous_id continuous_const)

/-- The same, in the real time parametrization. -/
theorem continuous_semigroup_pairing_real {f : Vec d → ℝ} (hf : Integrable f)
    (g : C₀(Vec d, ℝ)) :
    Continuous fun r : ℝ =>
      ∫ x, f x * (isFeller_laplacianSemigroup (d := d)).c0Semigroup (Real.toNNReal r) g x :=
  (continuous_semigroup_pairing hf g).comp continuous_real_toNNReal

/-- The payoff in the shape the stationary expansion produces: the pairing written with the raw
kernel integral against `laplacianSemigroup`. -/
theorem continuous_semigroup_pairing_integral {f : Vec d → ℝ} (hf : Integrable f)
    (g : C₀(Vec d, ℝ)) :
    Continuous fun r : ℝ =>
      ∫ x, f x * ∫ y, g y ∂(laplacianSemigroup d (Real.toNNReal r) x) :=
  continuous_semigroup_pairing_real hf g

end SubdiffusiveProcess.Probability.Diffusion
