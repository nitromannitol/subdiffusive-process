module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.Exhaustion

@[expose] public section

/-!
# Self-adjointness of the Brownian semigroup

 §2.2, continuing `SobolevPathLift/Stationarity.lean`.

The second payoff of `laplacianDensity_symm`, after the invariance of Lebesgue measure: the
semigroup pairing may be moved from one argument to the other,

```text
∫ f(x) (P_t g)(x) dx = ∫ g(y) (P_t f)(y) dy,
```

stated in `ℝ≥0∞` so that no integrability side condition is needed.  `lintegral_semigroup_eq_density`
is the intermediate readout of the semigroup average against the kernel.

## Why this matters for the second moment

The remaining obligation is the integrated Dynkin second moment `∫ E_x M_T² dx = 2T E(φ)`.
Checked against the `MarkovProcess` Dynkin API — `dynkinProcess`, `norm_dynkinProcess_le`,
`continuous_dynkinProcess`, `adapted_dynkinProcess`, `dynkinProcess_eq_add_shift`,
`integrable_dynkinProcess`, `integral_dynkinProcess`, `martingale_dynkinProcess` — there is **no**
second-moment statement, no quadratic variation, and no Doob inequality anywhere in that package.
Deriving `E_x M_T² = ∫₀^T E_x[(Δ(φ²) − 2φΔφ)(B_r)] dr` *pointwise in `x`* from the martingale
property alone needs either Itô's formula or a partition/derivative argument, neither of which the
tree has.

But the target is the **integrated** second moment, under the invariant measure.  There the whole
computation collapses to `L²` pairings against the semigroup: every term of
`∫ E_x[(φ(B_T) − φ(B_0) − ∫₀^T Δφ(B_r)dr)²] dx` expands, by stationarity
(`lintegral_path_eval_invariant`) and this self-adjointness, into integrals of `φ` and `Δφ`
against `P_r`, with no pathwise stochastic calculus.  That is the route this file is the first step
of, and it is why the two symmetry consequences are proved before the martingale work.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift

variable {d : ℕ}

/-- The semigroup average of a nonnegative measurable function, written against the kernel. -/
theorem lintegral_semigroup_eq_density {t : ℝ} (ht : 0 < t) {g : Vec d → ℝ≥0∞}
    (hg : Measurable g) (x : Vec d) :
    (∫⁻ y, g y ∂(laplacianSemigroup d (Real.toNNReal t) x))
      = ∫⁻ y, ENNReal.ofReal (laplacianDensity t x y) * g y ∂volume := by
  have hdens : Measurable fun y : Vec d => ENNReal.ofReal (laplacianDensity t x y) :=
    ((measurable_uncurry_laplacianDensity (d := d) t).of_uncurry_left (x := x)).ennreal_ofReal
  rw [laplacianSemigroup_eq_withDensity ht x, lintegral_withDensity_eq_lintegral_mul _ hdens hg]
  rfl

/-- **The Brownian semigroup is self-adjoint in `L²(dx)`**, in the `ℝ≥0∞` form that needs no
integrability side condition.  This is the second payoff of `laplacianDensity_symm`, after the
invariance of Lebesgue measure: the semigroup pairing may be moved from one argument to the
other. -/
theorem lintegral_semigroup_symm {t : ℝ} (ht : 0 < t) {f g : Vec d → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * (∫⁻ y, g y ∂(laplacianSemigroup d (Real.toNNReal t) x)) ∂volume)
      = ∫⁻ y, g y * (∫⁻ x, f x ∂(laplacianSemigroup d (Real.toNNReal t) y)) ∂volume := by
  have hjoint : Measurable fun p : Vec d × Vec d =>
      f p.1 * (ENNReal.ofReal (laplacianDensity t p.1 p.2) * g p.2) :=
    (hf.comp measurable_fst).mul
      (((measurable_uncurry_laplacianDensity (d := d) t).ennreal_ofReal).mul
        (hg.comp measurable_snd))
  have hleft : (∫⁻ x, f x * (∫⁻ y, g y ∂(laplacianSemigroup d (Real.toNNReal t) x)) ∂volume)
      = ∫⁻ x, ∫⁻ y, f x * (ENNReal.ofReal (laplacianDensity t x y) * g y) ∂volume ∂volume := by
    refine lintegral_congr fun x => ?_
    rw [lintegral_semigroup_eq_density ht hg x, lintegral_const_mul _ ?_]
    exact (((measurable_uncurry_laplacianDensity (d := d) t).of_uncurry_left
      (x := x)).ennreal_ofReal).mul hg
  have hright : (∫⁻ y, g y * (∫⁻ x, f x ∂(laplacianSemigroup d (Real.toNNReal t) y)) ∂volume)
      = ∫⁻ y, ∫⁻ x, f x * (ENNReal.ofReal (laplacianDensity t x y) * g y) ∂volume ∂volume := by
    refine lintegral_congr fun y => ?_
    have hmeas : Measurable fun x : Vec d =>
        ENNReal.ofReal (laplacianDensity t y x) * f x :=
      (((measurable_uncurry_laplacianDensity (d := d) t).of_uncurry_left
        (x := y)).ennreal_ofReal).mul hf
    rw [lintegral_semigroup_eq_density ht hf y, ← lintegral_const_mul _ hmeas]
    refine lintegral_congr fun x => ?_
    rw [laplacianDensity_symm t y x]
    ring
  rw [hleft, hright, lintegral_lintegral_swap hjoint.aemeasurable]

end SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift
