module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452Symmetry

@[expose] public section

/-!
# the one-dimensional integration-by-parts core

The stationary expansion of the integrated second moment
needs `∫ φ·Δφ = -E(φ)` for `φ ∈ C_c²`, and that reduces, coordinate by coordinate through Fubini,
to the one-dimensional statements proved here.

* `integral_deriv_eq_zero_of_compactSupport` — `∫_ℝ g' = 0` for compactly supported `C¹` `g`.
  Mathlib has no such lemma: its divergence theorem
  (`MeasureTheory/Integral/DivergenceTheorem.lean`) is stated for boxes, and there is no
  `integral_deriv_eq_zero`.  The proof is the obvious one — `support_deriv_subset` puts the
  derivative's support inside a compact interval, `intervalIntegral.integral_eq_integral_of_support_subset`
  turns the line integral into an interval integral, and FTC evaluates it at two points where `g`
  vanishes.
* `integral_mul_deriv_eq_neg` — `∫ u v' = -∫ u' v` when `u` has compact support.
* `integral_mul_deriv_deriv` — the specialization `∫ g g'' = -∫ (g')²`, which is the
  one-dimensional form of `∫ φ Δφ = -E(φ)`.

## What remains for the `d`-dimensional statement

Only the Fubini step: writing `∫_{ℝ^d} φ ∂ᵢᵢφ` as an iterated integral with the `i`-th coordinate
innermost and applying `integral_mul_deriv_deriv` there.  On `Vec d = Fin d → ℝ` that is the
`MeasurableEquiv.piFinSuccAbove` / `Measure.pi` decomposition; it is bookkeeping, but it is not
free, and it is the only thing between these lemmas and `∫ φ·fullLaplacian φ = -∫ energyDensity φ`.
-/

set_option autoImplicit false
open MeasureTheory Set Function
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

/-- **The one-dimensional FTC input.**  The integral over the whole line of the derivative of a
compactly supported `C¹` function is zero.  This is the per-coordinate ingredient of the
integration-by-parts identity `∫ φ Δφ = -E(φ)`. -/
theorem integral_deriv_eq_zero_of_compactSupport {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hsupp : HasCompactSupport g) :
    ∫ x : ℝ, deriv g x = 0 := by
  obtain ⟨R, hR⟩ := hsupp.isBounded.subset_closedBall (0 : ℝ)
  set T : ℝ := |R| + 1 with hT
  have hTpos : 0 < T := by rw [hT]; positivity
  have hRabs : R ≤ |R| := le_abs_self R
  have hnegRabs : -|R| ≤ -R := neg_le_neg hRabs
  have hsub : tsupport g ⊆ Set.Ioo (-T) T := by
    intro x hx
    have hx' := hR hx
    rw [Real.closedBall_eq_Icc] at hx'
    have h1 : 0 - R ≤ x := hx'.1
    have h2 : x ≤ 0 + R := hx'.2
    constructor
    · rw [hT]; linarith
    · rw [hT]; linarith
  have hdsub : Function.support (deriv g) ⊆ Set.Ioc (-T) T :=
    support_deriv_subset.trans (hsub.trans Ioo_subset_Ioc_self)
  have hcont : Continuous (deriv g) := (contDiff_one_iff_deriv.mp hg).2
  have hEq : ∫ x in (-T)..T, deriv g x = ∫ x, deriv g x :=
    intervalIntegral.integral_eq_integral_of_support_subset hdsub
  have hftc : ∫ x in (-T)..T, deriv g x = g T - g (-T) :=
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hg.differentiable one_ne_zero).differentiableAt)
      (hcont.intervalIntegrable _ _)
  have hzeroT : g T = 0 :=
    image_eq_zero_of_notMem_tsupport fun hmem => absurd (hsub hmem).2 (lt_irrefl T)
  have hzeronegT : g (-T) = 0 :=
    image_eq_zero_of_notMem_tsupport fun hmem => absurd (hsub hmem).1 (lt_irrefl (-T))
  rw [← hEq, hftc, hzeroT, hzeronegT, sub_zero]

/-- **One-dimensional integration by parts**, for a compactly supported first factor. -/
theorem integral_mul_deriv_eq_neg {u v : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hsupp : HasCompactSupport u) :
    ∫ x, u x * deriv v x = - ∫ x, deriv u x * v x := by
  have hucont : Continuous u := hu.continuous
  have hvcont : Continuous v := hv.continuous
  have hducont : Continuous (deriv u) := (contDiff_one_iff_deriv.mp hu).2
  have hdvcont : Continuous (deriv v) := (contDiff_one_iff_deriv.mp hv).2
  have hprodC1 : ContDiff ℝ 1 (fun x => u x * v x) := hu.mul hv
  have hprodSupp : HasCompactSupport (fun x => u x * v x) := hsupp.mul_right
  have hzero := integral_deriv_eq_zero_of_compactSupport hprodC1 hprodSupp
  have hderiv : ∀ x : ℝ, deriv (fun y => u y * v y) x = deriv u x * v x + u x * deriv v x := by
    intro x
    exact deriv_mul (hu.differentiable one_ne_zero).differentiableAt
      (hv.differentiable one_ne_zero).differentiableAt
  have hint1 : Integrable fun x : ℝ => deriv u x * v x :=
    (hducont.mul hvcont).integrable_of_hasCompactSupport (hsupp.deriv.mul_right)
  have hint2 : Integrable fun x : ℝ => u x * deriv v x :=
    (hucont.mul hdvcont).integrable_of_hasCompactSupport (hsupp.mul_right)
  have hsum : ∫ x, deriv (fun y => u y * v y) x
      = (∫ x, deriv u x * v x) + ∫ x, u x * deriv v x := by
    rw [← integral_add hint1 hint2]
    exact integral_congr_ae (Filter.Eventually.of_forall hderiv)
  rw [hzero] at hsum
  linarith [hsum]

/-- **The one-dimensional form of `∫ φ Δφ = -E(φ)`.** -/
theorem integral_mul_deriv_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hsupp : HasCompactSupport g) :
    ∫ x, g x * deriv (deriv g) x = - ∫ x, (deriv g x) ^ 2 := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hdg1 : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
  have h := integral_mul_deriv_eq_neg hg1 hdg1 hsupp
  rw [h]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
