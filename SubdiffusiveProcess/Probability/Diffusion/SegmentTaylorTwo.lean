module

public import SubdiffusiveProcess.Probability.Diffusion.StandardGaussianQuarticMoments

@[expose] public section

/-!
# The second-order Taylor remainder along a segment

 §1, Steps 1-2.

The central structural point is that Mathlib has no multivariate Taylor theorem with an
integral remainder at this toolchain — its own module docstring lists the integral form as a TODO
— so the multivariate expansion has to be reduced to a one-variable statement along the segment
`t ↦ x + t • h`.  The natural route for that is `taylor_mean_remainder_lagrange` at degree one,
which gives the sharp constant `1/2` at the price of `iteratedDerivWithin` bookkeeping.

The route taken here is shorter and needs no Taylor theorem at all: the mean-value **inequality**
(`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) applied twice on `Icc 0 1`, first to the
first-derivative error and then to the function error.  It pays a constant `1` instead of `1/2`,
which suffices (the `ε`-`δ` assembly only needs *some* finite constant),
and it keeps everything in terms of `HasDerivAt`.

* `hasDerivAt_lineMap`, `hasDerivAt_comp_lineMap`, `hasDerivAt_fderiv_comp_lineMap` — the chain
  rule along the segment, twice, proof on `iteratedFDeriv ℝ 2 ψ` through
  `iteratedFDeriv_two_apply`.  The second derivative is reached by composing the differential of
  `fderiv ℝ ψ` with the evaluation-at-`h` continuous linear map
  (`ContinuousLinearMap.apply ℝ ℝ h`), which is what turns a `fderiv` of a `fderiv` into a genuine
  one-variable derivative.
* `abs_taylor_two_le` — the remainder bound

  `|ψ(x+h) − ψ(x) − Dψ(x)h − ½D²ψ(x)[h,h]| ≤ M‖h‖²`,

  where `M` bounds the operator norm of `D²ψ(x+sh) − D²ψ(x)` for `s ∈ [0,1]`.  The bilinear step
  is `ContinuousMultilinearMap.le_opNorm` at `![h,h]`, whose product of norms is `‖h‖²` by
  `Fin.prod_univ_two`.

`‖·‖` on `Vec d` is the **sup** norm (`Vec d = Fin d → ℝ` carries Mathlib's default Pi instance),
so both `‖h‖²` and the modulus of continuity here are sup-norm quantities; the exchange with the
Euclidean `vecNormSq` belongs to the Gaussian integration step, not here.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The affine line `t ↦ x + t • h`. -/
theorem hasDerivAt_lineMap (x h : Vec d) (s : ℝ) :
    HasDerivAt (fun t : ℝ => x + t • h) h s := by
  simpa using ((hasDerivAt_id s).smul_const h).const_add x

/-- The first derivative of `ψ` along the line. -/
theorem hasDerivAt_comp_lineMap {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 2 ψ) (x h : Vec d) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ψ (x + t • h)) (fderiv ℝ ψ (x + s • h) h) s := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  exact (hd (x + s • h)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_lineMap x h s)

/-- The second derivative of `ψ` along the line, read as the second iterated derivative. -/
theorem hasDerivAt_fderiv_comp_lineMap {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 2 ψ) (x h : Vec d) (s : ℝ) :
    HasDerivAt (fun t : ℝ => fderiv ℝ ψ (x + t • h) h)
      (iteratedFDeriv ℝ 2 ψ (x + s • h) ![h, h]) s := by
  have hfd : Differentiable ℝ (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ ψ (x + t • h))
      (fderiv ℝ (fderiv ℝ ψ) (x + s • h) h) s :=
    (hfd (x + s • h)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_lineMap x h s)
  have h3 := (ContinuousLinearMap.apply ℝ ℝ h).hasFDerivAt.comp_hasDerivAt s h2
  rw [iteratedFDeriv_two_apply]
  simpa [Function.comp_def] using h3

/-- **The second-order Taylor remainder along a segment.**  The constant is `1`, not the sharp
`1/2`: the bound comes from the mean-value inequality applied twice rather than from an integral
remainder, and any finite constant suffices downstream. -/
theorem abs_taylor_two_le {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 2 ψ) (x h : Vec d) {M : ℝ}
    (hM : ∀ s ∈ Set.Icc (0:ℝ) 1,
      ‖iteratedFDeriv ℝ 2 ψ (x + s • h) - iteratedFDeriv ℝ 2 ψ x‖ ≤ M) :
    |ψ (x + h) - ψ x - fderiv ℝ ψ x h - (1/2) * iteratedFDeriv ℝ 2 ψ x ![h, h]|
      ≤ M * ‖h‖ ^ 2 := by
  set A : ℝ := fderiv ℝ ψ x h with hA
  set B : ℝ := iteratedFDeriv ℝ 2 ψ x ![h, h] with hB
  set u : ℝ → ℝ := fun t => fderiv ℝ ψ (x + t • h) h - A - t * B with hu
  have hMnn : 0 ≤ M := by
    have := hM 0 (by simp)
    simpa using this
  have hhsq : (0:ℝ) ≤ M * ‖h‖ ^ 2 := by positivity
  have hderivu : ∀ t : ℝ, HasDerivAt u
      (iteratedFDeriv ℝ 2 ψ (x + t • h) ![h, h] - B) t := by
    intro t
    have h1 := hasDerivAt_fderiv_comp_lineMap hψ x h t
    have h2 : HasDerivAt (fun r : ℝ => r * B) B t := by
      simpa using (hasDerivAt_id t).mul_const B
    simpa [hu, Pi.sub_def] using! (h1.sub_const A).sub h2
  have hbdd : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖iteratedFDeriv ℝ 2 ψ (x + t • h) ![h, h] - B‖ ≤ M * ‖h‖ ^ 2 := by
    intro t ht
    have hsplit : iteratedFDeriv ℝ 2 ψ (x + t • h) ![h, h] - B
        = (iteratedFDeriv ℝ 2 ψ (x + t • h) - iteratedFDeriv ℝ 2 ψ x) ![h, h] := by
      rw [sub_apply]
    rw [hsplit]
    refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
    have hprod : ∏ i : Fin 2, ‖(![h, h] : Fin 2 → Vec d) i‖ = ‖h‖ ^ 2 := by
      rw [Fin.prod_univ_two]
      simp [sq]
    rw [hprod]
    exact mul_le_mul_of_nonneg_right (hM t ht) (by positivity)
  have hu0 : u 0 = 0 := by simp [hu, hA]
  have hubound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖u t‖ ≤ M * ‖h‖ ^ 2 := by
    intro t ht
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := u) (f' := fun r => iteratedFDeriv ℝ 2 ψ (x + r • h) ![h, h] - B)
      (s := Set.Icc (0:ℝ) 1) (C := M * ‖h‖ ^ 2) (x := (0:ℝ)) (y := t)
      (fun r _ => (hderivu r).hasDerivWithinAt) hbdd (convex_Icc 0 1) (by simp) ht
    rw [hu0, sub_zero] at hmvt
    refine hmvt.trans ?_
    have ht1 : ‖t - (0:ℝ)‖ ≤ 1 := by
      rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact ht.2
    nlinarith [hhsq]
  set v : ℝ → ℝ := fun t => ψ (x + t • h) - ψ x - t * A - t ^ 2 / 2 * B with hv
  have hderivv : ∀ t : ℝ, HasDerivAt v (u t) t := by
    intro t
    have h1 := hasDerivAt_comp_lineMap hψ x h t
    have h2 : HasDerivAt (fun r : ℝ => r * A) A t := by
      simpa using (hasDerivAt_id t).mul_const A
    have h3 : HasDerivAt (fun r : ℝ => r ^ 2 / 2 * B) (t * B) t := by
      have : HasDerivAt (fun r : ℝ => r ^ 2 / 2) t t := by
        simpa using (hasDerivAt_pow 2 t).div_const 2
      simpa using this.mul_const B
    simpa [hv, hu, Pi.sub_def] using! (((h1.sub_const (ψ x)).sub h2).sub h3)
  have hv0 : v 0 = 0 := by simp [hv]
  have hfinal := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := v) (f' := u) (s := Set.Icc (0:ℝ) 1) (C := M * ‖h‖ ^ 2) (x := (0:ℝ)) (y := (1:ℝ))
    (fun r _ => (hderivv r).hasDerivWithinAt) hubound (convex_Icc 0 1) (by simp) (by simp)
  rw [hv0, sub_zero] at hfinal
  have hv1 : v 1 = ψ (x + h) - ψ x - A - (1/2) * B := by
    simp only [hv, one_smul, one_mul, one_pow]
  rw [hv1] at hfinal
  simpa [Real.norm_eq_abs] using hfinal

end SubdiffusiveProcess.Probability.Diffusion
