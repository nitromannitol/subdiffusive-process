module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.CrossTerms

@[expose] public section

/-!
# The diagonal term `Q` of §2.2, reduced to a double semigroup pairing

  §2.2:

```text
E_x[(∫₀ᵀ ψ(B_r) dr)²] = ∫₀ᵀ∫₀ᵀ E_x[ψ(B_r)ψ(B_{r'})] dr dr',
∫ₓ E_x[ψ(B_r)ψ(B_{r'})] dx = ⟨ψ, P_{|r−r'|} ψ⟩.
```

The first line is **two applications of one lemma**: `intervalIntegral_integral_swap_path_mul`, the
path/time Fubini of `SobolevPathLift.Markov` carrying an extra bounded measurable factor.  Writing the
square as `Y·Y` and expanding one factor at a time costs nothing and avoids ever building a
two-parameter product measure -- the swap is used twice with different bounded factors (`Y`
itself, then `ψ(B_s)`), each time on the *same* `Ioc 0 T × path` product.

The second line is, verbatim, `integral_cross_term_eval` from `SobolevPathLift.CrossTerms` with
`h = g = ψ`: the "cross term" and the "diagonal pair" are the same identity, read at different
times.  Only the case split `r ≤ r'` / `r' ≤ r` and the truncated-subtraction bookkeeping
`toNNReal r' − toNNReal r = toNNReal |r − r'|` are new.

Combined with `integral_integral_abs_sub` (`SobolevPathLift.CrossTerms`), what remains for `Q` is the
`x`-Fubini for the `dr dr'` integral against the **infinite** Lebesgue measure; that is the one
step of §2; `SobolevPathLift.DiagonalFubini` carries it out and records the dominating function.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift

variable {d : ℕ}

/-- Joint continuity of `(s, ω) ↦ ψ (ω s)` in the time and the path. -/
theorem continuous_path_eval_prod (ψ : C₀(Vec d, ℝ)) :
    Continuous fun p : ℝ × ContinuousPath (Vec d) => ψ (p.2 (Real.toNNReal p.1)) :=
  (map_continuous ψ).comp
    ((ContinuousEval.continuous_eval.comp continuous_swap).comp
      (continuous_real_toNNReal.fst'.prodMk continuous_snd))

/-- The time integral of a `C₀` observable along a path. -/
def timeIntegralPath (ψ : C₀(Vec d, ℝ)) (T : ℝ≥0) (ω : ContinuousPath (Vec d)) : ℝ :=
  ∫ s in (0 : ℝ)..(T : ℝ), ψ (ω (Real.toNNReal s))

theorem stronglyMeasurable_timeIntegralPath (ψ : C₀(Vec d, ℝ)) (T : ℝ≥0) :
    StronglyMeasurable (timeIntegralPath ψ T) := by
  have hprod := SubMarkovKernelSemigroup.stronglyMeasurable_integral_prod
    (Omega := ContinuousPath (Vec d)) (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))
    (phi := fun p : ℝ × ContinuousPath (Vec d) => ψ (p.2 (Real.toNNReal p.1)))
    (continuous_path_eval_prod ψ).stronglyMeasurable
  have hfun : timeIntegralPath ψ T
      = fun ω : ContinuousPath (Vec d) =>
        ∫ s, ψ (ω (Real.toNNReal s)) ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
    funext ω
    exact intervalIntegral.integral_of_le T.coe_nonneg
  rw [hfun]
  exact hprod

theorem abs_timeIntegralPath_le (ψ : C₀(Vec d, ℝ)) (T : ℝ≥0) (ω : ContinuousPath (Vec d)) :
    |timeIntegralPath ψ T ω| ≤ ‖ψ‖ * (T : ℝ) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (T : ℝ)) (C := ‖ψ‖)
    (f := fun s : ℝ => ψ (ω (Real.toNNReal s)))
    (fun s _ => SubMarkovKernelSemigroup.norm_c0_apply_le ψ _)
  rwa [sub_zero, abs_of_nonneg T.coe_nonneg, Real.norm_eq_abs] at h

/-- **The path/time Fubini with a bounded factor.**  Same template as
`intervalIntegral_integral_swap_path`, with the extra measurable bounded `Φ`. -/
theorem intervalIntegral_integral_swap_path_mul (ψ : C₀(Vec d, ℝ)) (T : ℝ≥0) (x : Vec d)
    {Φ : ContinuousPath (Vec d) → ℝ} (hΦ : StronglyMeasurable Φ) {CΦ : ℝ}
    (hΦb : ∀ ω, |Φ ω| ≤ CΦ) :
    (∫ s in (0 : ℝ)..(T : ℝ),
        ∫ ω, Φ ω * ψ (ω (Real.toNNReal s)) ∂(laplacianContinuousLaw d x))
      = ∫ ω, Φ ω * timeIntegralPath ψ T ω ∂(laplacianContinuousLaw d x) := by
  have hjoint : StronglyMeasurable fun p : ℝ × ContinuousPath (Vec d) =>
      Φ p.2 * ψ (p.2 (Real.toNNReal p.1)) :=
    (hΦ.comp_measurable measurable_snd).mul (continuous_path_eval_prod ψ).stronglyMeasurable
  have hbound : ∀ p : ℝ × ContinuousPath (Vec d),
      ‖Φ p.2 * ψ (p.2 (Real.toNNReal p.1))‖ ≤ CΦ * ‖ψ‖ := by
    intro p
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hΦb p.2)
      (by simpa [Real.norm_eq_abs] using SubMarkovKernelSemigroup.norm_c0_apply_le ψ _)
      (abs_nonneg _) (le_trans (abs_nonneg _) (hΦb p.2))
  have hprodint : Integrable
      (Function.uncurry fun (s : ℝ) (ω : ContinuousPath (Vec d)) =>
        Φ ω * ψ (ω (Real.toNNReal s)))
      ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (laplacianContinuousLaw d x)) :=
    Integrable.of_bound hjoint.aestronglyMeasurable _ (Eventually.of_forall hbound)
  rw [intervalIntegral.integral_of_le T.coe_nonneg, integral_integral_swap hprodint]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [integral_const_mul, timeIntegralPath, intervalIntegral.integral_of_le T.coe_nonneg]

/-- **The square of the time integral as a double time integral**, under each `P_x`. -/
theorem integral_sq_timeIntegralPath (ψ : C₀(Vec d, ℝ)) (T : ℝ≥0) (x : Vec d) :
    (∫ ω, (timeIntegralPath ψ T ω) ^ 2 ∂(laplacianContinuousLaw d x))
      = ∫ s in (0 : ℝ)..(T : ℝ), ∫ r in (0 : ℝ)..(T : ℝ),
          ∫ ω, ψ (ω (Real.toNNReal s)) * ψ (ω (Real.toNNReal r))
            ∂(laplacianContinuousLaw d x) := by
  have hstep1 := intervalIntegral_integral_swap_path_mul ψ T x
    (stronglyMeasurable_timeIntegralPath ψ T) (abs_timeIntegralPath_le ψ T)
  have hsq : (∫ ω, (timeIntegralPath ψ T ω) ^ 2 ∂(laplacianContinuousLaw d x))
      = ∫ ω, timeIntegralPath ψ T ω * timeIntegralPath ψ T ω
        ∂(laplacianContinuousLaw d x) := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    ring
  rw [hsq, ← hstep1]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hstep2 := intervalIntegral_integral_swap_path_mul ψ T x
    (Φ := fun ω : ContinuousPath (Vec d) => ψ (ω (Real.toNNReal s)))
    ((map_continuous ψ).comp_stronglyMeasurable
      (ContinuousPath.measurable_coordinateProcess (Real.toNNReal s)).stronglyMeasurable)
    (fun ω => abs_c0_apply_le ψ _)
  rw [hstep2]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  ring

/-! ## The pair identity -/

theorem toNNReal_sub_toNNReal {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    Real.toNNReal a - Real.toNNReal b = Real.toNNReal (a - b) := by
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_sub (Real.toNNReal_mono hba), Real.coe_toNNReal a (hb.trans hba),
    Real.coe_toNNReal b hb, Real.coe_toNNReal _ (by linarith)]

/-- **The diagonal pair identity.**  `∫ₓ E_x[ψ(B_s)ψ(B_r)] dx = ⟨ψ, P_{|r−s|} ψ⟩`.  It is
`integral_cross_term_eval` with `h = g = ψ`, plus the case split on the order of `r` and `s`. -/
theorem integral_x_pair_eq (ψ : C₀(Vec d, ℝ)) (hψsupp : HasCompactSupport (ψ : Vec d → ℝ))
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫ x, (∫ ω, ψ (ω (Real.toNNReal s)) * ψ (ω (Real.toNNReal r))
        ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫ y, (ψ : Vec d → ℝ) y *
          (brownianSemigroup d) (Real.toNNReal |r - s|) ψ y ∂volume := by
  rcases le_total s r with hsr | hrs
  · have hle : Real.toNNReal s ≤ Real.toNNReal r := Real.toNNReal_mono hsr
    have hpos : (0 : ℝ) < ((Real.toNNReal s : ℝ≥0) : ℝ) := by
      rw [Real.coe_toNNReal s hs.le]; exact hs
    have h := integral_cross_term_eval hle hpos ψ ψ hψsupp
    rw [h, toNNReal_sub_toNNReal hs.le hsr, abs_of_nonneg (by linarith : (0:ℝ) ≤ r - s)]
  · have hle : Real.toNNReal r ≤ Real.toNNReal s := Real.toNNReal_mono hrs
    have hpos : (0 : ℝ) < ((Real.toNNReal r : ℝ≥0) : ℝ) := by
      rw [Real.coe_toNNReal r hr.le]; exact hr
    have hcomm : (∫ x, (∫ ω, ψ (ω (Real.toNNReal s)) * ψ (ω (Real.toNNReal r))
        ∂(laplacianContinuousLaw d x)) ∂volume)
        = ∫ x, (∫ ω, ψ (ω (Real.toNNReal r)) * ψ (ω (Real.toNNReal s))
          ∂(laplacianContinuousLaw d x)) ∂volume := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    rw [hcomm, integral_cross_term_eval hle hpos ψ ψ hψsupp,
      toNNReal_sub_toNNReal hr.le hrs, abs_of_nonpos (by linarith : r - s ≤ 0), neg_sub]

end SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift
