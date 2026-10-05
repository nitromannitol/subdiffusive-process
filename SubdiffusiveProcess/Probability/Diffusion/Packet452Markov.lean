module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452InvarianceReal
public import SubdiffusiveProcess.Probability.Diffusion.LaplacianGenerator
public import SubdiffusiveProcess.Probability.Diffusion.HuntIdentity
public import MarkovProcess.Main

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-- The path average of a `C₀` observable at a single time is the semigroup average. -/
theorem integral_c0_eval (t : ℝ≥0) (g : C₀(Vec d, ℝ)) (y : Vec d) :
    (∫ ω, g (ω t) ∂(laplacianContinuousLaw d y)) = ∫ z, g z ∂(laplacianSemigroup d t y) := by
  have heval : Measurable fun w : ContinuousPath (Vec d) => w t :=
    ContinuousPath.measurable_coordinateProcess t
  rw [← laplacianContinuousLaw_map_eval t, Kernel.map_apply _ heval,
    integral_map heval.aemeasurable (map_continuous g).aestronglyMeasurable]

/-- A bounded measurable observable of the path at a single time is integrable under the law. -/
theorem integrable_eval_of_bound {t : ℝ≥0} {h : Vec d → ℝ} (hhm : Measurable h) {C : ℝ}
    (hhb : ∀ y, |h y| ≤ C) (y : Vec d) :
    Integrable (fun ω : ContinuousPath (Vec d) => h (ω t)) (laplacianContinuousLaw d y) :=
  Integrable.of_bound
    (hhm.comp (ContinuousPath.measurable_coordinateProcess t)).aestronglyMeasurable C
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hhb (ω t))

/-- **The time integral along a path may be moved outside the path expectation.**  Fubini on
`Ioc 0 T × ContinuousPath`, with the joint integrand bounded by `‖ψ‖` and jointly continuous --
the same template as `integral_eval_sub_eq_integral_integral_generator`'s Fubini step. -/
theorem intervalIntegral_integral_swap_path (ψ : C₀(Vec d, ℝ)) (T : ℝ≥0) (x : Vec d) :
    (∫ s in (0 : ℝ)..(T : ℝ), ∫ ω, ψ (ω (Real.toNNReal s)) ∂(laplacianContinuousLaw d x))
      = ∫ ω, (∫ s in (0 : ℝ)..(T : ℝ), ψ (ω (Real.toNNReal s)))
          ∂(laplacianContinuousLaw d x) := by
  have hcont : Continuous fun p : ℝ × ContinuousPath (Vec d) => ψ (p.2 (Real.toNNReal p.1)) :=
    (map_continuous ψ).comp
      ((ContinuousEval.continuous_eval.comp continuous_swap).comp
        (continuous_real_toNNReal.fst'.prodMk continuous_snd))
  have hbound : ∀ p : ℝ × ContinuousPath (Vec d), ‖ψ (p.2 (Real.toNNReal p.1))‖ ≤ ‖ψ‖ :=
    fun p => SubMarkovKernelSemigroup.norm_c0_apply_le ψ _
  have hprodint : Integrable
      (Function.uncurry fun (s : ℝ) (ω : ContinuousPath (Vec d)) => ψ (ω (Real.toNNReal s)))
      ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (laplacianContinuousLaw d x)) :=
    Integrable.of_bound hcont.aestronglyMeasurable _ (Eventually.of_forall hbound)
  rw [intervalIntegral.integral_of_le T.coe_nonneg, integral_integral_swap hprodint]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  exact (intervalIntegral.integral_of_le T.coe_nonneg).symm

/-- **The simple Markov property, in the form §2.1 consumes.** -/
theorem integral_markov_split {r T : ℝ≥0} (hrT : r ≤ T) (x : Vec d)
    {h : Vec d → ℝ} (hhm : Measurable h) {Ch : ℝ} (hhb : ∀ y, |h y| ≤ Ch)
    (g : C₀(Vec d, ℝ)) :
    (∫ ω, h (ω r) * g (ω T) ∂(laplacianContinuousLaw d x))
      = ∫ ω, h (ω r) * (∫ z, g z ∂(laplacianSemigroup d (T - r) (ω r)))
          ∂(laplacianContinuousLaw d x) := by
  classical
  set G : ContinuousPath (Vec d) → ℝ := fun η => g (η (T - r)) with hGdef
  have hGsm : StronglyMeasurable G :=
    (map_continuous g).comp_stronglyMeasurable
      (ContinuousPath.measurable_coordinateProcess (T - r)).stronglyMeasurable
  have hGb : ∀ η, ‖G η‖ ≤ ‖g‖ := fun η =>
    SubMarkovKernelSemigroup.norm_c0_apply_le g _
  have hshift : ∀ ω : ContinuousPath (Vec d), G (ContinuousPath.shift r ω) = g (ω T) := by
    intro ω
    rw [hGdef]
    simp only [ContinuousPath.shift_apply]
    rw [add_tsub_cancel_of_le hrT]
  have hce := isFeller_laplacianSemigroup.continuousProcess_condExp_shift
    (laplacianSemigroup d) isConservative_laplacianSemigroup
    kolmogorovRegular_laplacianSemigroup x r G hGsm ‖g‖ hGb
  -- the conditional expectation of `g (ω T)`, read as a semigroup average
  have hce' : (laplacianContinuousLaw d x)[fun ω => g (ω T)|
      ContinuousPath.canonicalFiltration (alpha := Vec d) r]
        =ᵐ[laplacianContinuousLaw d x]
      fun ω => ∫ z, g z ∂(laplacianSemigroup d (T - r) (ω r)) := by
    have hfun : (fun ω : ContinuousPath (Vec d) => G (ContinuousPath.shift r ω))
        = fun ω : ContinuousPath (Vec d) => g (ω T) := funext hshift
    rw [hfun] at hce
    refine hce.trans (Eventually.of_forall fun ω => ?_)
    exact integral_c0_eval (T - r) g (ω r)
  -- pull out the `𝓕_r`-measurable factor
  have hhsm : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := Vec d) r]
      fun ω : ContinuousPath (Vec d) => h (ω r) :=
    (hhm.comp (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
      (alpha := Vec d) r)).stronglyMeasurable
  have hgint : Integrable (fun ω : ContinuousPath (Vec d) => g (ω T))
      (laplacianContinuousLaw d x) :=
    integrable_eval_of_bound (map_continuous g).measurable
      (fun y => by simpa [Real.norm_eq_abs] using SubMarkovKernelSemigroup.norm_c0_apply_le g y) x
  have hprodint : Integrable
      ((fun ω : ContinuousPath (Vec d) => h (ω r)) * fun ω => g (ω T))
      (laplacianContinuousLaw d x) := by
    refine Integrable.of_bound ?_ (Ch * ‖g‖) (Eventually.of_forall fun ω => ?_)
    · exact ((hhm.comp (ContinuousPath.measurable_coordinateProcess r)).mul
        ((map_continuous g).measurable.comp
          (ContinuousPath.measurable_coordinateProcess T))).aestronglyMeasurable
    · simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hhb (ω r))
        (by simpa [Real.norm_eq_abs] using SubMarkovKernelSemigroup.norm_c0_apply_le g (ω T))
        (abs_nonneg _) (le_trans (abs_nonneg _) (hhb (ω r)))
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (m := ContinuousPath.canonicalFiltration (alpha := Vec d) r)
    (μ := laplacianContinuousLaw d x) hhsm hprodint hgint
  -- integrate
  have hleft : (∫ ω, h (ω r) * g (ω T) ∂(laplacianContinuousLaw d x))
      = ∫ ω, ((laplacianContinuousLaw d x)[
          (fun ω : ContinuousPath (Vec d) => h (ω r)) * fun ω => g (ω T)|
          ContinuousPath.canonicalFiltration (alpha := Vec d) r]) ω
        ∂(laplacianContinuousLaw d x) :=
    (integral_condExp ((ContinuousPath.canonicalFiltration (alpha := Vec d)).le r)).symm
  rw [hleft]
  refine integral_congr_ae ?_
  filter_upwards [hpull, hce'] with ω hω hω'
  rw [hω]
  simp only [Pi.mul_apply]
  rw [hω']

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
