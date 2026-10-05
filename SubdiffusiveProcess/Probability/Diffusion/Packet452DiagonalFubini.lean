module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452Diagonal

@[expose] public section

/-!
# §2's last Fubini, and the diagonal term `Q`

  §2.2/§2.4, closed:

```text
∫ₓ E_x[(∫₀ᵀ ψ(B_r) dr)²] dx = 2 ∫₀ᵀ (T − v) ⟨ψ, P_v ψ⟩ dv.
```

The delicate step is moving `∫ₓ` -- against the **infinite** Lebesgue measure --
inside the time integrals.  Three things make it go through.

* **One swap lemma covers both nestings.**  `integral_integral_swap_x_time` handles
  `∫ₓ ∫₀ᵀ (∫_ω Φ(ω)·ψ(ω t) dP_x) dt dx`, for any bounded strongly measurable `Φ`.  The outer
  nesting is `Φ = Y` (the time integral itself) and the inner one is `Φ = ψ(B_s)`; both are
  instances, so the Fubini work is done once.
* **The dominating function is `(P_t |ψ|)(x)`, and `|ψ| ∈ C₀`** -- not automatic, but immediate for
  a compactly supported `ψ` through `c0OfCompactSupport`, since a continuous compactly supported
  function is zero at infinity (`HasCompactSupport.is_zero_at_infty`).  Its `x`-integral is
  `‖ψ‖₁` at **every** positive time (real invariance), so the product integrability is
  `integrable_prod_iff'` with a *constant* second component.
* **Joint measurability in `(x, t)` of a kernel integral** is Mathlib's
  `StronglyMeasurable.integral_kernel_prod_right'`, applied to
  `Kernel.comap (laplacianContinuousLaw d) Prod.fst`: the kernel depends only on `x`, the
  integrand only on `(t, ω)`, and the lemma does not care.

With that, §2 closes: combined with `semigroup_pairing_nested_ftc` (§2.3) and
`integral_mul_fullLaplacian` (§2.5), `2‖φ‖₂² − 2⟨φ,P_Tφ⟩ + Q = −2T⟨φ,Δφ⟩ = 2T·E(φ)`.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-! ## Preliminaries: probability measures, `|ψ|` in `C₀`, and the semigroup of a `C₀` function -/

instance isProbabilityMeasure_laplacianSemigroup (t : ℝ≥0) (x : Vec d) :
    IsProbabilityMeasure (laplacianSemigroup d t x) := by
  rw [laplacianSemigroup_apply]
  infer_instance

/-- A continuous compactly supported function, as an element of `C₀`. -/
def c0OfCompactSupport {f : Vec d → ℝ} (hf : Continuous f) (hsupp : HasCompactSupport f) :
    C₀(Vec d, ℝ) where
  toFun := f
  continuous_toFun := hf
  zero_at_infty' := hsupp.is_zero_at_infty

@[simp] theorem c0OfCompactSupport_apply {f : Vec d → ℝ} (hf : Continuous f)
    (hsupp : HasCompactSupport f) (x : Vec d) : c0OfCompactSupport hf hsupp x = f x := rfl

/-- `|ψ|` as an element of `C₀`, for compactly supported `ψ`. -/
def absC0 (ψ : C₀(Vec d, ℝ)) (hsupp : HasCompactSupport (ψ : Vec d → ℝ)) : C₀(Vec d, ℝ) :=
  c0OfCompactSupport (map_continuous ψ).abs (hsupp.comp_left (g := abs) abs_zero)

@[simp] theorem absC0_apply (ψ : C₀(Vec d, ℝ)) (hsupp : HasCompactSupport (ψ : Vec d → ℝ))
    (x : Vec d) : absC0 ψ hsupp x = |ψ x| := rfl

theorem absC0_nonneg (ψ : C₀(Vec d, ℝ)) (hsupp : HasCompactSupport (ψ : Vec d → ℝ)) (x : Vec d) :
    0 ≤ absC0 ψ hsupp x := abs_nonneg _

theorem hasCompactSupport_absC0 (ψ : C₀(Vec d, ℝ))
    (hsupp : HasCompactSupport (ψ : Vec d → ℝ)) :
    HasCompactSupport (absC0 ψ hsupp : Vec d → ℝ) :=
  hsupp.comp_left (g := abs) abs_zero

/-- A `C₀` function is integrable under every transition measure. -/
theorem integrable_c0_semigroup (t : ℝ≥0) (x : Vec d) (u : C₀(Vec d, ℝ)) :
    Integrable (u : Vec d → ℝ) (laplacianSemigroup d t x) :=
  Integrable.of_bound (map_continuous u).aestronglyMeasurable ‖u‖
    (Eventually.of_forall fun z => SubMarkovKernelSemigroup.norm_c0_apply_le u z)

theorem semigroup_apply_nonneg {t : ℝ≥0} (u : C₀(Vec d, ℝ)) (hu : ∀ z, 0 ≤ u z) (x : Vec d) :
    0 ≤ (brownianSemigroup d) t u x :=
  integral_nonneg fun z => hu z

/-- **`x ↦ (P_t u)(x)` is integrable** for a nonnegative integrable `u ∈ C₀` and `t > 0`.  The
finiteness is the `ℝ≥0∞` invariance of Lebesgue measure. -/
theorem integrable_semigroup_apply {t : ℝ} (ht : 0 < t) (u : C₀(Vec d, ℝ))
    (hunn : ∀ z, 0 ≤ u z) (huint : Integrable (u : Vec d → ℝ)) :
    Integrable (fun x => (brownianSemigroup d) (Real.toNNReal t) u x) volume := by
  refine ⟨(map_continuous ((brownianSemigroup d) (Real.toNNReal t) u)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun x => semigroup_apply_nonneg u hunn x)]
  have hrw : ∀ x : Vec d, ENNReal.ofReal ((brownianSemigroup d) (Real.toNNReal t) u x)
      = ∫⁻ z, ENNReal.ofReal (u z) ∂(laplacianSemigroup d (Real.toNNReal t) x) := by
    intro x
    exact ofReal_integral_eq_lintegral_ofReal
      (integrable_c0_semigroup (Real.toNNReal t) x u)
      (Eventually.of_forall fun z => hunn z)
  simp only [hrw]
  rw [lintegral_laplacianSemigroup_invariant ht (map_continuous u).measurable.ennreal_ofReal]
  rw [← hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => hunn z)]
  exact huint.2

/-- The `x`-integral of `(P_t u)(x)` is `∫ u`, at every positive time. -/
theorem integral_semigroup_apply_eq {t : ℝ} (ht : 0 < t) (u : C₀(Vec d, ℝ))
    (huint : Integrable (u : Vec d → ℝ)) :
    (∫ x, (brownianSemigroup d) (Real.toNNReal t) u x ∂volume) = ∫ z, (u : Vec d → ℝ) z ∂volume :=
  integral_semigroup_invariant ht (map_continuous u).measurable huint

/-! ## The Fubini swap in `x` and one time variable -/

/-- The path kernel read as a kernel from `Vec d × ℝ`, forgetting the time coordinate. -/
def pathKernelProd (d : ℕ) : Kernel (Vec d × ℝ) (ContinuousPath (Vec d)) :=
  Kernel.comap (laplacianContinuousLaw d) Prod.fst measurable_fst

instance isMarkovKernel_pathKernelProd : IsMarkovKernel (pathKernelProd d) :=
  Kernel.IsMarkovKernel.comap (laplacianContinuousLaw d) measurable_fst

/-- **Fubini in `x` and one time variable.**  Both nestings of §2.2 are instances: the outer with
`Φ = Y`, the inner with `Φ = ψ(B_s)`. -/
theorem integral_integral_swap_x_time (T : ℝ≥0) {Φ : ContinuousPath (Vec d) → ℝ}
    (hΦ : StronglyMeasurable Φ) {CΦ : ℝ} (hΦb : ∀ ω, |Φ ω| ≤ CΦ)
    (ψ : C₀(Vec d, ℝ)) (hψsupp : HasCompactSupport (ψ : Vec d → ℝ)) :
    (∫ x, (∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, Φ ω * ψ (ω (Real.toNNReal t)) ∂(laplacianContinuousLaw d x)) ∂volume)
      = ∫ t in (0 : ℝ)..(T : ℝ),
          ∫ x, (∫ ω, Φ ω * ψ (ω (Real.toNNReal t)) ∂(laplacianContinuousLaw d x)) ∂volume := by
  classical
  have hCΦ : 0 ≤ CΦ := le_trans (abs_nonneg _) (hΦb default)
  set u : C₀(Vec d, ℝ) := absC0 ψ hψsupp with hu
  have huint : Integrable (u : Vec d → ℝ) :=
    (map_continuous u).integrable_of_hasCompactSupport (hasCompactSupport_absC0 ψ hψsupp)
  set A : ℝ → Vec d → ℝ := fun t x =>
    ∫ ω, Φ ω * ψ (ω (Real.toNNReal t)) ∂(laplacianContinuousLaw d x) with hA
  -- joint measurability of `A`
  have hjoint : StronglyMeasurable fun q : (Vec d × ℝ) × ContinuousPath (Vec d) =>
      Φ q.2 * ψ (q.2 (Real.toNNReal q.1.2)) := by
    refine (hΦ.comp_measurable measurable_snd).mul ?_
    exact ((map_continuous ψ).comp
      ((ContinuousEval.continuous_eval.comp continuous_swap).comp
        (((continuous_real_toNNReal.comp continuous_snd).comp continuous_fst).prodMk
          continuous_snd))).stronglyMeasurable
  have hAmeas : StronglyMeasurable fun p : Vec d × ℝ => A p.2 p.1 :=
    StronglyMeasurable.integral_kernel_prod_right' (κ := pathKernelProd d) hjoint
  -- the bound
  have hAbound : ∀ (t : ℝ) (x : Vec d),
      ‖A t x‖ ≤ CΦ * (brownianSemigroup d) (Real.toNNReal t) u x := by
    intro t x
    have hle : ‖A t x‖ ≤ ∫ ω, CΦ * |ψ (ω (Real.toNNReal t))|
        ∂(laplacianContinuousLaw d x) := by
      refine le_trans (norm_integral_le_integral_norm _) ?_
      refine integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _) ?_
        (Eventually.of_forall fun ω => ?_)
      · exact (integrable_eval_of_bound (t := Real.toNNReal t)
          (h := fun y : Vec d => |ψ y|) (map_continuous ψ).measurable.abs (fun y => by
            simpa [abs_abs] using abs_c0_apply_le ψ y) x).const_mul CΦ
      · simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hΦb ω) (abs_nonneg _)
    rw [integral_const_mul] at hle
    refine hle.trans_eq ?_
    congr 1
    exact integral_c0_eval (Real.toNNReal t) u x
  -- the dominating function is integrable on the product
  have hdomint : Integrable (fun p : Vec d × ℝ =>
      CΦ * (brownianSemigroup d) (Real.toNNReal p.2) u p.1)
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) := by
    have hdomcont : Continuous fun p : Vec d × ℝ =>
        (brownianSemigroup d) (Real.toNNReal p.2) u p.1 := by
      have h1 : Continuous fun t : ℝ => ((brownianSemigroup d) (Real.toNNReal t) u).toBCF :=
        ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp
          ((Semigroup.StronglyContinuousContractionSemigroup.continuous_operator_apply
            (brownianSemigroup d) continuous_id continuous_const).comp continuous_real_toNNReal)
      exact ContinuousEval.continuous_eval.comp
        ((h1.comp continuous_snd).prodMk continuous_fst)
    refine (integrable_prod_iff' (hdomcont.aestronglyMeasurable.const_mul CΦ)).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (integrable_semigroup_apply ht.1 u (absC0_nonneg ψ hψsupp) huint).const_mul CΦ
    · refine Integrable.congr (integrable_const (CΦ * ∫ z, (u : Vec d → ℝ) z ∂volume)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hrw : ∀ x : Vec d, ‖CΦ * (brownianSemigroup d) (Real.toNNReal t) u x‖
          = CΦ * (brownianSemigroup d) (Real.toNNReal t) u x := by
        intro x
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hCΦ,
          abs_of_nonneg (semigroup_apply_nonneg u (absC0_nonneg ψ hψsupp) x)]
      simp only [hrw]
      rw [integral_const_mul, integral_semigroup_apply_eq ht.1 u huint]
  -- integrability of `A` itself
  have hAint : Integrable (Function.uncurry fun (x : Vec d) (t : ℝ) => A t x)
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) := by
    refine Integrable.mono' hdomint ?_ (Eventually.of_forall fun p => ?_)
    · exact (hAmeas.comp_measurable
        (measurable_fst.prodMk measurable_snd)).aestronglyMeasurable
    · exact hAbound p.2 p.1
  -- the swap
  have hL : (∫ x, (∫ t in (0 : ℝ)..(T : ℝ), A t x) ∂volume)
      = ∫ x, ∫ t, A t x ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) ∂volume :=
    integral_congr_ae (Eventually.of_forall fun x =>
      intervalIntegral.integral_of_le T.coe_nonneg)
  rw [hL, integral_integral_swap hAint, intervalIntegral.integral_of_le T.coe_nonneg]

/-! ## The diagonal term -/

/-- **§2.2/§2.4's diagonal term `Q`**, closed:

```text
∫ₓ E_x[(∫₀ᵀ ψ(B_r) dr)²] dx = 2 ∫₀ᵀ (T − v) ⟨ψ, P_v ψ⟩ dv
```

-- exactly twice the triangle integral of §2.3, which is what makes the final cancellation
exact. -/
theorem integral_x_sq_timeIntegralPath (ψ : C₀(Vec d, ℝ))
    (hψsupp : HasCompactSupport (ψ : Vec d → ℝ)) (T : ℝ≥0) :
    (∫ x, (∫ ω, (timeIntegralPath ψ T ω) ^ 2 ∂(laplacianContinuousLaw d x)) ∂volume)
      = 2 * ∫ v in (0 : ℝ)..(T : ℝ), ((T : ℝ) - v) *
          ∫ y, (ψ : Vec d → ℝ) y * (brownianSemigroup d) (Real.toNNReal v) ψ y ∂volume := by
  classical
  have hψint : Integrable (ψ : Vec d → ℝ) :=
    (map_continuous ψ).integrable_of_hasCompactSupport hψsupp
  set K : ℝ → ℝ := fun v =>
    ∫ y, (ψ : Vec d → ℝ) y * (brownianSemigroup d) (Real.toNNReal v) ψ y ∂volume with hK
  have hKcont : Continuous K := continuous_semigroup_pairing_real hψint ψ
  -- expand the square, one factor at a time
  have ha : ∀ x : Vec d, (∫ ω, (timeIntegralPath ψ T ω) ^ 2 ∂(laplacianContinuousLaw d x))
      = ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, timeIntegralPath ψ T ω * ψ (ω (Real.toNNReal t))
          ∂(laplacianContinuousLaw d x) := by
    intro x
    rw [intervalIntegral_integral_swap_path_mul ψ T x
      (stronglyMeasurable_timeIntegralPath ψ T) (abs_timeIntegralPath_le ψ T)]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  simp only [ha]
  rw [integral_integral_swap_x_time T (stronglyMeasurable_timeIntegralPath ψ T)
    (abs_timeIntegralPath_le ψ T) ψ hψsupp, ← integral_integral_abs_sub hKcont T.coe_nonneg]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hsmem => ?_)
  rw [Set.uIoc_of_le T.coe_nonneg] at hsmem
  have hΦs : StronglyMeasurable fun ω : ContinuousPath (Vec d) => ψ (ω (Real.toNNReal s)) :=
    (map_continuous ψ).comp_stronglyMeasurable
      (ContinuousPath.measurable_coordinateProcess (Real.toNNReal s)).stronglyMeasurable
  have hΦsb : ∀ ω : ContinuousPath (Vec d), |ψ (ω (Real.toNNReal s))| ≤ ‖ψ‖ :=
    fun ω => abs_c0_apply_le ψ _
  have hc : ∀ x : Vec d, (∫ ω, timeIntegralPath ψ T ω * ψ (ω (Real.toNNReal s))
        ∂(laplacianContinuousLaw d x))
      = ∫ r in (0 : ℝ)..(T : ℝ), ∫ ω, ψ (ω (Real.toNNReal s)) * ψ (ω (Real.toNNReal r))
          ∂(laplacianContinuousLaw d x) := by
    intro x
    rw [intervalIntegral_integral_swap_path_mul ψ T x hΦs hΦsb]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  simp only [hc]
  rw [integral_integral_swap_x_time T hΦs hΦsb ψ hψsupp]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hrmem => ?_)
  rw [Set.uIoc_of_le T.coe_nonneg] at hrmem
  rw [integral_x_pair_eq ψ hψsupp hrmem.1 hsmem.1, hK]

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
