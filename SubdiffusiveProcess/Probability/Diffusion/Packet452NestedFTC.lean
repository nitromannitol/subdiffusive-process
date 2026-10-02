import SubdiffusiveProcess.Probability.Diffusion.Packet452SemigroupFTC
import SubdiffusiveProcess.Probability.Diffusion.Packet452SymmetryReal




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-- The `C₀` semigroup evaluated at a point is the kernel integral. -/
theorem brownianSemigroup_apply_apply (t : NNReal) (u : C₀(Vec d, ℝ)) (x : Vec d) :
    (brownianSemigroup d) t u x = ∫ y, u y ∂(laplacianSemigroup d t x) := rfl

/-- **Self-adjointness at every real time.**  For `t ≤ 0` the kernel is the identity and the
identity is `mul_comm` under the integral. -/
theorem integral_semigroup_symm_toNNReal {t : ℝ} {w g : Vec d → ℝ} {C : ℝ}
    (hwm : Measurable w) (hw : Integrable w) (hgm : Measurable g) (hgb : ∀ y, |g y| ≤ C) :
    (∫ x, w x * (∫ y, g y ∂(laplacianSemigroup d (Real.toNNReal t) x)) ∂volume)
      = ∫ y, g y * (∫ x, w x ∂(laplacianSemigroup d (Real.toNNReal t) y)) ∂volume := by
  rcases lt_or_ge 0 t with ht | ht
  · exact integral_semigroup_symm ht hwm hw hgm hgb
  · have h0 : Real.toNNReal t = 0 := by
      simp [Real.toNNReal_eq_zero, ht]
    have hker : ∀ x : Vec d, (laplacianSemigroup d (Real.toNNReal t)) x = Measure.dirac x := by
      intro x
      rw [h0]
      show ((laplacianSemigroup d).kernel 0) x = Measure.dirac x
      rw [(laplacianSemigroup d).kernel_zero, Kernel.id_apply]
    simp only [hker, integral_dirac' _ _ hgm.stronglyMeasurable,
      integral_dirac' _ _ hwm.stronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-! ## The triangle swap -/

/-- **The triangle swap**, by integration by parts against `t ↦ t − T`: both boundary terms
vanish, and the `(T − v)` weight is the surviving factor. -/
theorem integral_integral_triangle {K : ℝ → ℝ} (hK : Continuous K) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ∫ v in (0 : ℝ)..t, K v) = ∫ v in (0 : ℝ)..T, (T - v) * K v := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ∫ v in (0 : ℝ)..s, K v) (K t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hK.intervalIntegrable 0 t)
      hK.aestronglyMeasurable.stronglyMeasurableAtFilter hK.continuousAt
  have hucont : Continuous fun s : ℝ => ∫ v in (0 : ℝ)..s, K v :=
    continuous_iff_continuousAt.2 fun t => (hderiv t).continuousAt
  have hv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s - T) 1 t := fun t => by
    simpa using (hasDerivAt_id t).sub_const T
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun s : ℝ => ∫ v in (0 : ℝ)..s, K v) (u' := K) (v := fun s : ℝ => s - T)
    (v' := fun _ : ℝ => (1 : ℝ)) (a := 0) (b := T)
    hucont.continuousOn (by fun_prop) (fun x _ => hderiv x) (fun x _ => hv x)
    (hK.intervalIntegrable 0 T) intervalIntegrable_const
  simp only [mul_one, sub_self, mul_zero, intervalIntegral.integral_same, zero_mul,
    zero_sub] at hparts
  rw [hparts, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun v _ => ?_
  ring

/-! ## The closed form -/

/-- **The nested-FTC closed form of §2.3.**  `f` is the test function `φ`, `g` its full
Laplacian. -/
theorem semigroup_pairing_nested_ftc (f g : C₀(Vec d, ℝ))
    (hf2 : ContDiff ℝ 2 (f : Vec d → ℝ)) (hfsupp : HasCompactSupport (f : Vec d → ℝ))
    (hgsupp : HasCompactSupport (g : Vec d → ℝ))
    (hgdef : ∀ x, g x = ∑ i, iteratedFDeriv ℝ 2 (f : Vec d → ℝ) x
      ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)])
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ x, (f : Vec d → ℝ) x * (brownianSemigroup d) (Real.toNNReal T) f x)
      = (∫ x, (f : Vec d → ℝ) x ^ 2)
        + T * (∫ x, (f : Vec d → ℝ) x * (g : Vec d → ℝ) x)
        + ∫ v in (0 : ℝ)..T, (T - v) *
            ∫ x, (g : Vec d → ℝ) x * (brownianSemigroup d) (Real.toNNReal v) g x := by
  have hfint : Integrable (f : Vec d → ℝ) :=
    (map_continuous f).integrable_of_hasCompactSupport hfsupp
  have hgint : Integrable (g : Vec d → ℝ) :=
    (map_continuous g).integrable_of_hasCompactSupport hgsupp
  have hfm : Measurable (f : Vec d → ℝ) := (map_continuous f).measurable
  have hgm : Measurable (g : Vec d → ℝ) := (map_continuous g).measurable
  set K : ℝ → ℝ :=
    fun v => ∫ x, (g : Vec d → ℝ) x * (brownianSemigroup d) (Real.toNNReal v) g x with hKdef
  have hKcont : Continuous K := continuous_semigroup_pairing_real hgint g
  have hprimcont : Continuous fun t : ℝ => ∫ v in (0 : ℝ)..t, K v :=
    continuous_iff_continuousAt.2 fun t =>
      (intervalIntegral.integral_hasDerivAt_right (hKcont.intervalIntegrable 0 t)
        hKcont.aestronglyMeasurable.stronglyMeasurableAtFilter hKcont.continuousAt).continuousAt
  -- the two applications of the pairing FTC
  have hftc1 := integral_pairing_laplacian_eq_sub hfint f g hf2 hfsupp hgdef hT
  have hftc2 : ∀ t : ℝ, 0 ≤ t →
      (∫ v in (0 : ℝ)..t, K v)
        = (∫ x, (g : Vec d → ℝ) x * (brownianSemigroup d) (Real.toNNReal t) f x)
          - ∫ x, (g : Vec d → ℝ) x * (f : Vec d → ℝ) x := fun t ht =>
    integral_pairing_laplacian_eq_sub hgint f g hf2 hfsupp hgdef ht
  -- self-adjointness turns the first integrand into the second pairing
  have hsymm : ∀ t : ℝ,
      (∫ x, (f : Vec d → ℝ) x * (brownianSemigroup d) (Real.toNNReal t) g x)
        = ∫ x, (g : Vec d → ℝ) x * (brownianSemigroup d) (Real.toNNReal t) f x := fun t =>
    integral_semigroup_symm_toNNReal hfm hfint hgm (fun y => abs_c0_apply_le g y)
  -- rewrite the first FTC's integrand
  have hint : (∫ t in (0 : ℝ)..T,
        ∫ x, (f : Vec d → ℝ) x * (brownianSemigroup d) (Real.toNNReal t) g x)
      = T * (∫ x, (g : Vec d → ℝ) x * (f : Vec d → ℝ) x)
        + ∫ t in (0 : ℝ)..T, ∫ v in (0 : ℝ)..t, K v := by
    have hcongr : ∀ t ∈ uIcc (0 : ℝ) T,
        (∫ x, (f : Vec d → ℝ) x * (brownianSemigroup d) (Real.toNNReal t) g x)
          = (∫ x, (g : Vec d → ℝ) x * (f : Vec d → ℝ) x) + ∫ v in (0 : ℝ)..t, K v := by
      intro t htmem
      rw [uIcc_of_le hT] at htmem
      rw [hsymm t, hftc2 t htmem.1]
      ring
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_add intervalIntegrable_const
        (hprimcont.intervalIntegrable 0 T), intervalIntegral.integral_const]
    simp
  -- combine
  rw [hint, integral_integral_triangle hKcont T] at hftc1
  have hsq : (∫ x, (f : Vec d → ℝ) x * (f : Vec d → ℝ) x) = ∫ x, (f : Vec d → ℝ) x ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  have hcomm : (∫ x, (g : Vec d → ℝ) x * (f : Vec d → ℝ) x)
      = ∫ x, (f : Vec d → ℝ) x * (g : Vec d → ℝ) x :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [hsq, hcomm] at hftc1
  linarith [hftc1]

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
