import SubdiffusiveProcess.Probability.Diffusion.Packet452Convolution




set_option autoImplicit false

open Function Homogenization MeasureTheory Filter Set Topology

open scoped ENNReal Convolution Pointwise

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}




/-- For `C²` functions the diagonal of the second iterated Fréchet derivative is the iterated
directional derivative. -/
theorem iteratedFDeriv_two_eq {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (x v : Vec d) :
    iteratedFDeriv ℝ 2 f x ![v, v] = fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (by norm_num)).differentiable le_rfl) x
  have hcalc : fderiv ℝ (fun y => fderiv ℝ f y v) x = (fderiv ℝ (fderiv ℝ f) x).flip v := by
    have h := fderiv_clm_apply (𝕜 := ℝ) (c := fun y => fderiv ℝ f y) (u := fun _ : Vec d => v)
      hfd (differentiableAt_const v)
    simpa using h
  rw [iteratedFDeriv_two_apply, hcalc]
  simp [ContinuousLinearMap.flip_apply]

/-! ## Support localisation -/

/-- Re-derivation of the `private` support bound of `GlobalMollifierLp.lean`. -/
theorem tsupport_scaledConvexApproxKernel_subset {ρ : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) {a : ℝ} (ha : 0 < a) :
    tsupport (scaledConvexApproxKernel ρ a) ⊆ Metric.closedBall (0 : Vec d) a := by
  apply closure_minimal
  · intro t ht
    have hρ_ne : ρ (a⁻¹ • t) ≠ 0 := by
      intro hzero
      apply ht
      simp only [scaledConvexApproxKernel, hzero, mul_zero]
    have hρ_ball : a⁻¹ • t ∈ Metric.closedBall (0 : Vec d) 1 :=
      hρ.support_subset_closedBall (subset_tsupport ρ hρ_ne)
    rw [Metric.mem_closedBall, dist_zero_right] at hρ_ball ⊢
    calc
      ‖t‖ = a * (a⁻¹ * ‖t‖) := by field_simp
      _ = a * ‖a⁻¹ • t‖ := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ a * 1 := mul_le_mul_of_nonneg_left hρ_ball ha.le
      _ = a := mul_one _
  · exact Metric.isClosed_closedBall

/-- The reflected kernel `z ↦ k (x − z)` lives in the closed ball about `x`. -/
theorem tsupport_reflect_subset {k : Vec d → ℝ} {a : ℝ}
    (hk : tsupport k ⊆ Metric.closedBall (0 : Vec d) a) (x : Vec d) :
    tsupport (fun z : Vec d => k (x - z)) ⊆ Metric.closedBall x a := by
  have he : (fun z : Vec d => k (x - z)) = k ∘ (Homeomorph.subLeft x) := rfl
  rw [he, tsupport, Function.support_comp_eq_preimage,
    ← (Homeomorph.subLeft x).preimage_closure]
  intro z hz
  have hz' : x - z ∈ tsupport k := hz
  have h2 := hk hz'
  rw [Metric.mem_closedBall, dist_zero_right] at h2
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc ‖z - x‖ = ‖-(x - z)‖ := by rw [neg_sub]
    _ = ‖x - z‖ := norm_neg _
    _ ≤ a := h2

/-! ## The concrete family -/

/-- The `n`-th mollifier: the unit convex approximation kernel at scale `1/(n+1)`. -/
def mollKernel (d : ℕ) (n : ℕ) : Vec d → ℝ :=
  scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) (unitConvexApproxScale n)

theorem unitConvexApproxScale_pos (n : ℕ) : 0 < unitConvexApproxScale n := by
  rw [unitConvexApproxScale]
  positivity

theorem mollKernel_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (mollKernel d n) :=
  contDiff_scaledConvexApproxKernel isConvexApproxKernel_unitConvexApproxKernel _

theorem mollKernel_hasCompactSupport (n : ℕ) : HasCompactSupport (mollKernel d n) :=
  hasCompactSupport_scaledConvexApproxKernel
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)).compactSupport
    (unitConvexApproxScale_pos n)

theorem tsupport_mollKernel (n : ℕ) :
    tsupport (mollKernel d n) ⊆ Metric.closedBall (0 : Vec d) (unitConvexApproxScale n) :=
  tsupport_scaledConvexApproxKernel_subset isConvexApproxKernel_unitConvexApproxKernel
    (unitConvexApproxScale_pos n)

theorem tendsto_unitConvexApproxScale : Tendsto unitConvexApproxScale atTop (𝓝 0) :=
  tendsto_unitConvexApproxScale_zero

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
