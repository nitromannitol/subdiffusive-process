import SubdiffusiveProcess.Probability.Diffusion.LaplacianGenerator




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
