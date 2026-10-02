import SubdiffusiveProcess.Probability.Diffusion.GaussianBoundary

/-!
# A continuous and bounded boundary Gaussian envelope

The envelope extends by zero at nonpositive remaining times. Its continuity
at zero records explicitly that a fixed positive spatial separation removes
the singular Gaussian prefactor.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The separated Gaussian bound, extended by zero at nonpositive times. -/
def boundaryGaussianEnvelope (d : ℕ) (a r : ℝ) : ℝ :=
  if 0 < r then (Real.sqrt (4 * Real.pi * r))⁻¹ ^ d * Real.exp (-a / (4 * r)) else 0

theorem boundaryGaussianEnvelope_nonneg (d : ℕ) (a r : ℝ) :
    0 ≤ boundaryGaussianEnvelope d a r := by
  unfold boundaryGaussianEnvelope
  split_ifs <;> positivity

@[simp]
theorem boundaryGaussianEnvelope_zero (d : ℕ) (a : ℝ) :
    boundaryGaussianEnvelope d a 0 = 0 := by
  simp only [boundaryGaussianEnvelope, lt_self_iff_false, if_false]

/-- The zero extension is continuous, including where the remaining time vanishes. -/
theorem continuous_boundaryGaussianEnvelope {a : ℝ} (ha : 0 < a) :
    Continuous (boundaryGaussianEnvelope d a) := by
  rw [continuous_iff_continuousAt]
  intro r
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · change Tendsto (boundaryGaussianEnvelope d a) (𝓝 r)
      (𝓝 (boundaryGaussianEnvelope d a r))
    rw [boundaryGaussianEnvelope, if_neg (not_lt_of_ge hr.le)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_nhds hr] with s hs
    simp only [boundaryGaussianEnvelope, not_lt_of_ge hs.le, if_false]
  · rw [continuousAt_iff_continuous_left'_right']
    constructor
    · change Tendsto (boundaryGaussianEnvelope d a) (𝓝[<] 0)
        (𝓝 (boundaryGaussianEnvelope d a 0))
      rw [boundaryGaussianEnvelope_zero]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      change s < 0 at hs
      simp only [boundaryGaussianEnvelope, not_lt_of_ge hs.le, if_false]
    · change Tendsto (boundaryGaussianEnvelope d a) (𝓝[>] 0)
        (𝓝 (boundaryGaussianEnvelope d a 0))
      rw [boundaryGaussianEnvelope_zero]
      refine (tendsto_gaussian_boundary_envelope_zero (d := d) ha).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (if_pos hs).symm
  · change Tendsto (boundaryGaussianEnvelope d a) (𝓝 r)
      (𝓝 (boundaryGaussianEnvelope d a r))
    rw [boundaryGaussianEnvelope, if_pos hr]
    have hc : ContinuousAt (fun s : ℝ =>
        (Real.sqrt (4 * Real.pi * s))⁻¹ ^ d * Real.exp (-a / (4 * s))) r := by
      fun_prop (disch := positivity)
    refine hc.tendsto.congr' ?_
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact (if_pos hs).symm

/-- On any finite horizon, the separated Gaussian bound has a finite uniform
constant. Its only parameters are dimension, squared separation, and horizon. -/
theorem exists_bound_boundaryGaussianEnvelope {a : ℝ} (ha : 0 < a) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc 0 T, boundaryGaussianEnvelope d a r ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (continuous_boundaryGaussianEnvelope (d := d) ha).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun r hr => ?_⟩
  exact (hC ⟨r, hr, rfl⟩).trans (le_max_left _ _)

/-- The square of the product-norm distance is bounded by the sum of squared
coordinate distances, in every finite dimension. -/
theorem sq_dist_le_sum_coord (x y : Vec d) :
    dist x y ^ 2 ≤ ∑ i, (x i - y i) ^ 2 := by
  have hsum : 0 ≤ ∑ i, (x i - y i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hn : ‖x - y‖ ≤ Real.sqrt (∑ i, (x i - y i) ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    change |x i - y i| ≤ Real.sqrt (∑ i, (x i - y i) ^ 2)
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (x j - y j))
      (Finset.mem_univ i))
  rw [dist_eq_norm]
  calc
    _ ≤ (Real.sqrt (∑ i, (x i - y i) ^ 2)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hn
    _ = _ := Real.sq_sqrt hsum

/-- A ball contained in the domain gives a uniform positive squared separation
between a smaller interior ball and every point outside the domain. -/
theorem sq_separation_of_ball_subset {U : Set (Vec d)} {y₀ y z : Vec d} {δ : ℝ}
    (hδ : 0 < δ) (hball : Metric.ball y₀ (2 * δ) ⊆ U)
    (hy : y ∈ Metric.ball y₀ δ) (hz : z ∉ U) :
    δ ^ 2 ≤ ∑ i, (y i - z i) ^ 2 := by
  have hzdist : 2 * δ ≤ dist z y₀ := by
    exact le_of_not_gt (fun h => hz (hball h))
  have hyz : δ ≤ dist y z := by
    have htri := dist_triangle z y y₀
    rw [dist_comm z y] at htri
    exact le_of_lt (by linarith [Metric.mem_ball.mp hy])
  exact ((sq_le_sq₀ hδ.le dist_nonneg).2 hyz).trans (sq_dist_le_sum_coord y z)

end SubdiffusiveProcess.Probability.Diffusion
