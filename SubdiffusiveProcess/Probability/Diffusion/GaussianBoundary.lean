import SubdiffusiveProcess.Probability.Diffusion.GaussianKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Gaussian decay between the boundary and an interior point

The product Gaussian has an explicit scalar prefactor and exponential in the
sum of squared coordinate distances. At any fixed positive separation, its
upper envelope tends to zero as the remaining time tends to zero.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The explicit variance-`2t` product Gaussian formula. -/
theorem laplacianDensity_eq (t : ℝ) (ht : 0 < t) (x y : Vec d) :
    laplacianDensity t x y = (Real.sqrt (4 * Real.pi * t))⁻¹ ^ d *
      Real.exp (-(∑ i, (y i - x i) ^ 2) / (4 * t)) := by
  unfold laplacianDensity gaussianPDFReal
  simp only [NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal _ ht.le]
  have hscale : 2 * Real.pi * (2 * t) = 4 * Real.pi * t := by ring
  have hvar : 2 * (2 * t) = 4 * t := by ring
  rw [hscale]
  simp_rw [hvar]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_fin]
  rw [← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

/-- The Gaussian is bounded by its explicit envelope whenever squared
coordinate separation is at least `a`. -/
theorem laplacianDensity_le_of_sq_separation {t a : ℝ} (ht : 0 < t)
    (x y : Vec d) (hsep : a ≤ ∑ i, (y i - x i) ^ 2) :
    laplacianDensity t x y ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ ^ d *
      Real.exp (-a / (4 * t)) := by
  rw [laplacianDensity_eq t ht x y]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (neg_le_neg hsep) (by positivity)

/-- Factoring the Gaussian prefactor exposes the inverse-time power. -/
theorem gaussian_prefactor_eq {r : ℝ} (hr : 0 < r) :
    (Real.sqrt (4 * Real.pi * r))⁻¹ ^ d =
      (Real.sqrt (4 * Real.pi))⁻¹ ^ d * (r⁻¹) ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi), mul_inv_rev, mul_pow, mul_comm]
  congr 1
  rw [← Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity : 0 ≤ r⁻¹)]
  congr 1
  ring

/-- At positive separation the Gaussian factor dominates the entire
singular inverse-time prefactor; the upper bound tends to zero. -/
theorem tendsto_gaussian_boundary_envelope_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun r : ℝ => (Real.sqrt (4 * Real.pi * r))⁻¹ ^ d *
      Real.exp (-a / (4 * r))) (𝓝[>] 0) (𝓝 0) := by
  have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((d : ℝ) / 2) (a / 4) (by positivity)).comp tendsto_inv_nhdsGT_zero
  have h := hbase.const_mul ((Real.sqrt (4 * Real.pi))⁻¹ ^ d)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [gaussian_prefactor_eq hr]
  dsimp only [Function.comp_def]
  have he : -(a / 4) * r⁻¹ = -a / (4 * r) := by ring
  simp only [he, mul_assoc]

end SubdiffusiveProcess.Probability.Diffusion
