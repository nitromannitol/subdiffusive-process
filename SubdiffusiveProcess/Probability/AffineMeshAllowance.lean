import SubdiffusiveProcess.Probability.ExponentialTailMoment
import SubdiffusiveProcess.Probability.MeshEnvelope
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-! Exponential tails on a finite family at each mesh depth give one additive
allowance, with a prescribed linear cost in depth.  Dependence between all
members is unrestricted.  This file does not construct model-specific prefix
allowances or transfer finite-cutoff scores to their limits.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess

/-- Taking logarithms converts an exponential envelope into an additive one. -/
theorem le_affine_of_exp_le
    (x n W t xi : ℝ) (hW : 0 ≤ W) (ht : 0 < t)
    (h : Real.exp (t * x) ≤ W * Real.exp (t * xi * n)) :
    x ≤ xi * n + Real.log (1 + W) / t := by
  have hpos : 0 < 1 + W := add_pos_of_pos_of_nonneg one_pos hW
  have h' : Real.exp (t * x) ≤ Real.exp (Real.log (1 + W) + t * xi * n) := by
    rw [Real.exp_add, Real.exp_log hpos]
    exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
      (Real.exp_pos _).le)
  have hlog := Real.exp_le_exp.mp h'
  have hsub : x - xi * n ≤ Real.log (1 + W) / t :=
    (le_div_iff₀ ht).2 (by nlinarith only [hlog])
  linarith only [hsub]

/-- A mesh with polynomial-times-triadic cardinality and uniform exponential
allowance tails admits one finite random intercept at any admissible slope. -/
theorem exists_affine_mesh_allowance_of_exponential_tails
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (k : ℕ → ℕ) (d b : ℕ) (Ccount Ctail A t xi : ℝ)
    (hCcount : 0 ≤ Ccount) (hCtail : 0 ≤ Ctail)
    (ht : 0 < t) (htA : t < A)
    (hrate : (d : ℝ) * Real.log 3 < t * xi)
    (hcard : ∀ n : ℕ, (k n : ℝ) ≤
      Ccount * ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ ((d : ℝ) * n))
    (B : ∀ n : ℕ, Fin (k n) → Omega → ℕ)
    (hB : ∀ n i, Measurable (B n i))
    (htail : ∀ n i j, mu.real {omega | j < B n i omega} ≤
      Ctail * Real.exp (-A * (j : ℝ))) :
    ∀ᵐ omega ∂mu, ∃ B0 : ℝ, 0 < B0 ∧
      ∀ n i, (B n i omega : ℝ) ≤ xi * (n : ℝ) + B0 := by
  let eta : ℝ := t * xi / Real.log 3
  let Cmom : ℝ := 1 + Ctail * Real.exp t / (1 - Real.exp (t - A))
  let Z : ∀ n : ℕ, Fin (k n) → Omega → ℝ :=
    fun n i omega => Real.exp (t * (B n i omega : ℝ))
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hmom n i : Integrable (Z n i) mu ∧ (∫ omega, Z n i omega ∂mu) ≤ Cmom :=
    integrable_exp_nat_of_exponential_tail mu (B n i) (hB n i)
      Ctail A t hCtail ht.le htA (htail n i)
  have hnorm n i : eLpNorm (Z n i) 1 mu ≤ ENNReal.ofReal Cmom := by
    dsimp only [Z]
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp_rw [Real.enorm_of_nonneg (Real.exp_pos _).le]
    rw [← ofReal_integral_eq_lintegral_ofReal (hmom n i).1
      (ae_of_all mu (fun omega => (Real.exp_pos _).le))]
    exact ENNReal.ofReal_le_ofReal (hmom n i).2
  have hgap : (d : ℝ) < (1 : ℝ≥0∞).toReal * eta := by
    rw [ENNReal.toReal_one, one_mul]
    exact (lt_div_iff₀ hlog3).2 hrate
  obtain ⟨W, _, hW, _⟩ := exists_triadic_mesh_envelope mu k d b Ccount eta
    hCcount (p := 1) (q := 1) le_rfl le_rfl ENNReal.one_ne_top hgap hcard Z
    (fun n i => (hmom n i).1.aestronglyMeasurable)
    (ENNReal.ofReal Cmom) ENNReal.ofReal_ne_top hnorm
  filter_upwards [hW] with omega homega
  have hlog : 0 ≤ Real.log (1 + W omega) :=
    Real.log_nonneg (le_add_of_nonneg_right homega.1)
  refine ⟨1 + Real.log (1 + W omega) / t,
    add_pos_of_pos_of_nonneg one_pos (div_nonneg hlog ht.le), ?_⟩
  intro n i
  have hexp := homega.2 n i
  rw [abs_of_pos (Real.exp_pos _)] at hexp
  have hscale : (3 : ℝ) ^ (eta * (n : ℝ)) = Real.exp (t * xi * (n : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    dsimp only [eta]
    field_simp
  rw [hscale] at hexp
  have h := le_affine_of_exp_le (B n i omega) n (W omega) t xi homega.1 ht hexp
  linarith only [h]

end SubdiffusiveProcess
