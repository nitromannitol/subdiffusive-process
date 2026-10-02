import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

/-!
# Finite weighted-defect recurrence

This is the abstract sequence engine behind the homogenization step.  It is
adapted from Algsuperdiff's
`Section3/Provider/Homogenization/FiniteCorridorIteration.lean`; the carrier is
kept independent of either model so the eventual provider need only supply the
response recurrence and crude bound.
-/

/-- The finite convolution estimate needed by the weighted-defect induction. -/
def WeightedDefectKernel (C r ρ : ℝ) : Prop :=
  ∀ j : ℕ,
    C * ∑ k ∈ Finset.Icc 1 j, r ^ k * (ρ ^ (j - k) - ρ ^ j) ≤
      (1 / 2 : ℝ) * ρ ^ j

/-- A finite weighted-defect recurrence decays geometrically whenever its
convolution kernel has the required half-gain. -/
theorem weightedDefect_decay_of_kernel {F : ℕ → ℝ} {A C K₀ K δ r ρ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hrρ : r ≤ ρ)
    (hK : 0 ≤ K) (hAK : 2 * A ≤ K) (hK₀K : K₀ ≤ K)
    (hkernel : WeightedDefectKernel C r ρ)
    (hinit : F 0 ≤ K₀ * δ)
    (hrec : ∀ j : ℕ,
      F j ≤ A * δ * (δ + r ^ j) +
        C * ∑ k ∈ Finset.Icc 1 j, r ^ k * (F (j - k) - F j)) :
    ∀ j : ℕ, F j ≤ K * δ * (δ + ρ ^ j) := by
  have hρ0 : 0 ≤ ρ := hr.trans hrρ
  have hKδ : 0 ≤ K * δ := mul_nonneg hK hδ
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        have h1 : K₀ * δ ≤ K * δ := mul_le_mul_of_nonneg_right hK₀K hδ
        have h2 : 0 ≤ K * δ * δ := mul_nonneg hKδ hδ
        rw [pow_zero]
        linarith
      · have hT : 0 ≤ ∑ k ∈ Finset.Icc 1 j, r ^ k :=
          Finset.sum_nonneg fun k _ => pow_nonneg hr k
        have hsum : (∑ k ∈ Finset.Icc 1 j, r ^ k * (F (j - k) - F j)) ≤
            K * δ ^ 2 * (∑ k ∈ Finset.Icc 1 j, r ^ k) +
              K * δ * (∑ k ∈ Finset.Icc 1 j, r ^ k * ρ ^ (j - k)) -
              F j * (∑ k ∈ Finset.Icc 1 j, r ^ k) := by
          calc
            (∑ k ∈ Finset.Icc 1 j, r ^ k * (F (j - k) - F j))
                ≤ ∑ k ∈ Finset.Icc 1 j,
                    r ^ k * (K * δ * (δ + ρ ^ (j - k)) - F j) := by
                  refine Finset.sum_le_sum fun k hk => ?_
                  exact mul_le_mul_of_nonneg_left
                    (sub_le_sub_right
                      (ih (j - k) (by
                        have hk1 := (Finset.mem_Icc.mp hk).1
                        omega)) (F j))
                    (pow_nonneg hr k)
            _ = ∑ k ∈ Finset.Icc 1 j,
                  (K * δ ^ 2 * r ^ k + K * δ * (r ^ k * ρ ^ (j - k)) -
                    F j * r ^ k) :=
                Finset.sum_congr rfl fun k _ => by ring
            _ = K * δ ^ 2 * (∑ k ∈ Finset.Icc 1 j, r ^ k) +
                  K * δ * (∑ k ∈ Finset.Icc 1 j, r ^ k * ρ ^ (j - k)) -
                  F j * (∑ k ∈ Finset.Icc 1 j, r ^ k) := by
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
                  ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        have hkernel' : C * ((∑ k ∈ Finset.Icc 1 j, r ^ k * ρ ^ (j - k)) -
            ρ ^ j * (∑ k ∈ Finset.Icc 1 j, r ^ k)) ≤ (1 / 2 : ℝ) * ρ ^ j := by
          have hUT : (∑ k ∈ Finset.Icc 1 j, r ^ k * ρ ^ (j - k)) -
              ρ ^ j * (∑ k ∈ Finset.Icc 1 j, r ^ k) =
                ∑ k ∈ Finset.Icc 1 j, r ^ k * (ρ ^ (j - k) - ρ ^ j) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun k _ => by ring
          rw [hUT]
          exact hkernel j
        have hrpow : r ^ j ≤ ρ ^ j := pow_le_pow_left₀ hr hrρ j
        have hKhalf : (0 : ℝ) ≤ K / 2 * δ := by linarith
        have hAδ : A * δ ≤ K / 2 * δ :=
          mul_le_mul_of_nonneg_right (by linarith) hδ
        have hforce : A * δ * (δ + r ^ j) + (1 / 2 : ℝ) * K * δ * ρ ^ j ≤
            K * δ * (δ + ρ ^ j) := by
          have hAr : A * δ * r ^ j ≤ K / 2 * δ * ρ ^ j :=
            mul_le_mul hAδ hrpow (pow_nonneg hr j) hKhalf
          have hAδsq : A * δ * δ ≤ K / 2 * δ * δ :=
            mul_le_mul_of_nonneg_right hAδ hδ
          have hKδsq : 0 ≤ K * δ * δ := mul_nonneg hKδ hδ
          linarith
        have hsumC := mul_le_mul_of_nonneg_left hsum hC
        have hkernelMul := mul_le_mul_of_nonneg_left hkernel' hKδ
        have hjrec := hrec j
        have hpre : F j ≤ K * δ * (δ + ρ ^ j) +
            C * (∑ k ∈ Finset.Icc 1 j, r ^ k) *
              (K * δ * (δ + ρ ^ j) - F j) := by
          linarith
        have hCT : 0 ≤ C * (∑ k ∈ Finset.Icc 1 j, r ^ k) := mul_nonneg hC hT
        by_contra hcon
        push_neg at hcon
        have hXle : K * δ * (δ + ρ ^ j) - F j ≤ 0 := by linarith
        have hmul2 : C * (∑ k ∈ Finset.Icc 1 j, r ^ k) *
            (K * δ * (δ + ρ ^ j) - F j) ≤
              C * (∑ k ∈ Finset.Icc 1 j, r ^ k) * 0 :=
          mul_le_mul_of_nonneg_left hXle hCT
        rw [mul_zero] at hmul2
        linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
