import SubdiffusiveProcess.Paper.cor_14
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.relative_response_variation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section



lemma aux_lem_relvar_normalized_response_denominator_assembly_bound (K : ℝ) (hK : 0 < K) :
    ∀ (G Delta D Dg V A : ℝ),
      0 ≤ G → 0 ≤ Delta → 0 < D → 0 ≤ V →
      Real.exp (-G) * D ≤ Dg →
      |A| ≤ K * Delta * D →
      |Dg - D| ≤ K * G * Real.exp (K * G) * D * V →
      |A / Dg - A / D| ≤ (K ^ 2 + K + 1) * G *
        Real.exp ((K ^ 2 + K + 1) * G) * Delta * V := by
  intro G Delta D Dg V A hG hDelta hD hV hDg_lower hA_abs hDg_diff_abs
  have hDg_pos : 0 < Dg := lt_of_lt_of_le (mul_pos (Real.exp_pos (-G)) hD) hDg_lower
  have hden_pos : 0 < D * Dg := mul_pos hD hDg_pos
  have hCpos : 0 < K ^ 2 + K + 1 := by nlinarith [sq_nonneg K, hK]
  have hDg_diff_abs' : |D - Dg| ≤ K * G * Real.exp (K * G) * D * V := by
    rw [abs_sub_comm]
    exact hDg_diff_abs
  have hsub : A / Dg - A / D = A * (D - Dg) / (D * Dg) := by
    field_simp
  have hratio : D / Dg ≤ Real.exp G := by
    rw [div_le_iff₀ hDg_pos]
    have e : Real.exp G * Real.exp (-G) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      D = Real.exp G * (Real.exp (-G) * D) := by rw [← mul_assoc, e, one_mul]
      _ ≤ Real.exp G * Dg := mul_le_mul_of_nonneg_left hDg_lower (Real.exp_pos G).le
  have hK2le : K ^ 2 ≤ K ^ 2 + K + 1 := by nlinarith [hK]
  have hK1le : K + 1 ≤ K ^ 2 + K + 1 := by nlinarith [sq_nonneg K]
  have hexp_le : Real.exp ((K + 1) * G) ≤
      Real.exp ((K ^ 2 + K + 1) * G) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hK1le hG)
  have hcoeff : K ^ 2 * Real.exp ((K + 1) * G) ≤
      (K ^ 2 + K + 1) * Real.exp ((K ^ 2 + K + 1) * G) :=
    mul_le_mul hK2le hexp_le (Real.exp_pos _).le hCpos.le
  have hnum : |A / Dg - A / D| = |A| * |D - Dg| / (D * Dg) := by
    rw [hsub, abs_div, abs_mul, abs_of_pos hden_pos]
  have hstep1 : |A| * |D - Dg| / (D * Dg) ≤
      (K * Delta * D) * (K * G * Real.exp (K * G) * D * V) / (D * Dg) := by
    apply div_le_div_of_nonneg_right _ hden_pos.le
    exact mul_le_mul hA_abs hDg_diff_abs' (abs_nonneg _)
      (mul_nonneg (mul_nonneg hK.le hDelta) hD.le)
  have hstep2 :
      (K * Delta * D) * (K * G * Real.exp (K * G) * D * V) / (D * Dg) =
        K ^ 2 * Delta * G * Real.exp (K * G) * V * (D / Dg) := by
    field_simp
  have hstep3 : K ^ 2 * Delta * G * Real.exp (K * G) * V * (D / Dg) ≤
      K ^ 2 * Delta * G * Real.exp (K * G) * V * Real.exp G := by
    apply mul_le_mul_of_nonneg_left hratio
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg K) hDelta) hG)
      (Real.exp_pos _).le) hV
  have hstep4 : K ^ 2 * Delta * G * Real.exp (K * G) * V * Real.exp G =
      K ^ 2 * Delta * G * Real.exp ((K + 1) * G) * V := by
    have hexp : Real.exp ((K + 1) * G) = Real.exp (K * G) * Real.exp G := by
      rw [show (K + 1) * G = K * G + G by ring, Real.exp_add]
    rw [hexp]
    ring
  have hstep5 : K ^ 2 * Delta * G * Real.exp ((K + 1) * G) * V ≤
      (K ^ 2 + K + 1) * Delta * G *
        Real.exp ((K ^ 2 + K + 1) * G) * V := by
    have hfac : 0 ≤ Delta * G * V := mul_nonneg (mul_nonneg hDelta hG) hV
    have hmm := mul_le_mul_of_nonneg_right hcoeff hfac
    calc
      K ^ 2 * Delta * G * Real.exp ((K + 1) * G) * V =
          (K ^ 2 * Real.exp ((K + 1) * G)) * (Delta * G * V) := by ring
      _ ≤ ((K ^ 2 + K + 1) * Real.exp ((K ^ 2 + K + 1) * G)) *
          (Delta * G * V) := hmm
      _ = (K ^ 2 + K + 1) * Delta * G *
          Real.exp ((K ^ 2 + K + 1) * G) * V := by ring
  calc
    |A / Dg - A / D| = |A| * |D - Dg| / (D * Dg) := hnum
    _ ≤ (K * Delta * D) * (K * G * Real.exp (K * G) * D * V) /
          (D * Dg) := hstep1
    _ = K ^ 2 * Delta * G * Real.exp (K * G) * V * (D / Dg) := hstep2
    _ ≤ K ^ 2 * Delta * G * Real.exp (K * G) * V * Real.exp G := hstep3
    _ = K ^ 2 * Delta * G * Real.exp ((K + 1) * G) * V := hstep4
    _ ≤ (K ^ 2 + K + 1) * Delta * G *
          Real.exp ((K ^ 2 + K + 1) * G) * V := hstep5
    _ = (K ^ 2 + K + 1) * G *
          Real.exp ((K ^ 2 + K + 1) * G) * Delta * V := by ring

theorem lem_relvar_normalized_response_denominator_assembly
    (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (G Delta D Dg V A : ℝ),
      0 ≤ G → 0 ≤ Delta → 0 < D → 0 ≤ V →
      Real.exp (-G) * D ≤ Dg →
      |A| ≤ K * Delta * D →
      |Dg - D| ≤ K * G * Real.exp (K * G) * D * V →
      |A / Dg - A / D| ≤ C * G * Real.exp (C * G) * Delta * V := by
  exact ⟨K ^ 2 + K + 1, by nlinarith [sq_nonneg K, hK],
    aux_lem_relvar_normalized_response_denominator_assembly_bound K hK⟩

end
end Paper
