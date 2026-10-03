module

public import SubdiffusiveProcess.Paper.lfgc_near_transfer

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# A near-unit chart passes the single-point tests

If `aux_lfgc_near_tests_NearChart σ F ref θ` with `0 ≤ θ ≤ 1/(4d)`, then `2/3 ≤ lamF/ref`, `LamF/ref ≤ 3/2`,
the normalized top-cube matrix `A = σ/ref` satisfies `(2d)⁻¹ tr A |x|² ≤ x · A x`, and the
error is at most `θ`.  Deterministic.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02
open scoped ENNReal

namespace Paper
variable {d : ℕ}

/-- Coercivity of a matrix within `θ ≤ 1/(4d)` of the identity, entrywise. -/
theorem lfgc_near_pass (hd : 2 ≤ d) (A : Matrix (Fin d) (Fin d) ℝ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / (4 * d))
    (hA : ∀ i j, |A i j - (if i = j then (1 : ℝ) else 0)| ≤ θ) (x : Fin d → ℝ) :
    (2 * (d : ℝ))⁻¹ * Matrix.trace A * (x ⬝ᵥ x) ≤ x ⬝ᵥ A.mulVec x := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
  set S := ∑ i, x i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hxx : x ⬝ᵥ x = S := by
    simp only [dotProduct, hS, pow_two]
  set B : Matrix (Fin d) (Fin d) ℝ := fun i j => A i j - (if i = j then (1 : ℝ) else 0)
  have hquad : x ⬝ᵥ A.mulVec x = S + ∑ i, ∑ j, x i * B i j * x j := by
    simp only [dotProduct, Matrix.mulVec, hS, B, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ j, x i * ((A i j - if i = j then 1 else 0) * x j) =
        ∑ j, x i * (A i j * x j) - ∑ j, x i * ((if i = j then (1:ℝ) else 0) * x j) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at this
    simp only [mul_assoc]
    rw [this]; ring
  have hBsum : |∑ i, ∑ j, x i * B i j * x j| ≤ θ * (d * S) := by
    calc |∑ i, ∑ j, x i * B i j * x j| ≤ ∑ i, ∑ j, |x i| * θ * |x j| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul, abs_mul]
          gcongr
          exact hA i j
      _ = θ * (∑ i, |x i|) ^ 2 := by
          rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ θ * (d * S) := by
          gcongr
          have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |x i|)
          simpa [hS, sq_abs] using this
  have htr : Matrix.trace A ≤ d * (1 + θ) := by
    have : ∀ i, A i i ≤ 1 + θ := fun i => by
      have := (abs_le.mp (hA i i)).2
      simp only [if_true] at this
      linarith
    calc Matrix.trace A = ∑ i, A i i := rfl
      _ ≤ ∑ _i : Fin d, (1 + θ) := Finset.sum_le_sum fun i _ => this i
      _ = d * (1 + θ) := by simp; ring
  have hdθ : (d : ℝ) * θ ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hθ hdpos.le
    calc (d : ℝ) * θ ≤ d * (1 / (4 * d)) := this
      _ = 1 / 4 := by field_simp
  rw [hxx, hquad]
  have hlow : S - θ * (d * S) ≤ S + ∑ i, ∑ j, x i * B i j * x j := by
    have := (abs_le.mp hBsum).1; linarith
  have hup : (2 * (d : ℝ))⁻¹ * Matrix.trace A * S ≤ (1 + θ) / 2 * S := by
    have h1 : (2 * (d : ℝ))⁻¹ * Matrix.trace A ≤ (1 + θ) / 2 := by
      rw [inv_mul_le_iff₀ (by positivity)]
      nlinarith [htr]
    exact mul_le_mul_of_nonneg_right h1 hS0
  refine hup.trans (le_trans ?_ hlow)
  have hθ8 : θ ≤ 1 / 8 := by
    have : (1 : ℝ) / (4 * d) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith
  nlinarith [hdθ, hS0, hθ8]

/-- The single-point tests for a near-unit chart. -/
theorem aux_lfgc_near_tests_NearChart.tests (hd : 2 ≤ d) {σ : ℝ} {F : TriadicCoeffFamily d} {ref θ : ℝ}
    (href : 0 < ref) (hlam : 0 < Paper.aux_lem_band_U2_lamF σ F) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 1 / (4 * d)) (hn : aux_lfgc_near_tests_NearChart σ F ref θ) :
    2 / 3 ≤ Paper.aux_lem_band_U2_lamF σ F / ref ∧
    Paper.aux_lem_band_U2_LamF σ F / ref ≤ 3 / 2 ∧
    (∀ x : Fin d → ℝ, (2 * (d : ℝ))⁻¹ *
        Matrix.trace (fun i j => Paper.aux_lem_band_U2_sigF i j F / ref : Matrix (Fin d) (Fin d) ℝ) *
          (x ⬝ᵥ x) ≤
        x ⬝ᵥ Matrix.mulVec (fun i j => Paper.aux_lem_band_U2_sigF i j F / ref :
          Matrix (Fin d) (Fin d) ℝ) x) ∧
    Paper.aux_lem_band_U2_errF σ F ref ≤ θ := by
  obtain ⟨h1, h2, h3, h4⟩ := hn
  have hθ12 : θ ≤ 1 / 2 := by
    have : (1 : ℝ) / (4 * d) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith
  refine ⟨?_, ?_, fun x => lfgc_near_pass hd _ hθ0 hθ h3 x, h4⟩
  · have hup := (abs_le.mp h1).2
    have hq : ref / Paper.aux_lem_band_U2_lamF σ F ≤ 3 / 2 := by linarith
    rw [div_le_iff₀ hlam] at hq
    rw [le_div_iff₀ href]
    linarith
  · have := (abs_le.mp h2).2
    linarith

end Paper
