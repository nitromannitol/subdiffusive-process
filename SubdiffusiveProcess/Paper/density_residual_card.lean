module

public import SubdiffusiveProcess.Paper.lem_finite_stopping_partition_tree
@[expose] public section

open Filter MeasureTheory Finset
open scoped BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
open Classical

/-- The finite-word count in the density proof, with the real exponents and
large-subdivision inequality used in the paper. The set being counted is literal. -/
theorem density_residual_card
    (A : Type*) [Fintype A] (NP : Finset A)
    (L Cd dim eta : ℝ) (hL : 1 < L) (hCd : 0 < Cd)
    (heta : 0 < eta) (heta3 : eta ≤ 3)
    (hCard : (Fintype.card A : ℝ) ≤ L ^ dim)
    (hNP : (NP.card : ℝ) ≤ Cd * L ^ (dim - 1))
    (hLarge : 2 * Cd ^ (eta / 3) ≤ L ^ (eta / 3 - eta / 8)) (J : ℕ) :
    (((univ : Finset (Fin J → A)).filter (fun w =>
      (eta / 3) * (J : ℝ) ≤ (((univ : Finset (Fin J)).filter fun i => w i ∈ NP).card : ℝ))).card : ℝ) ≤
      L ^ ((dim - eta / 8) * (J : ℝ)) := by
  have hL0 : 0 < L := zero_lt_one.trans hL
  let T := Nat.ceil ((eta / 3) * (J : ℝ))
  have hT : (eta / 3) * (J : ℝ) ≤ (T : ℝ) := Nat.le_ceil _
  have hTJ : T ≤ J := by
    apply Nat.ceil_le.mpr
    nlinarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  have heq : (univ : Finset (Fin J → A)).filter (fun w =>
      (eta / 3) * (J : ℝ) ≤ (((univ : Finset (Fin J)).filter fun i => w i ∈ NP).card : ℝ)) =
      univ.filter (fun w : Fin J → A => T ≤ (univ.filter fun i => w i ∈ NP).card) := by
    ext w
    simp only [mem_filter, mem_univ, true_and]
    exact Nat.ceil_le.symm
  rw [heq]
  have hcount : (((univ : Finset (Fin J → A)).filter
      (fun w => T ≤ ((univ : Finset (Fin J)).filter fun i => w i ∈ NP).card)).card : ℝ) ≤
      (2 : ℝ) ^ J * (NP.card : ℝ) ^ T * (Fintype.card A : ℝ) ^ (J - T) := by
    exact_mod_cast aux_lem_finite_stopping_partition_card_many_hits_le J T NP
  have hraw : (2 : ℝ) ^ J * (NP.card : ℝ) ^ T * (Fintype.card A : ℝ) ^ (J - T) ≤
      (2 : ℝ) ^ J * (Cd * L ^ (dim - 1)) ^ T * (L ^ dim) ^ (J - T) := by
    gcongr
  apply hcount.trans (hraw.trans ?_)
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogLarge := Real.log_le_log (by positivity : (0 : ℝ) < 2 * Cd ^ (eta / 3)) hLarge
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hCd, Real.log_rpow hL0] at hlogLarge
  have hlogRatio : Real.log Cd - Real.log L ≤ 0 := by
    nlinarith
  have hweight := mul_le_mul_of_nonpos_right hT hlogRatio
  have hlargeJ := mul_le_mul_of_nonneg_right hlogLarge (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
  apply (Real.log_le_log_iff (by positivity : (0 : ℝ) <
    (2 : ℝ) ^ J * (Cd * L ^ (dim - 1)) ^ T * (L ^ dim) ^ (J - T))
    (Real.rpow_pos_of_pos hL0 _)).mp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_mul hCd.ne' (by positivity), Real.log_rpow hL0,
    Real.log_rpow hL0, Real.log_rpow hL0, Nat.cast_sub hTJ]
  nlinarith

end Paper
