import SubdiffusiveProcess.Paper.lem_prefix_limit_actual_coordinate_cauchy
import SubdiffusiveProcess.Analysis.FiniteSupRelativeComparison

/-! Retained primitive-response comparisons control the full discounted
response score up to its literal discarded tail. This deterministic step
does not bound the probability or size of that tail.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- The response discount is at most one when the fractional order is nonnegative. -/
theorem aux_lem_as_regularity_response_score_pair_discount (s : ℝ) (hs : 0 ≤ s) (r : ℕ) :
    aux_prefix_rraw_c s r ≤ 1 := by
  rw [aux_prefix_rraw_c, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  have hr := Nat.cast_nonneg (α := ℝ) r
  nlinarith only [hs, hr, mul_nonneg hs hr]

/-- A retained physical response comparison controls the full score plus its discarded tail. -/
theorem lem_as_regularity_response_score_pair {d : ℕ} [NeZero d]
    (M : GMCModel d) (s : ℝ) (hs : 0 ≤ s)
    (eta : ℕ → BilateralField d → PotentialSample d) (omega : BilateralField d)
    (n : ℤ) (z : SpatialCoordinates d) (N N' H : ℕ)
    (hNN' : N ≤ N') (hcutoff : n + (H : ℤ) ≤ (N : ℤ))
    (eps : ℝ) (heps : 0 ≤ eps)
    (hretained : ∀ rk ∈ aux_prefix_rraw_G d H,
      aux_prefix_rraw_atom M eta N (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega ≤
        (1 + eps) * aux_prefix_rraw_atom M eta N' (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega + eps) :
    (aux_prefix_rraw_Rset M s (eta N omega) ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z)).toReal ≤
      (1 + eps) * (aux_prefix_rraw_Rset M s (eta N' omega) ((N' : ℤ) - n).toNat
        ((3 : ℝ) ^ N' • z)).toReal + eps +
      (aux_prefix_rraw_tail M s (eta N omega) ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) H).toReal := by
  classical
  have hHN : H ≤ ((N : ℤ) - n).toNat := by omega
  have hHN' : H ≤ ((N' : ℤ) - n).toNat := by omega
  have hshallow := finite_discounted_relative_comparison (aux_prefix_rraw_G d H)
    (fun rk => aux_prefix_rraw_c s rk.1)
    (fun rk => aux_prefix_rraw_A M (eta N omega) ((N : ℤ) - n).toNat
      ((3 : ℝ) ^ N • z) rk.1 rk.2)
    (fun rk => aux_prefix_rraw_A M (eta N' omega) ((N' : ℤ) - n).toNat
      ((3 : ℝ) ^ N' • z) rk.1 rk.2) eps heps
    (fun rk _ => aux_lem_as_regularity_response_score_pair_discount s hs rk.1)
    (fun rk _ => aux_prefix_rraw_A_ne_top M (eta N omega) _ _ rk.1 rk.2)
    (fun rk _ => aux_prefix_rraw_A_ne_top M (eta N' omega) _ _ rk.1 rk.2) (by
      intro rk hrk
      have hrH : rk.1 ≤ H :=
        (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hrk).1).1).2
      rw [aux_prefix_rraw_A_eq_atom M eta n z N rk.1 rk.2 (by omega),
        aux_prefix_rraw_A_eq_atom M eta n z N' rk.1 rk.2 (by omega)]
      exact hretained rk hrk)
  change (aux_prefix_rraw_shallow M s (eta N omega) ((N : ℤ) - n).toNat
      ((3 : ℝ) ^ N • z) H).toReal ≤
    (1 + eps) * (aux_prefix_rraw_shallow M s (eta N' omega) ((N' : ℤ) - n).toNat
      ((3 : ℝ) ^ N' • z) H).toReal + eps at hshallow
  have hupper := ENNReal.toReal_mono
    (aux_psf_Rsc_ne_top M s ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) (eta N' omega))
    (aux_prefix_rraw_shallow_le_Rset M s (eta N' omega) ((N' : ℤ) - n).toNat
      ((3 : ℝ) ^ N' • z) H hHN')
  change (aux_prefix_rraw_shallow M s (eta N' omega) ((N' : ℤ) - n).toNat
      ((3 : ℝ) ^ N' • z) H).toReal ≤
    (aux_prefix_rraw_Rset M s (eta N' omega) ((N' : ℤ) - n).toNat
      ((3 : ℝ) ^ N' • z)).toReal at hupper
  have hupper' := mul_le_mul_of_nonneg_left hupper
    (show 0 ≤ 1 + eps by linarith only [heps])
  have htail := (le_abs_self
    ((aux_prefix_rraw_Rset M s (eta N omega) ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z)).toReal -
      (aux_prefix_rraw_shallow M s (eta N omega) ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) H).toReal)).trans
      (aux_prefix_rraw_abs_Rset_sub_shallow_le M s (eta N omega) ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) H hHN)
  linarith only [hshallow, hupper', htail]

end Paper
