module

public import SubdiffusiveProcess.Paper.lem_as_regularity_response_score_pair

@[expose] public section

/-! The clipped response term in the accumulated error has a deterministic
discarded-depth bound. A retained relative atom comparison therefore costs
only a square-root tolerance and that geometric tail. The three field terms
of the accumulated error are handled separately.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- Every physical primitive atom is nonnegative, including before its cutoff. -/
theorem aux_lem_as_regularity_clipped_response_pair_atom_nonneg {d : ℕ} [NeZero d]
    (M : GMCModel d) (eta : ℕ → BilateralField d → PotentialSample d)
    (N : ℕ) (l : ℤ) (y : SpatialCoordinates d) (omega : BilateralField d) :
    0 ≤ aux_prefix_rraw_atom M eta N l y omega := by
  unfold aux_prefix_rraw_atom
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

/-- The retained clipped-response supremum loses only a square-root tolerance. -/
theorem aux_lem_as_regularity_clipped_response_pair_shallow {d : ℕ} [NeZero d]
    (M : GMCModel d) (s : ℝ) (hs : 0 ≤ s)
    (eta : ℕ → BilateralField d → PotentialSample d) (omega : BilateralField d)
    (n : ℤ) (z : SpatialCoordinates d) (N N' H : ℕ)
    (hN : n + (H : ℤ) ≤ (N : ℤ)) (hN' : n + (H : ℤ) ≤ (N' : ℤ))
    (eps : ℝ) (heps : 0 ≤ eps)
    (hretained : ∀ rk ∈ aux_prefix_rraw_G d H,
      aux_prefix_rraw_atom M eta N (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega ≤
        (1 + eps) * aux_prefix_rraw_atom M eta N' (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega + eps) :
    (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s (eta N omega)
      ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) H).toReal ≤
      (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow M s (eta N' omega)
        ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) H).toReal + Real.sqrt (2 * eps) := by
  classical
  by_cases hne : (aux_prefix_rraw_G d H).Nonempty
  · rw [aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow_toReal_eq_atoms
      M s eta n z N H hN hne,
      aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow_toReal_eq_atoms
        M s eta n z N' H hN' hne]
    apply Finset.sup'_le hne
    intro rk hrk
    let w : ℝ := (3 : ℝ) ^ (-(s / 2) * (rk.1 : ℝ))
    have hw0 : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
    have hw1 : w ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have hr : 0 ≤ (rk.1 : ℝ) := Nat.cast_nonneg _
      have hprod := mul_nonneg hs hr
      nlinarith only [hprod]
    have hclip := sqrt_min_one_le_of_relative_le
      (aux_lem_as_regularity_clipped_response_pair_atom_nonneg M eta N' _ _ omega)
      heps (hretained rk hrk)
    have hweighted := mul_le_mul_of_nonneg_left hclip hw0
    have herror := mul_le_mul_of_nonneg_right hw1 (Real.sqrt_nonneg (2 * eps))
    have hpoint : w * Real.sqrt (min
        (aux_prefix_rraw_atom M eta N (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega) 1) ≤
      w * Real.sqrt (min
        (aux_prefix_rraw_atom M eta N' (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega) 1) +
        Real.sqrt (2 * eps) := by
      nlinarith only [hweighted, herror]
    have hsup := Finset.le_sup' (fun q : ℕ × (Fin d → ℤ) =>
      (3 : ℝ) ^ (-(s / 2) * (q.1 : ℝ)) * Real.sqrt (min
        (aux_prefix_rraw_atom M eta N' (-n - q.1)
          (z + (3 : ℝ) ^ (-n - q.1) • aux_prefix_rraw_kvec q.2) omega) 1)) hrk
    exact hpoint.trans (add_le_add hsup le_rfl)
  · have hempty : aux_prefix_rraw_G d H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow, hempty,
      Finset.sup_empty, bot_eq_zero, ENNReal.toReal_zero, zero_add]
    exact Real.sqrt_nonneg _

/-- The full clipped-response term is bounded by its future value and two explicit errors. -/
theorem lem_as_regularity_clipped_response_pair {d : ℕ} [NeZero d]
    (M : GMCModel d) (s : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d) (omega : BilateralField d)
    (n : ℤ) (z : SpatialCoordinates d) (N N' H : ℕ)
    (hNN' : N ≤ N') (hN : n + (H : ℤ) ≤ (N : ℤ))
    (eps : ℝ) (heps : 0 ≤ eps)
    (hretained : ∀ rk ∈ aux_prefix_rraw_G d H,
      aux_prefix_rraw_atom M eta N (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega ≤
        (1 + eps) * aux_prefix_rraw_atom M eta N' (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega + eps) :
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((N : ℤ) - n).toNat
      ((3 : ℝ) ^ N • z) (eta N omega)).toReal ≤
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s ((N' : ℤ) - n).toNat
        ((3 : ℝ) ^ N' • z) (eta N' omega)).toReal + Real.sqrt (2 * eps) +
        (3 : ℝ) ^ (-(s / 2) * ((H + 1 : ℕ) : ℝ)) := by
  have hHN : H ≤ ((N : ℤ) - n).toNat := by omega
  have hHN' : H ≤ ((N' : ℤ) - n).toNat := by omega
  have hshallow := aux_lem_as_regularity_clipped_response_pair_shallow M s hs.le eta omega
    n z N N' H hN (by omega) eps heps hretained
  have hupper := ENNReal.toReal_mono
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_ne_top M s hs
      ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) (eta N' omega))
    (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow_le_Dt1 M s (eta N' omega)
      ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) H hHN')
  have htail := aux_lem_prefix_limit_actual_coordinate_cauchy_abs_Dt1_sub_T1shallow_le
    M s (eta N omega) ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) H
    (aux_lem_prefix_limit_actual_coordinate_cauchy_T1shallow_le_Dt1 M s (eta N omega)
      ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) H hHN)
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_le_max M s hs (eta N omega)
      ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) H)
  have htail' := (le_abs_self _).trans htail
  linarith only [hshallow, hupper, htail']

end Paper
