module

public import Mathlib
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldPrePrincipal

@[expose] public section

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess

namespace SubdiffusiveProcess.Paper

theorem prefix_sqrt_linear (L : ℝ) (hL : 0 ≤ L) :
    (2 * ENNReal.ofReal (2 + L)) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (2 * (1 + L)) := by
  have hscalar : Real.sqrt (2 * (2 + L)) ≤ 2 * (1 + L) := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith [sq_nonneg L]
  have hbase : (2 : ENNReal) * ENNReal.ofReal (2 + L) =
      ENNReal.ofReal (2 * (2 + L)) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [hbase, ENNReal.ofReal_rpow_of_nonneg (by linarith) (by norm_num)]
  rw [← Real.sqrt_eq_rpow]
  exact ENNReal.ofReal_le_ofReal hscalar


noncomputable def prefix_log_card (d j : ℕ) : ℝ :=
  Real.log (2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ))

theorem prefix_log_card_nonneg (d j : ℕ) :
    0 ≤ prefix_log_card d j := by
  unfold prefix_log_card
  apply Real.log_nonneg
  have hpow : 1 ≤ (2 * 3 ^ (2 * j + 1) + 1) ^ d :=
    Nat.one_le_pow _ _ (by omega)
  have hcast : (1 : ℝ) ≤ (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr hpow
  linarith

theorem prefix_log_card_le_linear (d j : ℕ) :
    prefix_log_card d j ≤
      (((d * (2 + 2 * j) + 1 : ℕ) : ℝ)) * Real.log 3 := by
  unfold prefix_log_card
  have hnat : 2 * (2 * 3 ^ (2 * j + 1) + 1) ^ d ≤
      3 ^ (d * (2 + 2 * j) + 1) := by
    simpa only [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using aux_psf_nat_cover_bound d 0 (2 * j)
  have hcast : (2 : ℝ) * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) =
      ((2 * (2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) := by
    push_cast
    ring
  have hle : (2 : ℝ) * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) ≤
      (3 : ℝ) ^ (d * (2 + 2 * j) + 1) := by
    rw [hcast]
    have hh : ((2 * (2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) ≤
        ((3 ^ (d * (2 + 2 * j) + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using! hh
  have hpos : 0 < (2 : ℝ) * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) := by
    have hpow : 0 < (2 * 3 ^ (2 * j + 1) + 1) ^ d :=
      Nat.pow_pos (by omega)
    have hcast : 0 < (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) :=
      Nat.cast_pos.mpr hpow
    positivity
  calc
    Real.log (2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ)) ≤
      Real.log ((3 : ℝ) ^ (d * (2 + 2 * j) + 1)) :=
        Real.log_le_log hpos hle
    _ = (((d * (2 + 2 * j) + 1 : ℕ) : ℝ)) * Real.log 3 := by
      rw [Real.log_pow]


noncomputable def prefix_L2_series_bound {d : ℕ} (M : GMCModel d)
    (s : ℝ) (j : ℕ) : ℝ :=
  (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
    (2 * aux_psf_sigma M * (1 + prefix_log_card d j))

theorem prefix_L2_series_bound_nonneg {d : ℕ} (M : GMCModel d)
    (s : ℝ) (j : ℕ) : 0 ≤ prefix_L2_series_bound M s j := by
  unfold prefix_L2_series_bound
  have hL := prefix_log_card_nonneg d j
  have hσ := (aux_psf_sigma_pos M).le
  positivity

theorem prefix_L2_series_bound_summable {d : ℕ} (M : GMCModel d)
    (s : ℝ) (hs : 0 < s) :
    Summable (fun j : ℕ => prefix_L2_series_bound M s j) := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hσ := aux_psf_sigma_pos M
  set r : ℝ := (3 : ℝ) ^ (-(s / 8)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hrn : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hrj : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) = r ^ j := by
    intro j
    rw [hr, ← Real.rpow_natCast ((3 : ℝ) ^ (-(s / 8))) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  set A : ℝ := 1 + ((2 * (d : ℝ) + 1) * Real.log 3) with hA
  set B : ℝ := 2 * (d : ℝ) * Real.log 3 with hB
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set C : ℝ := 4 * aux_psf_sigma M * (A + B) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hmaj : Summable (fun j : ℕ => C * (((j : ℝ) + 1) ^ 2 * r ^ j)) := by
    have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hrn
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrn
    have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hrn
    have hbase : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ 2 * r ^ j) := by
      refine ((h2.add (h1.mul_left 2)).add h0).congr ?_
      intro j
      ring
    exact hbase.mul_left C
  refine Summable.of_nonneg_of_le
    (prefix_L2_series_bound_nonneg M s) (fun j => ?_) hmaj
  unfold prefix_L2_series_bound
  rw [hrj j]
  have hLj := prefix_log_card_le_linear d j
  have hlin : 1 + prefix_log_card d j ≤ A + B * (j : ℝ) := by
    rw [hA, hB]
    push_cast at hLj
    nlinarith [hlog3.le]
  have hlin2 : A + B * (j : ℝ) ≤ (A + B) * ((j : ℝ) + 1) := by
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hcard : ((2 * j + 1 : ℕ) : ℝ) ≤ 2 * ((j : ℝ) + 1) := by
    push_cast
    linarith
  have hprod : ((2 * j + 1 : ℕ) : ℝ) *
      (2 * aux_psf_sigma M * (1 + prefix_log_card d j)) ≤
      4 * aux_psf_sigma M * (A + B) * ((j : ℝ) + 1) ^ 2 := by
    have hLnonneg := prefix_log_card_nonneg d j
    calc
      ((2 * j + 1 : ℕ) : ℝ) *
          (2 * aux_psf_sigma M * (1 + prefix_log_card d j)) ≤
        (2 * ((j : ℝ) + 1)) *
          (2 * aux_psf_sigma M * (1 + prefix_log_card d j)) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (2 * ((j : ℝ) + 1)) *
          (2 * aux_psf_sigma M * ((A + B) * ((j : ℝ) + 1))) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left (hlin.trans hlin2) (by positivity)
            · positivity
      _ = 4 * aux_psf_sigma M * (A + B) * ((j : ℝ) + 1) ^ 2 := by ring
  have hstep := mul_le_mul_of_nonneg_left hprod (pow_nonneg hr0.le j)
  rw [hC]
  nlinarith [hstep]


end SubdiffusiveProcess.Paper
