import SubdiffusiveProcess.Static.HarmonicPairFactors
import SubdiffusiveProcess.Static.HarmonicCutoffGap
import SubdiffusiveProcess.Static.HarmonicCutoffPatching

/-! # Cardinality-root bounds for the finite harmonic cell bank -/
open MeasureTheory Homogenization Metric
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- The cell cutoff gap is no larger than the mesh depth, even at negative
physical cell scales. -/
theorem pair_cell_cutoff_gap {j m n : ℕ} (hjm : j ≤ m) :
    j - min j ((m : ℤ) - n).toNat ≤ n := by omega

/-- A half-power budget absorbs the cardinality root at high moment order. -/
theorem pair_cardinality_root_bound {a : ℕ} (d n : ℕ) {S R : ℝ}
    (hS : 1 ≤ S) (hR : 1 ≤ R) (hdR : 2 * (d : ℝ) ≤ R)
    (ha : (a : ℝ) ≤ S * ((3 : ℝ) ^ n) ^ d) :
    (a : ℝ) ^ (1 / R) ≤ S * (3 : ℝ) ^ ((n : ℝ) / 2) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hroot : S ^ (1 / R) ≤ S := by
    calc
      _ ≤ S ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hS
        ((div_le_one hR0).mpr hR)
      _ = S := Real.rpow_one S
  have hscale : (((3 : ℝ) ^ n) ^ d) ^ (1 / R) ≤
      (3 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast (3 : ℝ) n,
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h := mul_le_mul_of_nonneg_left hdR (by positivity : (0 : ℝ) ≤ n)
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hR0).mpr
    nlinarith only [h]
  calc
    _ ≤ (S * ((3 : ℝ) ^ n) ^ d) ^ (1 / R) :=
      Real.rpow_le_rpow (by positivity) ha (by positivity)
    _ = S ^ (1 / R) * (((3 : ℝ) ^ n) ^ d) ^ (1 / R) :=
      Real.mul_rpow (zero_le_one.trans hS) (by positivity)
    _ ≤ S * (3 : ℝ) ^ ((n : ℝ) / 2) :=
      mul_le_mul hroot hscale (by positivity) (zero_le_one.trans hS)

/-- Transition-cell counts in a bounded parent window grow like `3^(dn)`. -/
theorem pair_transition_card_bound {d n : ℕ} {R1 R2 rho : ℝ}
    (hrho : 0 ≤ rho) (hR2 : R2 ≤ rho) :
    let h := ((3 : ℝ) ^ n)⁻¹
    let T := (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2)
      (by positivity : 0 < h)).toFinset
    (T.card : ℝ) ≤ (2 * (rho + 1)) ^ d * ((3 : ℝ) ^ n) ^ d := by
  classical
  dsimp only
  let h := ((3 : ℝ) ^ n)⁻¹
  have hh : 0 < h := by positivity
  let T := (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2) hh).toFinset
  have hcount := aux_hcut_card_mul_le (x := (0 : Vec d)) hh T hrho (fun k hk => by
    have htrans := (aux_hcut_mem_T hh).mp hk
    refine ⟨aux_hcut_cc h k, mem_ball_self (half_pos hh), ?_⟩
    exact ball_subset_ball hR2 (aux_hcut_trans_cell_subset hh htrans
      (mem_closedBall_self (half_pos hh).le)))
  have hh1 : h ≤ 1 := by
    dsimp only [h]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))
  have hcount' : (T.card : ℝ) * h ^ d ≤ (2 * (rho + 1)) ^ d :=
    hcount.trans (pow_le_pow_left₀ (by positivity) (by linarith) d)
  have hhd : 0 < h ^ d := by positivity
  have hdiv := (le_div_iff₀ hhd).mpr hcount'
  convert hdiv using 1 <;> simp [T, h, div_eq_mul_inv]

end SubdiffusiveProcess.Static
