import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter
open scoped Topology

namespace SubdiffusiveProcess

/-- A polynomial-times-triadic cardinality bound gives summability at the sharp strict margin d < q η. The polynomial costs no extra fixed exponent loss. -/
theorem summable_triadic_mesh_cardinality
    (k : ℕ → ℕ) (d b : ℕ) (C q η : ℝ)
    (hC : 0 ≤ C) (hq : 1 ≤ q) (hgap : (d : ℝ) < q * η)
    (hcard : ∀ n : ℕ, (k n : ℝ) ≤
      C * ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ ((d : ℝ) * n)) :
    Summable (fun n : ℕ =>
      (3 : ℝ) ^ (-η * n) * (k n : ℝ) ^ (1 / q)) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hexp_nonneg : 0 ≤ 1 / q := by positivity
  have hexp_le : 1 / q ≤ 1 := by
    rw [div_le_one hqpos]
    exact hq
  let r : ℝ := (3 : ℝ) ^ ((d : ℝ) / q - η)
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrexponent : (d : ℝ) / q - η < 0 := by
    apply sub_neg.mpr
    exact (div_lt_iff₀ hqpos).2 (by simpa [mul_comm] using hgap)
  have hrlt : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hrexponent
  have hrsum : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ b) * r ^ n) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ b * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one b (by simpa [abs_of_pos hrpos] using hrlt)
    have hshift := (hbase.comp_injective Nat.succ_injective).mul_left r⁻¹
    refine hshift.congr (fun n => ?_)
    simp only [Function.comp_apply, Nat.cast_succ]
    rw [pow_succ]
    field_simp [hrpos.ne']
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_
    (hrsum.mul_left (C ^ (1 / q)))
  intro n
  have hk_nonneg : 0 ≤ (k n : ℝ) := Nat.cast_nonneg _
  have hn_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
  have hn_one : 1 ≤ (n : ℝ) + 1 := by
    linarith only [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hpoly_one : 1 ≤ ((n : ℝ) + 1) ^ b := one_le_pow₀ hn_one
  have hkpow := Real.rpow_le_rpow hk_nonneg (hcard n) hexp_nonneg
  calc
    (3 : ℝ) ^ (-η * n) * (k n : ℝ) ^ (1 / q)
        ≤ (3 : ℝ) ^ (-η * n) *
            (C * (((n : ℝ) + 1) ^ b) * (3 : ℝ) ^ ((d : ℝ) * n)) ^ (1 / q) :=
          mul_le_mul_of_nonneg_left hkpow (Real.rpow_nonneg (by norm_num) _)
    _ = (3 : ℝ) ^ (-η * n) *
          (C ^ (1 / q) * ((((n : ℝ) + 1) ^ b) ^ (1 / q)) *
            (((3 : ℝ) ^ ((d : ℝ) * n)) ^ (1 / q))) := by
          rw [Real.mul_rpow (mul_nonneg hC (pow_nonneg hn_nonneg _))
            (Real.rpow_nonneg (by norm_num) _),
            Real.mul_rpow hC (pow_nonneg hn_nonneg _)]
    _ ≤ (3 : ℝ) ^ (-η * n) *
          (C ^ (1 / q) * (((n : ℝ) + 1) ^ b) *
            (((3 : ℝ) ^ ((d : ℝ) * n)) ^ (1 / q))) := by
          gcongr
          exact Real.rpow_le_self_of_one_le hpoly_one hexp_le
    _ = C ^ (1 / q) * (((n : ℝ) + 1) ^ b * r ^ n) := by
          have hgeom : (3 : ℝ) ^ (-η * n) *
              (((3 : ℝ) ^ ((d : ℝ) * n)) ^ (1 / q)) = r ^ n := by
            dsimp [r]
            rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
              ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
            congr 1
            field_simp [hqpos.ne']
            ring
          rw [← hgeom]
          ring

end SubdiffusiveProcess
