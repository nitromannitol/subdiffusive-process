module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
@[expose] public section

open scoped BigOperators
namespace SubdiffusiveProcess
/-- Compose finitely many radius-dependent energy inequalities. The bound retains the complete product of geometric and multiplicative losses and every nonnegative source term. -/
theorem finite_radius_energy_composition
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (s R E Z A F : ℕ → ℝ)
    (hs : ∀ j ≤ n, 0 < s j)
    (hR : ∀ j < n, 0 < R j)
    (hE : ∀ j ≤ n, 0 ≤ E j)
    (hZ : ∀ j < n, 1 ≤ Z j)
    (hA : ∀ j < n, 1 ≤ A j)
    (hF : ∀ j < n, 0 ≤ F j)
    (hnext : ∀ j < n, s (j + 1) ≤ A j * R j)
    (hstep : ∀ j < n,
      E j ≤ Z j * (((s j / R j) ^ t) * E (j + 1) + (s j) ^ t * F j)) :
    E 0 ≤ (s 0) ^ t * (∏ j ∈ Finset.range n, Z j * (A j) ^ t) *
      (E n / (s n) ^ t + ∑ j ∈ Finset.range n, F j) := by
  induction n generalizing s R E Z A F with
  | zero =>
      have hs0 : 0 < s 0 := hs 0 (by omega)
      have hp0 : 0 < (s 0) ^ t := Real.rpow_pos_of_pos hs0 t
      simp only [Finset.range_zero, Finset.prod_empty, Finset.sum_empty,
        add_zero, mul_one]
      rw [mul_div_cancel₀ (E 0) (ne_of_gt hp0)]
  | succ n ih =>
      have hprefix :
          E 0 ≤ (s 0) ^ t * (∏ j ∈ Finset.range n, Z j * (A j) ^ t) *
            (E n / (s n) ^ t + ∑ j ∈ Finset.range n, F j) :=
        ih s R E Z A F
          (fun j hj => hs j (Nat.le_trans hj (Nat.le_succ n)))
          (fun j hj => hR j (Nat.lt_succ_of_lt hj))
          (fun j hj => hE j (Nat.le_trans hj (Nat.le_succ n)))
          (fun j hj => hZ j (Nat.lt_succ_of_lt hj))
          (fun j hj => hA j (Nat.lt_succ_of_lt hj))
          (fun j hj => hF j (Nat.lt_succ_of_lt hj))
          (fun j hj => hnext j (Nat.lt_succ_of_lt hj))
          (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      have hsn : 0 < s n := hs n (Nat.le_succ n)
      have hsnext : 0 < s (n + 1) := hs (n + 1) (by omega)
      have hRn : 0 < R n := hR n (Nat.lt_succ_self n)
      have hAn : 0 < A n := lt_of_lt_of_le zero_lt_one (hA n (Nat.lt_succ_self n))
      have hZn : 0 ≤ Z n := le_trans zero_le_one (hZ n (Nat.lt_succ_self n))
      have hEnext : 0 ≤ E (n + 1) := hE (n + 1) (by omega)
      have hFn : 0 ≤ F n := hF n (Nat.lt_succ_self n)
      have hpow_s : 0 < (s n) ^ t := Real.rpow_pos_of_pos hsn t
      have hpow_next : 0 < (s (n + 1)) ^ t := Real.rpow_pos_of_pos hsnext t
      have hpow_R : 0 < (R n) ^ t := Real.rpow_pos_of_pos hRn t
      have hpow_A : 1 ≤ (A n) ^ t := by
        simpa using Real.one_le_rpow (hA n (Nat.lt_succ_self n)) ht
      have hscale : (s (n + 1)) ^ t ≤ (A n) ^ t * (R n) ^ t := by
        calc
          (s (n + 1)) ^ t ≤ (A n * R n) ^ t :=
            Real.rpow_le_rpow (le_of_lt hsnext) (hnext n (Nat.lt_succ_self n)) ht
          _ = (A n) ^ t * (R n) ^ t := Real.mul_rpow (le_of_lt hAn) (le_of_lt hRn)
      have hratio : E (n + 1) / (R n) ^ t ≤
          (A n) ^ t * (E (n + 1) / (s (n + 1)) ^ t) := by
        apply (div_le_iff₀ hpow_R).2
        calc
          E (n + 1) = (E (n + 1) / (s (n + 1)) ^ t) * (s (n + 1)) ^ t := by
            field_simp
          _ ≤ (E (n + 1) / (s (n + 1)) ^ t) * ((A n) ^ t * (R n) ^ t) :=
            mul_le_mul_of_nonneg_left hscale (div_nonneg hEnext (le_of_lt hpow_next))
          _ = ((A n) ^ t * (E (n + 1) / (s (n + 1)) ^ t)) * (R n) ^ t := by ring
      have hnormalized : E n / (s n) ^ t ≤
          Z n * ((A n) ^ t * (E (n + 1) / (s (n + 1)) ^ t) + F n) := by
        apply (div_le_iff₀ hpow_s).2
        calc
          E n ≤ Z n * (((s n / R n) ^ t) * E (n + 1) + (s n) ^ t * F n) :=
            hstep n (Nat.lt_succ_self n)
          _ = (s n) ^ t * (Z n * (E (n + 1) / (R n) ^ t + F n)) := by
            rw [Real.div_rpow (le_of_lt hsn) (le_of_lt hRn)]
            field_simp
          _ ≤ (s n) ^ t *
              (Z n * ((A n) ^ t * (E (n + 1) / (s (n + 1)) ^ t) + F n)) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hpow_s)
            apply mul_le_mul_of_nonneg_left _ hZn
            exact add_le_add hratio le_rfl
          _ = (Z n * ((A n) ^ t * (E (n + 1) / (s (n + 1)) ^ t) + F n)) *
              (s n) ^ t := by ring
      have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range n, F j := by
        exact Finset.sum_nonneg fun j hj => hF j (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))
      have hfactor_nonneg :
          0 ≤ (s 0) ^ t * (∏ j ∈ Finset.range n, Z j * (A j) ^ t) := by
        apply mul_nonneg (Real.rpow_nonneg (le_of_lt (hs 0 (by omega))) t)
        apply Finset.prod_nonneg
        intro j hj
        exact mul_nonneg
          (le_trans zero_le_one (hZ j (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))))
          (Real.rpow_nonneg (le_trans zero_le_one (hA j (Nat.lt_succ_of_lt (Finset.mem_range.mp hj)))) t)
      calc
        E 0 ≤ (s 0) ^ t * (∏ j ∈ Finset.range n, Z j * (A j) ^ t) *
            (E n / (s n) ^ t + ∑ j ∈ Finset.range n, F j) := hprefix
        _ ≤ (s 0) ^ t * (∏ j ∈ Finset.range n, Z j * (A j) ^ t) *
            (Z n * ((A n) ^ t * (E (n + 1) / (s (n + 1)) ^ t) + F n) +
              ∑ j ∈ Finset.range n, F j) := by
          gcongr
        _ ≤ (s 0) ^ t * (∏ j ∈ Finset.range n, Z j * (A j) ^ t) *
            ((Z n * (A n) ^ t) *
              (E (n + 1) / (s (n + 1)) ^ t +
                (∑ j ∈ Finset.range n, F j) + F n)) := by
          apply mul_le_mul_of_nonneg_left _ hfactor_nonneg
          have hZone := hZ n (Nat.lt_succ_self n)
          have hc : 1 ≤ Z n * (A n) ^ t :=
            le_trans hZone (by simpa using mul_le_mul_of_nonneg_left hpow_A hZn)
          have hsource : Z n * F n ≤ Z n * (A n) ^ t * F n := by
            calc
              Z n * F n ≤ Z n * ((A n) ^ t * F n) :=
                mul_le_mul_of_nonneg_left (by simpa using mul_le_mul_of_nonneg_right hpow_A hFn) hZn
              _ = Z n * (A n) ^ t * F n := by ring
          have hsum : (∑ j ∈ Finset.range n, F j) ≤
              (Z n * (A n) ^ t) * (∑ j ∈ Finset.range n, F j) :=
            by simpa using mul_le_mul_of_nonneg_right hc hsum_nonneg
          nlinarith
        _ = (s 0) ^ t * (∏ j ∈ Finset.range (n + 1), Z j * (A j) ^ t) *
            (E (n + 1) / (s (n + 1)) ^ t +
              ∑ j ∈ Finset.range (n + 1), F j) := by
          rw [Finset.prod_range_succ, Finset.sum_range_succ]
          ring

end SubdiffusiveProcess
