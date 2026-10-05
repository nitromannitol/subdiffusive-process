module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-! # Full discounted forward convolutions

A bounded nonnegative sequence has every strictly discounted geometric sum.
The forward shift loses exactly the corresponding inverse discount. These
facts justify the full double sum, before evaluating its geometric constant.
-/
open Filter
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess

/-- A fixed bound supplies summability at any strictly positive geometric discount. -/
theorem geometric_weight_summable {A : ℕ → ℝ} {K t : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hK : ∀ n, A n ≤ K) (ht : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun n => t^n * A n) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg ht _) (hA n))
    (fun n => mul_le_mul_of_nonneg_left (hK n) (pow_nonneg ht _))
    ((summable_geometric_of_lt_one ht ht1).mul_right K)

/-- The full weighted shifted sum is bounded by the original sum divided by the shift discount. -/
theorem geometric_weight_shift_le {A : ℕ → ℝ} {K t : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hK : ∀ n, A n ≤ K) (ht : 0 < t) (ht1 : t < 1) (k : ℕ) :
    (∑' n, t^n * A (n+k)) ≤ (∑' n, t^n * A n) / t^k := by
  have hsum := geometric_weight_summable hA hK ht.le ht1
  apply (le_div_iff₀ (pow_pos ht k)).2
  calc
    (∑' n, t^n * A (n+k)) * t^k = ∑' n, t^(n+k) * A (n+k) := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro n
      rw [pow_add]
      ring
    _ ≤ ∑' n, t^n * A n := by
      have he := hsum.sum_add_tsum_nat_add k
      have hn : 0 ≤ ∑ i ∈ Finset.range k, t^i * A i :=
        Finset.sum_nonneg fun i _ => mul_nonneg (pow_nonneg ht.le _) (hA i)
      linarith

/-- The two geometric weights make the actual forward double convolution summable. -/
theorem geometric_forward_double_summable {A : ℕ → ℝ} {K q t : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hK : ∀ n, A n ≤ K)
    (hq : 0 ≤ q) (hq1 : q < 1) (ht : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun p : ℕ × ℕ => t^p.1 * q^p.2 * A (p.1+p.2+1)) := by
  have hb : Summable (fun p : ℕ × ℕ => (t^p.1 * q^p.2) * K) := by
    exact ((summable_geometric_of_lt_one ht ht1).mul_of_nonneg
      (summable_geometric_of_lt_one hq hq1)
      (fun n => pow_nonneg ht n) (fun n => pow_nonneg hq n)).mul_right K
  exact Summable.of_nonneg_of_le
    (fun p => mul_nonneg (mul_nonneg (pow_nonneg ht _) (pow_nonneg hq _)) (hA _))
    (fun p => mul_le_mul_of_nonneg_left (hK _) (mul_nonneg (pow_nonneg ht _) (pow_nonneg hq _))) hb

/-- The discounted sum of the forward convolution has the exact geometric upper constant. -/
theorem geometric_forward_tsum_le {A : ℕ → ℝ} {K q t : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hK : ∀ n, A n ≤ K)
    (hq : 0 ≤ q) (hqt : q < t) (ht1 : t < 1) :
    (∑' n, t^n * ∑' j, q^j * A (n+j+1)) ≤
      (∑' n, t^n * A n) / (t-q) := by
  have ht : 0 < t := lt_of_le_of_lt hq hqt
  have hq1 : q < 1 := hqt.trans ht1
  have hd := geometric_forward_double_summable hA hK hq hq1 ht.le ht1
  let S := ∑' n, t^n * A n
  have hgeom := summable_geometric_of_lt_one (div_nonneg hq ht.le)
    ((div_lt_one ht).2 hqt)
  have hbound : Summable (fun j : ℕ => q^j * (S / t^(j+1))) := by
    convert hgeom.mul_right (S/t) using 1
    funext j
    rw [div_pow, pow_succ]
    field_simp
  calc
    (∑' n, t^n * ∑' j, q^j * A (n+j+1)) =
        ∑' j, q^j * ∑' n, t^n * A (n+j+1) := by
      have he := Summable.tsum_comm (f := fun n j : ℕ => t^n * q^j * A (n+j+1)) hd
      calc
        _ = ∑' n, ∑' j, t^n * q^j * A (n+j+1) := by
          simp only [← tsum_mul_left, mul_assoc]
        _ = ∑' j, ∑' n, t^n * q^j * A (n+j+1) := he.symm
        _ = _ := by simp only [← tsum_mul_left, mul_assoc, mul_left_comm]
    _ ≤ ∑' j, q^j * (S / t^(j+1)) := by
      apply Summable.tsum_le_tsum
      · intro j
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Nat.add_assoc] using geometric_weight_shift_le hA hK ht ht1 (j+1))
          (pow_nonneg hq j)
      · have he := hd.prod_symm.prod
        simpa only [Prod.fst_swap, Prod.snd_swap, ← tsum_mul_left, mul_assoc, mul_left_comm] using he
      · exact hbound
    _ = S / (t-q) := by
      have he : (fun j : ℕ => q^j * (S / t^(j+1))) = (fun j => (q/t)^j * (S/t)) := by
        funext j
        rw [div_pow, pow_succ]
        field_simp
      rw [he, tsum_mul_right, tsum_geometric_of_lt_one (div_nonneg hq ht.le)
        ((div_lt_one ht).2 hqt)]
      field_simp

/-- A pointwise forward convolution gives a full discounted comparison. -/
theorem geometric_convolution_discount_le {A B : ℕ → ℝ} {K L C q t : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hK : ∀ n, A n ≤ K)
    (hB : ∀ n, 0 ≤ B n) (hL : ∀ n, B n ≤ L)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hqt : q < t) (ht1 : t < 1)
    (hconv : ∀ n, B n ≤ A n + C * ∑' j, q^j * A (n+j+1)) :
    (∑' n, t^n * B n) ≤ (1 + C/(t-q)) * ∑' n, t^n * A n := by
  have ht : 0 < t := lt_of_le_of_lt hq hqt
  have ha := geometric_weight_summable hA hK ht.le ht1
  have hb := geometric_weight_summable hB hL ht.le ht1
  have hd := geometric_forward_double_summable hA hK hq (hqt.trans ht1) ht.le ht1
  have he : Summable (fun n => t^n * ∑' j, q^j * A (n+j+1)) := by
    simpa only [← tsum_mul_left, mul_assoc] using hd.prod
  calc
    (∑' n, t^n * B n) ≤ ∑' n, (t^n * A n + C * (t^n * ∑' j, q^j * A (n+j+1))) := by
      apply Summable.tsum_le_tsum _ hb (ha.add (he.mul_left C))
      intro n
      have h := mul_le_mul_of_nonneg_left (hconv n) (pow_nonneg ht.le n)
      nlinarith only [h]
    _ = (∑' n, t^n * A n) + C * ∑' n, t^n * ∑' j, q^j * A (n+j+1) := by
      rw [ha.tsum_add (he.mul_left C), tsum_mul_left]
    _ ≤ (∑' n, t^n * A n) + C * ((∑' n, t^n * A n) / (t-q)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (geometric_forward_tsum_le hA hK hq hqt ht1) hC)
    _ = _ := by ring

/-- A large limit forces a large base value or a dyadic approximation increment. -/
theorem exists_large_increment_of_tendsto
    {u : ℕ → ℝ} {z : ℝ}
    (hu : Tendsto u atTop (𝓝 z)) (hz : (1 : ℝ) / 2 < z) :
    (1 : ℝ) / 4 < u 0 ∨ ∃ n : ℕ,
      ((1 : ℝ) / 2) ^ (n + 4) < u (n + 1) - u n := by
  by_contra h
  push Not at h
  have htel : ∀ n : ℕ,
      u n ≤ u 0 + ∑ i ∈ Finset.range n, ((1 : ℝ) / 2) ^ (i + 4) := by
    intro n
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero, le_refl]
    | succ n ih =>
        rw [Finset.sum_range_succ]
        linarith [h.2 n]
  have hsum : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, ((1 : ℝ) / 2) ^ (i + 4)) ≤ (1 : ℝ) / 8 := by
    intro n
    rw [show (∑ i ∈ Finset.range n, ((1 : ℝ) / 2) ^ (i + 4)) =
        ((1 : ℝ) / 2) ^ 4 * ∑ i ∈ Finset.range n, ((1 : ℝ) / 2) ^ i by
      calc
        _ = ∑ i ∈ Finset.range n,
              ((1 : ℝ) / 2) ^ 4 * ((1 : ℝ) / 2) ^ i := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [pow_add, mul_comm]
        _ = _ := by rw [Finset.mul_sum]]
    norm_num
    linarith [sum_geometric_two_le n]
  have hub : ∀ n : ℕ, u n ≤ (3 : ℝ) / 8 := by
    intro n
    linarith [htel n, hsum n, h.1]
  have hzle : z ≤ (3 : ℝ) / 8 :=
    le_of_tendsto hu (Eventually.of_forall hub)
  linarith

end SubdiffusiveProcess
