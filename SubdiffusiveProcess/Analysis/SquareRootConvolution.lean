module

public import SubdiffusiveProcess.Analysis.GeometricConvolution
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-! # Square-root comparison of full nonnegative convolutions

Finite square-root subadditivity passes through convergent nonnegative sums.
The resulting geometric convolution uses the square roots of the original
ratio and prefactor. Bounds justify every sum; no tail is discarded.
-/
noncomputable section
namespace SubdiffusiveProcess

/-- Square root is subadditive on nonnegative real inputs. -/
theorem sqrt_add_le_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x+y) ≤ Real.sqrt x + Real.sqrt y := by
  apply Real.sqrt_le_iff.2
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- Finite square-root subadditivity with the original nonnegative summands. -/
theorem sqrt_sum_le_sum_sqrt {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) : Real.sqrt (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Real.sqrt_zero, le_refl]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (sqrt_add_le_of_nonneg (hf i) (Finset.sum_nonneg fun j _ => hf j)).trans
      (add_le_add le_rfl ih)

/-- Full square-root subadditivity follows by continuity from finite sums. -/
theorem sqrt_tsum_le_tsum_sqrt {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hs : Summable f) (hr : Summable (fun n => Real.sqrt (f n))) :
    Real.sqrt (∑' n, f n) ≤ ∑' n, Real.sqrt (f n) :=
  le_of_tendsto_of_tendsto
    (Real.continuous_sqrt.continuousAt.tendsto.comp hs.hasSum.tendsto_sum_nat)
    hr.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall fun n => sqrt_sum_le_sum_sqrt (Finset.range n) hf)

/-- Square root commutes with natural powers of a nonnegative real. -/
theorem sqrt_nat_pow {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    Real.sqrt (q^n) = (Real.sqrt q)^n := by
  induction n with
  | zero => simp only [pow_zero, Real.sqrt_one]
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hq n), ih, pow_succ]

/-- Taking square roots preserves a strict geometric discount. -/
theorem sqrt_lt_one_of_nonneg {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Real.sqrt q < 1 := by
  nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q]

/-- The square roots of a bounded nonnegative geometric sequence are summable. -/
theorem geometric_sqrt_summable {A : ℕ → ℝ} {K q : ℝ}
    (hK : ∀ n, A n ≤ K) (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n => Real.sqrt (q^n * A n)) := by
  have h := geometric_weight_summable (fun n => Real.sqrt_nonneg (A n))
    (fun n => Real.sqrt_le_sqrt (hK n)) (Real.sqrt_nonneg q) (sqrt_lt_one_of_nonneg hq hq1)
  simpa only [Real.sqrt_mul (pow_nonneg hq _), sqrt_nat_pow hq] using h

/-- Taking square roots of a forward convolution preserves its full tail. -/
theorem sqrt_forward_convolution_le {A B : ℕ → ℝ} {K C q : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hK : ∀ n, A n ≤ K) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hconv : ∀ n, B n ≤ A n + C * ∑' j, q^j * A (n+j+1)) (n : ℕ) :
    Real.sqrt (B n) ≤ Real.sqrt (A n) + Real.sqrt C *
      ∑' j, (Real.sqrt q)^j * Real.sqrt (A (n+j+1)) := by
  have hterms : ∀ j, 0 ≤ q^j * A (n+j+1) :=
    fun j => mul_nonneg (pow_nonneg hq j) (hA _)
  have hs := geometric_weight_summable (fun j => hA (n+j+1))
    (fun j => hK (n+j+1)) hq hq1
  have hr := geometric_sqrt_summable (fun j => hK (n+j+1)) hq hq1
  calc
    Real.sqrt (B n) ≤ Real.sqrt (A n + C * ∑' j, q^j * A (n+j+1)) :=
      Real.sqrt_le_sqrt (hconv n)
    _ ≤ Real.sqrt (A n) + Real.sqrt (C * ∑' j, q^j * A (n+j+1)) :=
      sqrt_add_le_of_nonneg (hA n) (mul_nonneg hC (tsum_nonneg hterms))
    _ = Real.sqrt (A n) + Real.sqrt C * Real.sqrt (∑' j, q^j * A (n+j+1)) := by
      rw [Real.sqrt_mul hC]
    _ ≤ Real.sqrt (A n) + Real.sqrt C * (∑' j, Real.sqrt (q^j * A (n+j+1))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (sqrt_tsum_le_tsum_sqrt hterms hs hr)
        (Real.sqrt_nonneg C))
    _ = _ := by simp only [Real.sqrt_mul (pow_nonneg hq _), sqrt_nat_pow hq]

/-- The square-root discounted convolution has the corresponding exact constant. -/
theorem sqrt_convolution_discount_le {A B : ℕ → ℝ} {K L C q t : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hK : ∀ n, A n ≤ K)
    (hL : ∀ n, B n ≤ L) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hqt : Real.sqrt q < t) (ht1 : t < 1)
    (hconv : ∀ n, B n ≤ A n + C * ∑' j, q^j * A (n+j+1)) :
    (∑' n, t^n * Real.sqrt (B n)) ≤
      (1 + Real.sqrt C/(t-Real.sqrt q)) * ∑' n, t^n * Real.sqrt (A n) := by
  have hq1 : q < 1 := by
    have h := hqt.trans ht1
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q]
  exact geometric_convolution_discount_le (fun n => Real.sqrt_nonneg (A n))
    (fun n => Real.sqrt_le_sqrt (hK n)) (fun n => Real.sqrt_nonneg (B n))
    (fun n => Real.sqrt_le_sqrt (hL n)) (Real.sqrt_nonneg C) (Real.sqrt_nonneg q) hqt ht1
    (sqrt_forward_convolution_le hA hK hC hq hq1 hconv)

end SubdiffusiveProcess
