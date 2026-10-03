module

public import Mathlib
public import Homogenization.Book.Ch02.MultiscaleEllipticity

@[expose] public section




open scoped BigOperators
open Homogenization Homogenization.Book.Ch02

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- `finsetSupReal` of a nonnegative function is nonnegative (including the empty case,
where mathlib's `sSup ∅ = 0`). -/
lemma w19_finsetSupReal_nonneg {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ finsetSupReal s f := by
  classical
  unfold finsetSupReal
  rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · simp [h]
  · exact (hf x).trans
      (le_csSup ((s.finite_toSet.image f).bddAbove) ⟨x, hx, rfl⟩)

lemma w19_maxDescendantBMatrixNormAtScale_nonneg {d : ℕ} (Q : TriadicCube d) (k : ℤ)
    (a : TriadicCoeffFamily d) :
    0 ≤ maxDescendantBMatrixNormAtScale Q k a :=
  w19_finsetSupReal_nonneg _ _ (fun _ => norm_nonneg _)

lemma w19_maxDescendantSigmaStarInvMatrixNormAtScale_nonneg {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) (a : TriadicCoeffFamily d) :
    0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale Q k a :=
  w19_finsetSupReal_nonneg _ _ (fun _ => norm_nonneg _)

/-- `c_{s,q} = 1 - 3^{-sq}` lies in `(0,1]` for positive `s` and `q`. -/
lemma w19_geometricDiscount_pos (s q : ℝ) (hs : 0 < s) (hq : 0 < q) :
    0 < geometricDiscount s q := by
  have h : Real.rpow (3 : ℝ) (-s * q) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
  simpa [geometricDiscount] using h

lemma w19_geometricDiscount_le_one (s q : ℝ) :
    geometricDiscount s q ≤ 1 := by
  have h : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * q) := Real.rpow_nonneg (by norm_num) _
  simp only [geometricDiscount]
  linarith

/-- Termwise comparison of the geometric weights at two orders `s0 ≤ s`. -/
lemma w19_geometricWeight_le (s0 s q : ℝ) (hs0 : 0 < s0) (hq : 0 < q) (hss : s0 ≤ s)
    (n : ℕ) :
    geometricWeight s q n ≤ (geometricDiscount s0 q)⁻¹ * geometricWeight s0 q n := by
  have hc0 : 0 < geometricDiscount s0 q := w19_geometricDiscount_pos s0 q hs0 hq
  have hrw : (geometricDiscount s0 q)⁻¹ * geometricWeight s0 q n =
      Real.rpow (3 : ℝ) (-s0 * q * (n : ℝ)) := by
    simp only [geometricWeight]
    field_simp
  rw [hrw]
  have hexp : -s * q * (n : ℝ) ≤ -s0 * q * (n : ℝ) := by
    have : s0 * q * (n : ℝ) ≤ s * q * (n : ℝ) := by
      have h1 : (0 : ℝ) ≤ q * (n : ℝ) := by positivity
      nlinarith
    linarith
  have hmono : Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) ≤
      Real.rpow (3 : ℝ) (-s0 * q * (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  calc geometricWeight s q n
      = geometricDiscount s q * Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) := rfl
    _ ≤ 1 * Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (w19_geometricDiscount_le_one s q) hnn
    _ = Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) := one_mul _
    _ ≤ Real.rpow (3 : ℝ) (-s0 * q * (n : ℝ)) := hmono

lemma w19_geometricWeight_nonneg (s q : ℝ) (hs : 0 < s) (hq : 0 < q) (n : ℕ) :
    0 ≤ geometricWeight s q n := by
  have hc0 : 0 < geometricDiscount s q := w19_geometricDiscount_pos s q hs hq
  have : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  exact mul_nonneg hc0.le this

/-- Transfer of a weighted discounted sum from order `s0` to any larger order `s`:
the weights only lose the normalizing factor `c_{s0,q}`. -/
lemma w19_tsum_weight_transfer (s0 s q : ℝ) (hs0 : 0 < s0) (hq : 0 < q) (hss : s0 ≤ s)
    (X : ℕ → ℝ) (hX : ∀ n, 0 ≤ X n)
    (hsum : Summable (fun n : ℕ => geometricWeight s0 q n * X n)) :
    (∑' n : ℕ, geometricWeight s q n * X n) ≤
      (geometricDiscount s0 q)⁻¹ * ∑' n : ℕ, geometricWeight s0 q n * X n := by
  have hs : 0 < s := lt_of_lt_of_le hs0 hss
  have hc0 : 0 < geometricDiscount s0 q := w19_geometricDiscount_pos s0 q hs0 hq
  have hterm : ∀ n : ℕ, geometricWeight s q n * X n ≤
      (geometricDiscount s0 q)⁻¹ * (geometricWeight s0 q n * X n) := by
    intro n
    have := w19_geometricWeight_le s0 s q hs0 hq hss n
    calc geometricWeight s q n * X n
        ≤ ((geometricDiscount s0 q)⁻¹ * geometricWeight s0 q n) * X n :=
          mul_le_mul_of_nonneg_right this (hX n)
      _ = (geometricDiscount s0 q)⁻¹ * (geometricWeight s0 q n * X n) := by ring
  have hsum' : Summable (fun n : ℕ =>
      (geometricDiscount s0 q)⁻¹ * (geometricWeight s0 q n * X n)) := hsum.mul_left _
  have hnn : ∀ n : ℕ, 0 ≤ geometricWeight s q n * X n := fun n =>
    mul_nonneg (w19_geometricWeight_nonneg s q hs hq n) (hX n)
  have hLsum : Summable (fun n : ℕ => geometricWeight s q n * X n) :=
    hsum'.of_nonneg_of_le hnn hterm
  calc (∑' n : ℕ, geometricWeight s q n * X n)
      ≤ ∑' n : ℕ, (geometricDiscount s0 q)⁻¹ * (geometricWeight s0 q n * X n) :=
        hLsum.tsum_le_tsum hterm hsum'
    _ = (geometricDiscount s0 q)⁻¹ * ∑' n : ℕ, geometricWeight s0 q n * X n :=
        tsum_mul_left

section Ellipticities

variable {d : ℕ}

/-- The `Λ_{s,q}` summand family is nonnegative. -/
lemma w19_LambdaTerm_nonneg (Q : TriadicCube d) (q : ℝ) (a : TriadicCoeffFamily d)
    (n : ℕ) :
    0 ≤ (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^ (q / 2) :=
  Real.rpow_nonneg (w19_maxDescendantBMatrixNormAtScale_nonneg _ _ _) _

lemma w19_lambdaTerm_nonneg (Q : TriadicCube d) (q : ℝ) (a : TriadicCoeffFamily d)
    (n : ℕ) :
    0 ≤ (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^ (q / 2) :=
  Real.rpow_nonneg (w19_maxDescendantSigmaStarInvMatrixNormAtScale_nonneg _ _ _) _

/-- **Order transfer for `Λ_{s,q}`.**  For `0 < s0 ≤ s` the upper coarse ellipticity at
order `s` is controlled by the one at order `s0`, at the cost of the fixed normalizing
constant `c_{s0,q}^{-2/q}`.  `Λ_{s,q}` is *not* monotone in `s` (the normalization
`1 - 3^{-sq}` grows with `s`), so the constant is genuinely needed. -/
theorem w19_LambdaSqFinite_transfer_order (Q : TriadicCube d) (s0 s q : ℝ)
    (hs0 : 0 < s0) (hq : 0 < q) (hss : s0 ≤ s) (a : TriadicCoeffFamily d)
    (hsum : Summable (fun n : ℕ => geometricWeight s0 q n *
      (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^ (q / 2))) :
    LambdaSqFinite Q s q a ≤
      ((geometricDiscount s0 q)⁻¹) ^ (2 / q) * LambdaSqFinite Q s0 q a := by
  have hc0 : 0 < geometricDiscount s0 q := w19_geometricDiscount_pos s0 q hs0 hq
  set X : ℕ → ℝ := fun n =>
    (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^ (q / 2) with hXdef
  have hX : ∀ n, 0 ≤ X n := fun n => w19_LambdaTerm_nonneg Q q a n
  have hs : 0 < s := lt_of_lt_of_le hs0 hss
  have hSs : 0 ≤ ∑' n : ℕ, geometricWeight s q n * X n :=
    tsum_nonneg fun n => mul_nonneg (w19_geometricWeight_nonneg s q hs hq n) (hX n)
  have hS0 : 0 ≤ ∑' n : ℕ, geometricWeight s0 q n * X n :=
    tsum_nonneg fun n => mul_nonneg (w19_geometricWeight_nonneg s0 q hs0 hq n) (hX n)
  have hmain := w19_tsum_weight_transfer s0 s q hs0 hq hss X hX hsum
  have hexp : (0 : ℝ) ≤ 2 / q := by positivity
  have hgoal : (∑' n : ℕ, geometricWeight s q n * X n) ^ (2 / q) ≤
      ((geometricDiscount s0 q)⁻¹) ^ (2 / q) *
        (∑' n : ℕ, geometricWeight s0 q n * X n) ^ (2 / q) := by
    calc (∑' n : ℕ, geometricWeight s q n * X n) ^ (2 / q)
        ≤ ((geometricDiscount s0 q)⁻¹ * ∑' n : ℕ, geometricWeight s0 q n * X n) ^ (2 / q) :=
          Real.rpow_le_rpow hSs hmain hexp
      _ = ((geometricDiscount s0 q)⁻¹) ^ (2 / q) *
            (∑' n : ℕ, geometricWeight s0 q n * X n) ^ (2 / q) :=
          Real.mul_rpow (by positivity) hS0
  exact hgoal

/-- **Order transfer for `λ_{s,q}^{-1}`.**  Same statement for the reciprocal lower
coarse ellipticity. -/
theorem w19_lambdaSqFinite_inv_transfer_order (Q : TriadicCube d) (s0 s q : ℝ)
    (hs0 : 0 < s0) (hq : 0 < q) (hss : s0 ≤ s) (a : TriadicCoeffFamily d)
    (hsum : Summable (fun n : ℕ => geometricWeight s0 q n *
      (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^ (q / 2))) :
    (lambdaSqFinite Q s q a)⁻¹ ≤
      ((geometricDiscount s0 q)⁻¹) ^ (2 / q) * (lambdaSqFinite Q s0 q a)⁻¹ := by
  have hc0 : 0 < geometricDiscount s0 q := w19_geometricDiscount_pos s0 q hs0 hq
  set X : ℕ → ℝ := fun n =>
    (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^ (q / 2)
    with hXdef
  have hX : ∀ n, 0 ≤ X n := fun n => w19_lambdaTerm_nonneg Q q a n
  have hs : 0 < s := lt_of_lt_of_le hs0 hss
  have hSs : 0 ≤ ∑' n : ℕ, geometricWeight s q n * X n :=
    tsum_nonneg fun n => mul_nonneg (w19_geometricWeight_nonneg s q hs hq n) (hX n)
  have hS0 : 0 ≤ ∑' n : ℕ, geometricWeight s0 q n * X n :=
    tsum_nonneg fun n => mul_nonneg (w19_geometricWeight_nonneg s0 q hs0 hq n) (hX n)
  have hinv : ∀ u : ℝ, 0 ≤ u → (u ^ (-(2 / q)))⁻¹ = u ^ (2 / q) := by
    intro u hu
    rw [Real.rpow_neg hu, inv_inv]
  have hlhs : (lambdaSqFinite Q s q a)⁻¹ =
      (∑' n : ℕ, geometricWeight s q n * X n) ^ (2 / q) := hinv _ hSs
  have hrhs : (lambdaSqFinite Q s0 q a)⁻¹ =
      (∑' n : ℕ, geometricWeight s0 q n * X n) ^ (2 / q) := hinv _ hS0
  have hmain := w19_tsum_weight_transfer s0 s q hs0 hq hss X hX hsum
  have hexp : (0 : ℝ) ≤ 2 / q := by positivity
  rw [hlhs, hrhs]
  calc (∑' n : ℕ, geometricWeight s q n * X n) ^ (2 / q)
      ≤ ((geometricDiscount s0 q)⁻¹ * ∑' n : ℕ, geometricWeight s0 q n * X n) ^ (2 / q) :=
        Real.rpow_le_rpow hSs hmain hexp
    _ = ((geometricDiscount s0 q)⁻¹) ^ (2 / q) *
          (∑' n : ℕ, geometricWeight s0 q n * X n) ^ (2 / q) :=
        Real.mul_rpow (by positivity) hS0

end Ellipticities

section CauchySchwarz

/-- Cauchy--Schwarz for a weighted series with nonnegative weights: the weighted sum of
`U` is square-summable-controlled by the weighted sum of `U ^ 2`. -/
lemma w19_tsum_weighted_cauchy_schwarz (A U : ℕ → ℝ)
    (hA : ∀ n, 0 ≤ A n) (hU : ∀ n, 0 ≤ U n)
    (hsA : Summable A) (hsAU : Summable (fun n => A n * U n ^ 2)) :
    (∑' n : ℕ, A n * U n) ^ 2 ≤ (∑' n : ℕ, A n) * ∑' n : ℕ, A n * U n ^ 2 := by
  classical
  set C : ℝ := (∑' n : ℕ, A n) * ∑' n : ℕ, A n * U n ^ 2 with hC
  have hA' : 0 ≤ ∑' n : ℕ, A n := tsum_nonneg hA
  have hAU2' : 0 ≤ ∑' n : ℕ, A n * U n ^ 2 :=
    tsum_nonneg fun n => mul_nonneg (hA n) (sq_nonneg _)
  have hC0 : 0 ≤ C := mul_nonneg hA' hAU2'
  have hfin : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, A i * U i) ^ 2 ≤ C := by
    intro m
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m)
      (fun i => Real.sqrt (A i)) (fun i => Real.sqrt (A i) * U i)
    have e1 : (∑ i ∈ Finset.range m, Real.sqrt (A i) * (Real.sqrt (A i) * U i)) =
        ∑ i ∈ Finset.range m, A i * U i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, Real.mul_self_sqrt (hA i)]
    have e2 : (∑ i ∈ Finset.range m, Real.sqrt (A i) ^ 2) =
        ∑ i ∈ Finset.range m, A i := by
      refine Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hA i)
    have e3 : (∑ i ∈ Finset.range m, (Real.sqrt (A i) * U i) ^ 2) =
        ∑ i ∈ Finset.range m, A i * U i ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (hA i)]
    rw [e1, e2, e3] at hcs
    refine hcs.trans (mul_le_mul ?_ ?_ (Finset.sum_nonneg fun i _ =>
      mul_nonneg (hA i) (sq_nonneg _)) hA')
    · exact hsA.sum_le_tsum _ (fun i _ => hA i)
    · exact hsAU.sum_le_tsum _ (fun i _ => mul_nonneg (hA i) (sq_nonneg _))
  have hpart : ∀ m : ℕ, (∑ i ∈ Finset.range m, A i * U i) ≤ Real.sqrt C := by
    intro m
    have hnn : 0 ≤ ∑ i ∈ Finset.range m, A i * U i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hA i) (hU i)
    have h := Real.sqrt_le_sqrt (hfin m)
    rwa [Real.sqrt_sq hnn] at h
  have htsum : (∑' n : ℕ, A n * U n) ≤ Real.sqrt C :=
    Real.tsum_le_of_sum_range_le (fun n => mul_nonneg (hA n) (hU n)) hpart
  have hnn : 0 ≤ ∑' n : ℕ, A n * U n :=
    tsum_nonneg fun n => mul_nonneg (hA n) (hU n)
  have := mul_self_le_mul_self hnn htsum
  calc (∑' n : ℕ, A n * U n) ^ 2
      = (∑' n : ℕ, A n * U n) * (∑' n : ℕ, A n * U n) := sq _
    _ ≤ Real.sqrt C * Real.sqrt C := this
    _ = C := Real.mul_self_sqrt hC0

end CauchySchwarz

section OrderExchange

/-- Geometric-weight Cauchy--Schwarz in normalized form: with the normalizing constant
`1 - r` the squared weighted sum of `X` is dominated by the weighted sum of `X ^ 2`. -/
lemma w19_geometric_cs (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (X : ℕ → ℝ)
    (hX : ∀ n, 0 ≤ X n) (hsum : Summable (fun n : ℕ => r ^ n * X n ^ 2)) :
    ((1 - r) * ∑' n : ℕ, r ^ n * X n) ^ 2 ≤ (1 - r) * ∑' n : ℕ, r ^ n * X n ^ 2 := by
  have hc0 : 0 < 1 - r := by linarith
  have hsumA : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hcs := w19_tsum_weighted_cauchy_schwarz (fun n : ℕ => r ^ n) X
    (fun n => pow_nonneg hr0 n) hX hsumA hsum
  rw [tsum_geometric_of_lt_one hr0 hr1] at hcs
  calc ((1 - r) * ∑' n : ℕ, r ^ n * X n) ^ 2
      = (1 - r) ^ 2 * (∑' n : ℕ, r ^ n * X n) ^ 2 := by ring
    _ ≤ (1 - r) ^ 2 * ((1 - r)⁻¹ * ∑' n : ℕ, r ^ n * X n ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = (1 - r) * ∑' n : ℕ, r ^ n * X n ^ 2 := by
        field_simp

/-- The discounted sums defining `Λ_{s,q}` and `λ_{s,q}^{-1}` are nonnegative. -/
lemma w19_discounted_sum_nonneg (sigma q : ℝ) (hs : 0 < sigma) (hq : 0 < q)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) :
    0 ≤ ∑' n : ℕ, geometricWeight sigma q n * B n ^ (q / 2) :=
  tsum_nonneg fun n =>
    mul_nonneg (w19_geometricWeight_nonneg sigma q hs hq n) (Real.rpow_nonneg (hB n) _)

/-- The abstract `q = 1 → q = 2` exchange between the two discounted sums, with the
discount halved and no constant. -/
lemma w19_discounted_one_le_two (s : ℝ) (hs : 0 < s) (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hsum : Summable (fun n : ℕ =>
      geometricWeight (s / 2) 2 n * B n ^ ((2 : ℝ) / 2))) :
    (∑' n : ℕ, geometricWeight s 1 n * B n ^ ((1 : ℝ) / 2)) ^ ((2 : ℝ) / 1) ≤
      (∑' n : ℕ, geometricWeight (s / 2) 2 n * B n ^ ((2 : ℝ) / 2)) ^ ((2 : ℝ) / 2) := by
  classical
  set X : ℕ → ℝ := fun n => B n ^ ((1 : ℝ) / 2) with hXdef
  have hX : ∀ n, 0 ≤ X n := fun n => Real.rpow_nonneg (hB n) _
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-s) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hc0 : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by linarith
  have hXsq : ∀ n : ℕ, X n ^ 2 = B n ^ ((2 : ℝ) / 2) := by
    intro n
    have hxn : X n = B n ^ ((1 : ℝ) / 2) := rfl
    rw [hxn, ← Real.rpow_natCast (B n ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul (hB n)]
    norm_num
  have hexp1 : ∀ n : ℕ, (3 : ℝ) ^ (-s * 1 * (n : ℝ)) = ((3 : ℝ) ^ (-s)) ^ n := by
    intro n
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-s)) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hexp2 : ∀ n : ℕ, (3 : ℝ) ^ (-(s / 2) * 2 * (n : ℝ)) = ((3 : ℝ) ^ (-s)) ^ n := by
    intro n
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-s)) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      show (-(s / 2) * 2 * (n : ℝ)) = -s * (n : ℝ) by ring]
  have hd1 : (1 : ℝ) - (3 : ℝ) ^ (-s * 1) = 1 - (3 : ℝ) ^ (-s) := by
    rw [show (-s * 1 : ℝ) = -s by ring]
  have hd2 : (1 : ℝ) - (3 : ℝ) ^ (-(s / 2) * 2) = 1 - (3 : ℝ) ^ (-s) := by
    rw [show (-(s / 2) * 2 : ℝ) = -s by ring]
  have hw1 : ∀ n : ℕ, geometricWeight s 1 n * B n ^ ((1 : ℝ) / 2) =
      (1 - (3 : ℝ) ^ (-s)) * (((3 : ℝ) ^ (-s)) ^ n * X n) := by
    intro n
    show ((1 : ℝ) - (3 : ℝ) ^ (-s * 1)) * (3 : ℝ) ^ (-s * 1 * (n : ℝ)) *
      B n ^ ((1 : ℝ) / 2) = _
    rw [hd1, hexp1 n]
    have hxn : X n = B n ^ ((1 : ℝ) / 2) := rfl
    rw [hxn]
    ring
  have hw2 : ∀ n : ℕ, geometricWeight (s / 2) 2 n * B n ^ ((2 : ℝ) / 2) =
      (1 - (3 : ℝ) ^ (-s)) * (((3 : ℝ) ^ (-s)) ^ n * X n ^ 2) := by
    intro n
    show ((1 : ℝ) - (3 : ℝ) ^ (-(s / 2) * 2)) *
      (3 : ℝ) ^ (-(s / 2) * 2 * (n : ℝ)) * B n ^ ((2 : ℝ) / 2) = _
    rw [hd2, hexp2 n, hXsq n]
    ring
  have hsum' : Summable (fun n : ℕ => ((3 : ℝ) ^ (-s)) ^ n * X n ^ 2) := by
    have h := hsum.mul_left (1 - (3 : ℝ) ^ (-s))⁻¹
    refine h.congr ?_
    intro n
    rw [hw2 n]
    field_simp
  have hS1 : (∑' n : ℕ, geometricWeight s 1 n * B n ^ ((1 : ℝ) / 2)) =
      (1 - (3 : ℝ) ^ (-s)) * ∑' n : ℕ, ((3 : ℝ) ^ (-s)) ^ n * X n := by
    rw [tsum_congr hw1, tsum_mul_left]
  have hS2 : (∑' n : ℕ, geometricWeight (s / 2) 2 n * B n ^ ((2 : ℝ) / 2)) =
      (1 - (3 : ℝ) ^ (-s)) * ∑' n : ℕ, ((3 : ℝ) ^ (-s)) ^ n * X n ^ 2 := by
    rw [tsum_congr hw2, tsum_mul_left]
  rw [hS1, hS2, show ((2 : ℝ) / 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    show ((2 : ℝ) / 2) = (1 : ℝ) by norm_num, Real.rpow_one]
  exact w19_geometric_cs ((3 : ℝ) ^ (-s)) hr0 hr1 X hX hsum'

variable {d : ℕ}

/-- **Exponent transfer `q = 1 → q = 2`** for the upper coarse ellipticity.  This is the
paper's step "for `q = 1` weighted Cauchy--Schwarz bounds the squared sum of square-root
matrices by this sum of matrices" in the proof of `mfd:lem-as-coarse`: the discount is
halved and there is *no* constant, `Λ_{s,1} ≤ Λ_{s/2,2}`. -/
theorem w19_LambdaSqFinite_one_le_two (Q : TriadicCube d) (s : ℝ) (hs : 0 < s)
    (a : TriadicCoeffFamily d)
    (hsum : Summable (fun n : ℕ => geometricWeight (s / 2) 2 n *
      (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^ ((2 : ℝ) / 2))) :
    LambdaSqFinite Q s 1 a ≤ LambdaSqFinite Q (s / 2) 2 a :=
  w19_discounted_one_le_two s hs
    (fun n => maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
    (fun _ => w19_maxDescendantBMatrixNormAtScale_nonneg _ _ _) hsum

/-- **Exponent transfer `q = 1 → q = 2`** for the reciprocal lower coarse ellipticity. -/
theorem w19_lambdaSqFinite_inv_one_le_two (Q : TriadicCube d) (s : ℝ) (hs : 0 < s)
    (a : TriadicCoeffFamily d)
    (hsum : Summable (fun n : ℕ => geometricWeight (s / 2) 2 n *
      (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^
        ((2 : ℝ) / 2))) :
    (lambdaSqFinite Q s 1 a)⁻¹ ≤ (lambdaSqFinite Q (s / 2) 2 a)⁻¹ := by
  have hB : ∀ n : ℕ,
      0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    fun _ => w19_maxDescendantSigmaStarInvMatrixNormAtScale_nonneg _ _ _
  have hinv : ∀ u y : ℝ, 0 ≤ u → (u ^ (-y))⁻¹ = u ^ y := by
    intro u y hu
    rw [Real.rpow_neg hu, inv_inv]
  have hS1 := w19_discounted_sum_nonneg s 1 hs one_pos
    (fun n => maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) hB
  have hS2 := w19_discounted_sum_nonneg (s / 2) 2 (by linarith) two_pos
    (fun n => maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) hB
  have hL1 : (lambdaSqFinite Q s 1 a)⁻¹ =
      (∑' n : ℕ, geometricWeight s 1 n *
        (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^
          ((1 : ℝ) / 2)) ^ ((2 : ℝ) / 1) := hinv _ _ hS1
  have hL2 : (lambdaSqFinite Q (s / 2) 2 a)⁻¹ =
      (∑' n : ℕ, geometricWeight (s / 2) 2 n *
        (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^
          ((2 : ℝ) / 2)) ^ ((2 : ℝ) / 2) := hinv _ _ hS2
  rw [hL1, hL2]
  exact w19_discounted_one_le_two s hs
    (fun n => maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) hB hsum

end OrderExchange

section Summability

variable {d : ℕ}

/-- In `ℝ` a nonzero `tsum` forces summability (mathlib sends a divergent series to `0`). -/
lemma w19_summable_of_tsum_ne_zero {X : ℕ → ℝ} (h : (∑' n : ℕ, X n) ≠ 0) :
    Summable X := by
  by_contra hc
  exact h (tsum_eq_zero_of_not_summable hc)

/-- Positivity of `Λ_{s,q}` (which `in_J.Lam_pos` asserts and `in_J.Lam_eq` transports to
this carrier) already supplies the summability that the order/exponent transfer lemmas
need.  Without it `Λ_{s,q}` would be mathlib's junk value `0` on divergent data. -/
lemma w19_summable_of_LambdaSqFinite_pos (Q : TriadicCube d) (s q : ℝ) (hq : 0 < q)
    (a : TriadicCoeffFamily d) (hpos : 0 < LambdaSqFinite Q s q a) :
    Summable (fun n : ℕ => geometricWeight s q n *
      (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^ (q / 2)) := by
  refine w19_summable_of_tsum_ne_zero ?_
  intro h0
  have hz : LambdaSqFinite Q s q a = (0 : ℝ) ^ ((2 : ℝ) / q) := by
    show (∑' n : ℕ, geometricWeight s q n *
      (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^ (q / 2)) ^
      ((2 : ℝ) / q) = _
    rw [h0]
  rw [Real.zero_rpow (by positivity)] at hz
  exact absurd hz (ne_of_gt hpos)

/-- The same for `λ_{s,q}`, from `in_J.lam_pos`. -/
lemma w19_summable_of_lambdaSqFinite_pos (Q : TriadicCube d) (s q : ℝ) (hq : 0 < q)
    (a : TriadicCoeffFamily d) (hpos : 0 < lambdaSqFinite Q s q a) :
    Summable (fun n : ℕ => geometricWeight s q n *
      (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^ (q / 2)) := by
  refine w19_summable_of_tsum_ne_zero ?_
  intro h0
  have hz : lambdaSqFinite Q s q a = (0 : ℝ) ^ (-((2 : ℝ) / q)) := by
    show (∑' n : ℕ, geometricWeight s q n *
      (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^ (q / 2)) ^
      (-((2 : ℝ) / q)) = _
    rw [h0]
  rw [Real.zero_rpow (neg_ne_zero.mpr (by positivity))] at hz
  exact absurd hz (ne_of_gt hpos)

end Summability

end Paper
