module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess.FractionalEmbedding

/-- The natural dyadic levels above a positive initial threshold. -/
def levelScale (t : ℝ) (k : ℕ) : ℝ := t * 2 ^ k

/-- Constant in the scalar recurrence for dyadic distribution functions. -/
def dyadicStepConstant (β : ℝ) : ℝ := ((1 / 8 : ℝ) ^ (1 / β)) ^ (β - 1)

theorem levelScale_pos {t : ℝ} (ht : 0 < t) (k : ℕ) : 0 < levelScale t k := by
  exact mul_pos ht (pow_pos (by norm_num) k)

theorem levelScale_succ (t : ℝ) (k : ℕ) : levelScale t (k + 1) = 2 * levelScale t k := by
  unfold levelScale
  rw [pow_succ]
  ring

theorem levelScale_sq (t : ℝ) (k : ℕ) : (levelScale t k) ^ 2 = t ^ 2 * 4 ^ k := by
  unfold levelScale
  rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
  norm_num

theorem dyadicStepConstant_pos (β : ℝ) : 0 < dyadicStepConstant β := by
  exact Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _

/-- A pointwise alternative to the Holder step of DNPV Lemma 6.2. -/
theorem dyadic_mass_step {β a b : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hb : 0 ≤ b) (hba : b ≤ a) :
    b ^ β ≤ a ^ β / 8 + dyadicStepConstant β * b * a ^ (β - 1) := by
  have ha : 0 ≤ a := hb.trans hba
  by_cases ha0 : a = 0
  · have hb0 : b = 0 := le_antisymm (ha0 ▸ hba) hb
    subst a
    subst b
    simp only [Real.zero_rpow hβ.ne', zero_div, mul_zero, zero_mul, zero_add, le_refl]
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  let δ : ℝ := (1 / 8 : ℝ) ^ (1 / β)
  have hδ : 0 < δ := Real.rpow_pos_of_pos (by norm_num) _
  have hδβ : δ ^ β = 1 / 8 := by
    dsimp only [δ]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
    rw [div_mul_cancel₀ _ hβ.ne', Real.rpow_one]
  have hD : 0 ≤ dyadicStepConstant β * b * a ^ (β - 1) :=
    mul_nonneg (mul_nonneg (dyadicStepConstant_pos β).le hb) (Real.rpow_nonneg ha _)
  by_cases hsmall : b ≤ δ * a
  · have hle := Real.rpow_le_rpow hb hsmall hβ.le
    rw [Real.mul_rpow hδ.le ha, hδβ] at hle
    linarith
  · have hlarge : δ * a ≤ b := (lt_of_not_ge hsmall).le
    have hbPos : 0 < b := lt_of_lt_of_le (mul_pos hδ haPos) hlarge
    have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hδ haPos) hlarge
      (show β - 1 ≤ 0 by linarith)
    have hbId : b ^ β = b * b ^ (β - 1) := by
      calc
        b ^ β = b ^ ((β - 1) + 1) := by congr 1; ring
        _ = b ^ (β - 1) * b := Real.rpow_add_one hbPos.ne' (β - 1)
        _ = b * b ^ (β - 1) := mul_comm _ _
    rw [Real.mul_rpow hδ.le ha] at hpow
    have hle : b ^ β ≤ dyadicStepConstant β * b * a ^ (β - 1) := by
      rw [hbId]
      simpa only [dyadicStepConstant, δ, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left hpow hb
    exact hle.trans (le_add_of_nonneg_left (div_nonneg (Real.rpow_nonneg ha _) (by norm_num)))

/-- The finite, natural-index distribution recurrence; its initial term is retained. -/
theorem dyadic_mass_sum {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hmono : ∀ k, a (k + 1) ≤ a k) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (4 : ℝ) ^ k * (a k) ^ β) ≤
      2 * (a 0) ^ β + 8 * dyadicStepConstant β *
        ∑ k ∈ Finset.range N, (4 : ℝ) ^ k * a (k + 1) * (a k) ^ (β - 1) := by
  have hstep : (∑ k ∈ Finset.range N, (4 : ℝ) ^ k * (a (k + 1)) ^ β) ≤
      (∑ k ∈ Finset.range N, (4 : ℝ) ^ k * (a k) ^ β) / 8 +
        dyadicStepConstant β *
          ∑ k ∈ Finset.range N, (4 : ℝ) ^ k * a (k + 1) * (a k) ^ (β - 1) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, (4 : ℝ) ^ k *
          ((a k) ^ β / 8 + dyadicStepConstant β * a (k + 1) * (a k) ^ (β - 1)) := by
        exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (dyadic_mass_step hβ hβ1 (ha (k + 1)) (hmono k)) (by positivity)
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← mul_div_assoc, ← Finset.sum_div]
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hhead : (∑ k ∈ Finset.range (N + 1), (4 : ℝ) ^ k * (a k) ^ β) =
      (a 0) ^ β + 4 * ∑ k ∈ Finset.range N, (4 : ℝ) ^ k * (a (k + 1)) ^ β := by
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, pow_succ, Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have htail : (∑ k ∈ Finset.range N, (4 : ℝ) ^ k * (a k) ^ β) ≤
      ∑ k ∈ Finset.range (N + 1), (4 : ℝ) ^ k * (a k) ^ β := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (Real.rpow_nonneg (ha N) _))
  have hdiv : (∑ k ∈ Finset.range N, (4 : ℝ) ^ k * (a k) ^ β) / 8 ≤
      (∑ k ∈ Finset.range (N + 1), (4 : ℝ) ^ k * (a k) ^ β) / 8 :=
    div_le_div_of_nonneg_right htail (by norm_num)
  have h := hstep.trans (add_le_add hdiv le_rfl)
  linarith

theorem geometric_four_sum (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (4 : ℝ) ^ k) ≤ (4 / 3 : ℝ) * 4 ^ N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) N]

/-- Summing the separated-pair weights costs only a geometric-series constant. -/
theorem pair_level_sum (t a b : ℝ) (ht : 0 < t) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      if 2 * levelScale t k < a ∧ b ≤ levelScale t k then (levelScale t k) ^ 2 else 0) ≤
      (4 / 3 : ℝ) * (a - b) ^ 2 := by
  have hfull (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1),
        if 2 * levelScale t k < a ∧ b ≤ levelScale t k then (levelScale t k) ^ 2 else 0) ≤
      (4 / 3 : ℝ) * (levelScale t n) ^ 2 := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n + 1), (levelScale t k) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        split_ifs
        · exact le_rfl
        · exact sq_nonneg _
      _ = t ^ 2 * ∑ k ∈ Finset.range (n + 1), (4 : ℝ) ^ k := by
        simp only [levelScale_sq, Finset.mul_sum]
      _ ≤ t ^ 2 * ((4 / 3 : ℝ) * 4 ^ n) :=
        mul_le_mul_of_nonneg_left (geometric_four_sum n) (sq_nonneg _)
      _ = _ := by rw [levelScale_sq]; ring
  induction N with
  | zero =>
    by_cases h : 2 * levelScale t 0 < a ∧ b ≤ levelScale t 0
    · have hpos := levelScale_pos ht 0
      have hsquare : (levelScale t 0) ^ 2 ≤ (a - b) ^ 2 := by nlinarith [h.1, h.2]
      exact (hfull 0).trans (mul_le_mul_of_nonneg_left hsquare (by norm_num))
    · norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ite_eq_right h]
      positivity
  | succ N ih =>
    by_cases h : 2 * levelScale t (N + 1) < a ∧ b ≤ levelScale t (N + 1)
    · have hpos := levelScale_pos ht (N + 1)
      have hsquare : (levelScale t (N + 1)) ^ 2 ≤ (a - b) ^ 2 := by nlinarith [h.1, h.2]
      exact (hfull (N + 1)).trans (mul_le_mul_of_nonneg_left hsquare (by norm_num))
    · rw [Finset.sum_range_succ, ite_eq_right h, add_zero]
      exact ih

/-- A truncated moment is controlled by finitely many upper-level indicators. -/
theorem truncated_rpow_le_dyadic (t a q : ℝ) (ht : 0 < t) (ha : 0 ≤ a)
    (hq : 0 ≤ q) (N : ℕ) :
    (min a (levelScale t (N + 1))) ^ q ≤ t ^ q +
      ∑ k ∈ Finset.range (N + 1),
        if levelScale t k < a then (levelScale t (k + 1)) ^ q else 0 := by
  have hterm (k : ℕ) : 0 ≤
      (if levelScale t k < a then (levelScale t (k + 1)) ^ q else 0) := by
    split_ifs
    · exact Real.rpow_nonneg (levelScale_pos ht _).le _
    · exact le_rfl
  have htq : 0 ≤ t ^ q := Real.rpow_nonneg ht.le _
  induction N with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    by_cases h : levelScale t 0 < a
    · rw [ite_eq_left h]
      have hle := Real.rpow_le_rpow (le_min ha (levelScale_pos ht _).le)
        (min_le_right a (levelScale t 1)) hq
      linarith
    · rw [ite_eq_right h, add_zero]
      have hat : a ≤ t := by simpa only [levelScale, pow_zero, mul_one] using le_of_not_gt h
      exact Real.rpow_le_rpow (le_min ha (levelScale_pos ht _).le)
        ((min_le_left _ _).trans hat) hq
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases h : levelScale t (N + 1) < a
    · rw [ite_eq_left h]
      have hsum : 0 ≤ ∑ k ∈ Finset.range (N + 1),
          if levelScale t k < a then (levelScale t (k + 1)) ^ q else 0 :=
        Finset.sum_nonneg fun k _ => hterm k
      have hle := Real.rpow_le_rpow (le_min ha (levelScale_pos ht _).le)
        (min_le_right a (levelScale t (N + 1 + 1))) hq
      linarith
    · rw [ite_eq_right h, add_zero]
      have haOld : a ≤ levelScale t (N + 1) := le_of_not_gt h
      have haNew : a ≤ levelScale t (N + 1 + 1) := by
        rw [levelScale_succ]
        have hpos := levelScale_pos ht (N + 1)
        linarith
      rw [min_eq_left haNew]
      rwa [min_eq_left haOld] at ih

/-- Subadditivity of a fractional power across a finite sum. -/
theorem finite_sum_rpow_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (F : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ k ∈ F, 0 ≤ a k) :
    (∑ k ∈ F, a k) ^ β ≤ ∑ k ∈ F, (a k) ^ β := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Real.zero_rpow hβ.ne', le_refl]
  | @insert k F hk ih =>
    have hk0 : 0 ≤ a k := ha k (Finset.mem_insert_self _ _)
    have hF0 : ∀ j ∈ F, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    exact (Real.rpow_add_le_add_rpow hk0 (Finset.sum_nonneg hF0) hβ.le hβ1).trans
      (add_le_add le_rfl (ih hF0))

/-- Critical-exponent bookkeeping for the dyadic moment summands. -/
theorem dyadic_moment_term {t a q β : ℝ} (ht : 0 < t) (ha : 0 ≤ a)
    (_hβ : 0 < β) (hqβ : q * β = 2) (k : ℕ) :
    (((levelScale t (k + 1)) ^ q) * a) ^ β =
      4 * t ^ 2 * (4 : ℝ) ^ k * a ^ β := by
  rw [Real.mul_rpow (Real.rpow_nonneg (levelScale_pos ht _).le _) ha,
    ← Real.rpow_mul (levelScale_pos ht _).le, hqβ, Real.rpow_two, levelScale_sq, pow_succ]
  ring

/-- A real moment bound becomes the finite dyadic distribution sum at critical power. -/
theorem dyadic_moment_power {t I V q β : ℝ} (ht : 0 < t) (hI : 0 ≤ I)
    (hV : 0 ≤ V) (hβ : 0 < β) (hβ1 : β < 1) (hqβ : q * β = 2)
    (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (N : ℕ)
    (hbound : I ≤ t ^ q * V + ∑ k ∈ Finset.range (N + 1),
      (levelScale t (k + 1)) ^ q * a k) :
    I ^ β ≤ t ^ 2 * V ^ β + 4 * t ^ 2 *
      ∑ k ∈ Finset.range (N + 1), (4 : ℝ) ^ k * (a k) ^ β := by
  have hsum : 0 ≤ ∑ k ∈ Finset.range (N + 1), (levelScale t (k + 1)) ^ q * a k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Real.rpow_nonneg (levelScale_pos ht _).le _) (ha k)
  calc
    I ^ β ≤ (t ^ q * V + ∑ k ∈ Finset.range (N + 1),
        (levelScale t (k + 1)) ^ q * a k) ^ β := Real.rpow_le_rpow hI hbound hβ.le
    _ ≤ (t ^ q * V) ^ β +
        (∑ k ∈ Finset.range (N + 1), (levelScale t (k + 1)) ^ q * a k) ^ β :=
      Real.rpow_add_le_add_rpow (mul_nonneg (Real.rpow_nonneg ht.le _) hV) hsum hβ.le hβ1.le
    _ ≤ (t ^ q * V) ^ β + ∑ k ∈ Finset.range (N + 1),
        ((levelScale t (k + 1)) ^ q * a k) ^ β :=
      add_le_add le_rfl (finite_sum_rpow_le hβ hβ1.le _ _
        (fun k _ => mul_nonneg (Real.rpow_nonneg (levelScale_pos ht _).le _) (ha k)))
    _ = _ := by
      rw [Real.mul_rpow (Real.rpow_nonneg ht.le _) hV, ← Real.rpow_mul ht.le,
        hqβ, Real.rpow_two]
      simp_rw [dyadic_moment_term ht (ha _) hβ hqβ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring

end SubdiffusiveProcess.FractionalEmbedding
