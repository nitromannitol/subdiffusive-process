module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
namespace SubdiffusiveProcess.Analysis

/-- A unit-scale Hölder estimate can be chained across any fixed bounded distance. -/
theorem holder_bound_of_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E → ℝ) (a C : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hlocal : ∀ x y, dist x y ≤ 1 → |v x - v y| ≤ C * dist x y ^ a)
    (N : ℕ) (hN : 0 < N) (x y : E) (hxy : dist x y ≤ N) :
    |v x - v y| ≤ (N : ℝ) * C * dist x y ^ a := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let z : ℕ → E := fun k => x + ((k : ℝ) / N) • (y - x)
  have hz0 : z 0 = x := by simp only [z, Nat.cast_zero, zero_div, zero_smul, add_zero]
  have hzN : z N = y := by
    simp only [z, div_self hNr.ne', one_smul, add_sub_cancel]
  have hstep : ∀ k, dist (z k) (z (k + 1)) = dist x y / N := by
    intro k
    have hid : z k - z (k + 1) = (-(1 / (N : ℝ))) • (y - x) := by
      dsimp only [z]
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      congr 1
      push_cast
      ring
    rw [dist_eq_norm, hid, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity), norm_sub_rev, ← dist_eq_norm]
    simp only [div_eq_mul_inv, one_mul]
    ring
  have hbound : ∀ k, dist (v (z k)) (v (z (k + 1))) ≤ C * dist x y ^ a := by
    intro k
    rw [Real.dist_eq]
    refine (hlocal _ _ (by rw [hstep]; exact (div_le_one hNr).2 hxy)).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.rpow_le_rpow dist_nonneg _ ha
    rw [hstep]
    exact div_le_self dist_nonneg hN1
  have h := dist_le_range_sum_of_dist_le (f := fun k => v (z k)) N (fun {k} _ => hbound k)
  change dist (v (z 0)) (v (z N)) ≤ _ at h
  rw [hz0, hzN, Real.dist_eq] at h
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc] using h


/-- A local Hölder function with one zero has a uniform norm bound on a bounded set. -/
theorem exists_bound_of_local_holder_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (hS : Bornology.IsBounded S) (x0 : E) (a : ℝ) (ha : 0 ≤ a) :
    ∃ G : ℝ, 0 < G ∧ ∀ (v : E → ℝ) (C : ℝ), 0 ≤ C → v x0 = 0 →
      (∀ x y, dist x y ≤ 1 → |v x - v y| ≤ C * dist x y ^ a) →
      (∀ x ∈ S, |v x| ≤ G * C) ∧
      (∀ x ∈ S, ∀ y ∈ S, |v x - v y| ≤ G * C * dist x y ^ a) := by
  obtain ⟨r, hr⟩ := hS.subset_closedBall x0
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (2 * max r 0))
  have hN1 : (1 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hNr : 0 < (N : ℝ) := zero_lt_one.trans_le hN1
  have hNpos : 0 < N := by exact_mod_cast hNr
  have hN2 : 2 * max r 0 ≤ N := (le_max_right _ _).trans hN
  have hdx : ∀ x ∈ S, dist x x0 ≤ max r 0 :=
    fun x hx => (hr hx).trans (le_max_left _ _)
  have hdist : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ N := by
    intro x hx y hy
    exact (dist_triangle x x0 y).trans
      ((add_le_add (hdx x hx) (by simpa only [dist_comm] using hdx y hy)).trans
        (by linarith only [hN2]))
  let G : ℝ := (N : ℝ) * (1 + (N : ℝ) ^ a)
  have hG : 0 < G := mul_pos hNr (by positivity)
  have hNG : (N : ℝ) ≤ G := by
    dsimp only [G]
    exact le_mul_of_one_le_right hNr.le (by linarith [Real.rpow_nonneg hNr.le a])
  refine ⟨G, hG, fun v C hC hz hl => ⟨?_, ?_⟩⟩
  · intro x hx
    have hxb : dist x x0 ≤ N := (hdx x hx).trans (by linarith only [hN2, le_max_right r 0])
    have h := holder_bound_of_local v a C ha hC hl N hNpos x x0 hxb
    rw [hz, sub_zero] at h
    refine h.trans ?_
    calc
      (N : ℝ) * C * dist x x0 ^ a ≤ (N : ℝ) * C * (N : ℝ) ^ a :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hxb ha) (mul_nonneg hNr.le hC)
      _ ≤ G * C := by
        dsimp only [G]
        nlinarith only [mul_nonneg hNr.le hC]
  · intro x hx y hy
    exact (holder_bound_of_local v a C ha hC hl N hNpos x y (hdist x hx y hy)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNG hC)
        (Real.rpow_nonneg dist_nonneg _))

end SubdiffusiveProcess.Analysis
