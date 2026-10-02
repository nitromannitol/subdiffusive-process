

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A quantitative lower-tail bootstrap

Real-variable support for the binary recursion in the weighted-volume argument.
The results here are conditional deterministic lemmas; they do not import or
assert the Section 9 weighted-volume theorem.
-/

namespace SubdiffusiveProcess.Section9

/-- Geometric-interval induction for a binary lower-tail recursion. -/
theorem lowerTail_geometric_bootstrap
    (F G : ℝ → ℝ) (ell U a p : ℝ)
    (hell : 0 ≤ ell) (hUpos : 0 < U) (hU : (4 / 3 : ℝ) * ell ≤ U)
    (hFnonneg : ∀ u, ell ≤ u → 0 ≤ F u)
    (hseed : ∀ u, ell ≤ u → u ≤ U → F u ≤ Real.exp (-a * p * u))
    (hrec : ∀ u, U ≤ u → F u ≤ G u + (F ((3 / 4 : ℝ) * u)) ^ 2)
    (hforcing : ∀ u, U ≤ u → G u ≤ (1 / 2 : ℝ) * Real.exp (-a * p * u))
    (hrecursive : ∀ u, U ≤ u →
      (Real.exp (-a * p * ((3 / 4 : ℝ) * u))) ^ 2 ≤
        (1 / 2 : ℝ) * Real.exp (-a * p * u)) :
    ∀ u, ell ≤ u → F u ≤ Real.exp (-a * p * u) := by
  have hgrid : ∀ n : ℕ, ∀ u : ℝ, ell ≤ u →
      u ≤ U * (4 / 3 : ℝ) ^ n → F u ≤ Real.exp (-a * p * u) := by
    intro n
    induction n with
    | zero =>
        intro u huell huU
        apply hseed u huell
        simpa only [pow_zero, mul_one] using huU
    | succ n ih =>
        intro u huell hugrid
        by_cases hu : u ≤ U * (4 / 3 : ℝ) ^ n
        · exact ih u huell hu
        · have hUnonneg : 0 ≤ U := hell.trans (le_trans (by linarith) hU)
          have hpowone : 1 ≤ (4 / 3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
          have hUu : U ≤ u := by
            have : U ≤ U * (4 / 3 : ℝ) ^ n :=
              le_mul_of_one_le_right hUnonneg hpowone
            exact this.trans (le_of_not_ge hu)
          have hvell : ell ≤ (3 / 4 : ℝ) * u := by
            have : U < u := lt_of_le_of_lt
              (le_mul_of_one_le_right hUnonneg hpowone) (lt_of_not_ge hu)
            nlinarith
          have hvgrid : (3 / 4 : ℝ) * u ≤ U * (4 / 3 : ℝ) ^ n := by
            rw [pow_succ] at hugrid
            nlinarith
          have hv := ih ((3 / 4 : ℝ) * u) hvell hvgrid
          calc
            F u ≤ G u + (F ((3 / 4 : ℝ) * u)) ^ 2 := hrec u hUu
            _ ≤ (1 / 2 : ℝ) * Real.exp (-a * p * u) +
                (Real.exp (-a * p * ((3 / 4 : ℝ) * u))) ^ 2 := by
              exact add_le_add (hforcing u hUu) (by
                simpa only [pow_two] using
                  mul_self_le_mul_self (hFnonneg _ hvell) hv)
            _ ≤ (1 / 2 : ℝ) * Real.exp (-a * p * u) +
                (1 / 2 : ℝ) * Real.exp (-a * p * u) :=
              add_le_add_right (hrecursive u hUu) _
            _ = Real.exp (-a * p * u) := by ring
  intro u huell
  by_cases huU : u ≤ U
  · exact hseed u huell huU
  · have hx : 1 ≤ u / U := (le_div_iff₀ hUpos).2 (by
      simpa only [one_mul] using le_of_not_ge huU)
    obtain ⟨n, -, hn⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 4 / 3)
    apply hgrid (n + 1) u huell
    simpa only [mul_comm] using ((div_lt_iff₀ hUpos).1 hn).le

/-- The squared recursive contribution has half-target slack once the rate at
the base threshold is at least `2 log 2`. -/
theorem lowerTail_recursive_half
    {a p U u : ℝ} (hap : 0 ≤ a * p) (hUu : U ≤ u)
    (hslack : 2 * Real.log 2 ≤ a * p * U) :
    (Real.exp (-a * p * ((3 / 4 : ℝ) * u))) ^ 2 ≤
      (1 / 2 : ℝ) * Real.exp (-a * p * u) := by
  rw [sq, ← Real.exp_add]
  have hlog : Real.log 2 ≤ a * p * u / 2 := by
    have := mul_le_mul_of_nonneg_left hUu hap
    nlinarith
  calc
    Real.exp (-a * p * ((3 / 4 : ℝ) * u) +
        -a * p * ((3 / 4 : ℝ) * u)) ≤
        Real.exp (-a * p * u - Real.log 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = (1 / 2 : ℝ) * Real.exp (-a * p * u) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring

/-- Explicit sufficient inequalities absorbing the Gaussian forcing term. -/
theorem gaussianForcing_le_half
    {C c δ U a p u : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hδ : 0 < δ) (hU : 2 * max C 1 ≤ U)
    (hUu : U ≤ u) (hrateBase : a * p ≤ c * U / (8 * δ ^ 2))
    (hlogBase : Real.log (2 * max C 1) ≤ c * U ^ 2 / (8 * δ ^ 2)) :
    C * Real.exp (-c * max (u - C) 0 ^ 2 / δ ^ 2) ≤
      (1 / 2 : ℝ) * Real.exp (-a * p * u) := by
  have hM : 1 ≤ max C 1 := le_max_right _ _
  have hCu : C ≤ u / 2 := by
    have := le_trans hU hUu
    exact le_trans (le_max_left C 1) (by linarith)
  have hpos : 0 ≤ u - C := by linarith
  rw [max_eq_left hpos]
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hrate : a * p * u ≤ c * u ^ 2 / (8 * δ ^ 2) := by
    have hu0 : 0 ≤ u := by linarith
    have hm := mul_le_mul_of_nonneg_right hrateBase hu0
    have hUu' : U * u ≤ u ^ 2 := by nlinarith
    have hden : 0 < 8 * δ ^ 2 := mul_pos (by norm_num) hδ2
    exact hm.trans (by
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hden).2
      nlinarith)
  have hlog' : Real.log (2 * max C 1) ≤ c * u ^ 2 / (8 * δ ^ 2) := by
    have hu2 : U ^ 2 ≤ u ^ 2 := by nlinarith
    exact hlogBase.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu2 hc.le) (by positivity))
  have hexponent : a * p * u + Real.log (2 * max C 1) ≤
      c * (u - C) ^ 2 / δ ^ 2 := by
    have hdiff : u / 2 ≤ u - C := by linarith
    have hsq : u ^ 2 / 4 ≤ (u - C) ^ 2 := by nlinarith
    have hden : 0 < δ ^ 2 := hδ2
    apply (le_div_iff₀ hden).2
    have hr := (le_div_iff₀ (show 0 < 8 * δ ^ 2 by positivity)).1 hrate
    have hl := (le_div_iff₀ (show 0 < 8 * δ ^ 2 by positivity)).1 hlog'
    nlinarith
  have hCtwo : C ≤ (1 / 2 : ℝ) * (2 * max C 1) := by
    rw [show (1 / 2 : ℝ) * (2 * max C 1) = max C 1 by ring]
    exact le_max_left _ _
  calc
    C * Real.exp (-c * (u - C) ^ 2 / δ ^ 2) ≤
        (1 / 2 : ℝ) * (2 * max C 1) *
          Real.exp (-c * (u - C) ^ 2 / δ ^ 2) := by
      exact mul_le_mul_of_nonneg_right hCtwo (Real.exp_nonneg _)
    _ ≤ (1 / 2 : ℝ) * (2 * max C 1) *
          Real.exp (-(a * p * u + Real.log (2 * max C 1))) := by
      gcongr
      rw [show -c * (u - C) ^ 2 / δ ^ 2 =
        -(c * (u - C) ^ 2 / δ ^ 2) by ring]
      exact neg_le_neg hexponent
    _ = (1 / 2 : ℝ) * Real.exp (-a * p * u) := by
      rw [neg_add, Real.exp_add,
        Real.exp_neg (Real.log (2 * max C 1)),
        Real.exp_log (show 0 < 2 * max C 1 by positivity)]
      field_simp

end SubdiffusiveProcess.Section9
