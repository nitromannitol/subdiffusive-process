import Mathlib.Analysis.SpecificLimits.Basic

/-! This module turns positive-scale normalized coefficient limits into eventual margins and one common tail. It makes no stochastic or sign claim about the coefficients. -/

open Filter
open scoped Topology

namespace SubdiffusiveProcess

/-- A converging normalized upper coefficient is eventually bounded by twice its positive reference cap. -/
theorem eventually_upper_coefficient_of_normalized_tendsto
    (a scale : ℕ → ℝ) (U s C : ℝ) (hs : 0 < s) (hC : 0 < C)
    (hscale : Tendsto scale atTop (𝓝 s))
    (hnorm : Tendsto (fun n => a n / scale n) atTop (𝓝 U))
    (hU : U ≤ C) :
    ∀ᶠ n in atTop, a n ≤ 2 * C * s := by
  have hscale_pos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually_const_lt hs
  have hscale_ne : ∀ᶠ n in atTop, scale n ≠ 0 :=
    hscale_pos.mono fun n hn => ne_of_gt hn
  have hprod : Tendsto (fun n => a n / scale n * scale n) atTop (𝓝 (U * s)) :=
    hnorm.mul hscale
  have hcoeff : Tendsto a atTop (𝓝 (U * s)) := by
    refine Filter.Tendsto.congr' ?_ hprod
    filter_upwards [hscale_ne] with n hn
    exact div_mul_cancel₀ (a n) hn
  have hUs : U * s ≤ C * s := mul_le_mul_of_nonneg_right hU hs.le
  have hCs_pos : 0 < C * s := mul_pos hC hs
  have hCs_lt : C * s < 2 * C * s := by
    nlinarith only [hCs_pos]
  have hmargin : U * s < 2 * C * s := lt_of_le_of_lt hUs hCs_lt
  have hlt : ∀ᶠ n in atTop, a n < 2 * C * s :=
    hcoeff.eventually_lt_const hmargin
  exact hlt.mono fun n hn => hn.le

/-- A converging normalized lower coefficient eventually retains half its positive reference floor. -/
theorem eventually_lower_coefficient_of_normalized_tendsto
    (a scale : ℕ → ℝ) (L s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hscale : Tendsto scale atTop (𝓝 s))
    (hnorm : Tendsto (fun n => a n / scale n) atTop (𝓝 L))
    (hL : c ≤ L) :
    ∀ᶠ n in atTop, c * s / 2 ≤ a n := by
  have hscale_pos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually_const_lt hs
  have hscale_ne : ∀ᶠ n in atTop, scale n ≠ 0 :=
    hscale_pos.mono fun n hn => ne_of_gt hn
  have hprod : Tendsto (fun n => a n / scale n * scale n) atTop (𝓝 (L * s)) :=
    hnorm.mul hscale
  have hcoeff : Tendsto a atTop (𝓝 (L * s)) := by
    refine Filter.Tendsto.congr' ?_ hprod
    filter_upwards [hscale_ne] with n hn
    exact div_mul_cancel₀ (a n) hn
  have hcs_le : c * s ≤ L * s := mul_le_mul_of_nonneg_right hL hs.le
  have hcs_pos : 0 < c * s := mul_pos hc hs
  have hhalf : c * s / 2 < c * s := by
    linarith only [hcs_pos]
  have hmargin : c * s / 2 < L * s := lt_of_lt_of_le hhalf hcs_le
  have hlt : ∀ᶠ n in atTop, c * s / 2 < a n :=
    hcoeff.eventually_const_lt hmargin
  exact hlt.mono fun n hn => hn.le

/-- Normalized lower and upper convergence provide one tail carrying both coefficient bounds. -/
theorem exists_tail_coefficient_bounds_of_normalized_tendsto
    (lo hi scale : ℕ → ℝ) (L U s c C : ℝ) (hs : 0 < s) (hc : 0 < c) (hC : 0 < C)
    (hscale : Tendsto scale atTop (𝓝 s))
    (hlo : Tendsto (fun n => lo n / scale n) atTop (𝓝 L))
    (hhi : Tendsto (fun n => hi n / scale n) atTop (𝓝 U))
    (hL : c ≤ L) (hU : U ≤ C) :
    ∃ N : ℕ, ∀ n : ℕ, c * s / 2 ≤ lo (N + n) ∧ hi (N + n) ≤ 2 * C * s := by
  have hlo_bound : ∀ᶠ n in atTop, c * s / 2 ≤ lo n :=
    eventually_lower_coefficient_of_normalized_tendsto lo scale L s c hs hc
      hscale hlo hL
  have hhi_bound : ∀ᶠ n in atTop, hi n ≤ 2 * C * s :=
    eventually_upper_coefficient_of_normalized_tendsto hi scale U s C hs hC
      hscale hhi hU
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hlo_bound.and hhi_bound)
  refine ⟨N, fun n => ?_⟩
  exact hN (N + n) (Nat.le_add_right N n)

end SubdiffusiveProcess
