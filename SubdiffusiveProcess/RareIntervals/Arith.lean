module

public import Mathlib

@[expose] public section

/-!
# Final arithmetic of the rare-interval lemma

With `x = λ θ N`, `λ θ ≥ 100`, `0 < θ ≤ 1`, `N ≥ 1`:
`2 N e^{-λ N} + 2^{3N} e^{-x/6} ≤ e^{-x/24}`.
-/

namespace SubdiffusiveProcess.RareIntervals

theorem rare_arith (lam θ : ℝ) (N : ℕ) (hN : 1 ≤ N) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hC : 100 ≤ lam * θ) :
    2 * (N : ℝ) * Real.exp (-(lam * N)) + 2 ^ (3 * N) * Real.exp (-(lam * (θ * N / 6))) ≤
      Real.exp (-(lam * θ * N / 24)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlam : 0 < lam := by
    by_contra h
    push Not at h
    nlinarith
  set x : ℝ := lam * θ * N with hx
  have hxN : 100 * (N : ℝ) ≤ x := by rw [hx]; nlinarith
  have hxlam : x ≤ lam * N := by rw [hx]; nlinarith
  have hexp2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hT1 : 2 * (N : ℝ) * Real.exp (-(lam * N)) ≤ Real.exp (-(x / 24)) / 2 := by
    have h1 : Real.exp (-(lam * N)) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    have h2 : 4 * (N : ℝ) ≤ Real.exp (23 * x / 24) := by
      have := Real.add_one_le_exp (23 * x / 24); nlinarith
    have h3 : Real.exp (-(x / 24)) = Real.exp (-x) * Real.exp (23 * x / 24) := by
      rw [← Real.exp_add]; ring_nf
    calc 2 * (N : ℝ) * Real.exp (-(lam * N)) ≤ 2 * (N : ℝ) * Real.exp (-x) := by gcongr
      _ = (4 * (N : ℝ) * Real.exp (-x)) / 2 := by ring
      _ ≤ (Real.exp (23 * x / 24) * Real.exp (-x)) / 2 := by gcongr
      _ = Real.exp (-(x / 24)) / 2 := by rw [h3]; ring
  have hT2 : 2 ^ (3 * N) * Real.exp (-(lam * (θ * N / 6))) ≤ Real.exp (-(x / 24)) / 2 := by
    have h4 : (2 : ℝ) ^ (3 * N + 1) ≤ Real.exp (x / 8) := by
      calc (2 : ℝ) ^ (3 * N + 1) ≤ Real.exp 1 ^ (3 * N + 1) := by gcongr
        _ = Real.exp (((3 * N + 1 : ℕ) : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ Real.exp (x / 8) := by
          apply Real.exp_le_exp.mpr
          push_cast
          nlinarith
    have h5 : Real.exp (-(lam * (θ * N / 6))) = Real.exp (-(x / 6)) := by
      congr 1; rw [hx]; ring
    have h6 : Real.exp (-(x / 24)) = Real.exp (-(x / 6)) * Real.exp (x / 8) := by
      rw [← Real.exp_add]; ring_nf
    rw [h5]
    calc 2 ^ (3 * N) * Real.exp (-(x / 6))
        = (2 ^ (3 * N + 1) * Real.exp (-(x / 6))) / 2 := by ring
      _ ≤ (Real.exp (x / 8) * Real.exp (-(x / 6))) / 2 := by gcongr
      _ = Real.exp (-(x / 24)) / 2 := by rw [h6]; ring
  calc _ ≤ Real.exp (-(x / 24)) / 2 + Real.exp (-(x / 24)) / 2 := add_le_add hT1 hT2
    _ = Real.exp (-(x / 24)) := by ring
    _ = _ := by rw [hx]

end SubdiffusiveProcess.RareIntervals
