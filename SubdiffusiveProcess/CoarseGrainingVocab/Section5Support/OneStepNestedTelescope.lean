import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# The finite-scale telescope for the one-step nested recentring

This is the model-independent accumulation used after recentering the
large-cube solution at every member of a concentric triadic family.  A
harmonic increment born at level `j` receives the arbitrary-gap factor
`3⁻ʲ`, while its forcing defect has size `3^(n+j)`.  Their product is
independent of `j`, so the forcing loss is linear in the number of levels.

The organization mirrors
`Algsuperdiff/Section3/Provider/Diffusivity/Corrector/OscillationTelescope.lean`.
Only its elementary finite-sum layer is needed here; the GMC weak-equation
and stochastic transports live in `OneStepNestedRecentering` and
`OneStepNestedMomentSweep`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

/-- Cancellation of the arbitrary-gap harmonic factor against the
birth-scale size of a correction. -/
theorem oneStep_zpow_neg_natCast_mul_zpow_add (n : ℤ) (j : ℕ) :
    (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (n + (j : ℤ)) = (3 : ℝ) ^ n := by
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  ring

/-- A triadically weighted family of birth-scale errors accumulates only
linearly in the number of recentering levels. -/
theorem oneStep_sum_zpow_neg_mul_le_nsmul_of_triadic_bound
    {E : ℕ → ℝ} {n : ℤ} {N : ℕ} {A rho c : ℝ}
    (hA : 0 ≤ A) (hrho : 0 ≤ rho)
    (hE : ∀ j ≤ N, E j ≤ c * (3 : ℝ) ^ (n + (j : ℤ))) :
    ∑ j ∈ Finset.range N,
        A * (3 : ℝ) ^ (-(j : ℤ)) * (E j + rho * E (j + 1)) ≤
      (N : ℝ) * (A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c)) := by
  have hterm : ∀ j ∈ Finset.range N,
      A * (3 : ℝ) ^ (-(j : ℤ)) * (E j + rho * E (j + 1)) ≤
        A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c) := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have hEj : E j ≤ c * (3 : ℝ) ^ (n + (j : ℤ)) := hE j hjN.le
    have hEj1 : E (j + 1) ≤
        c * ((3 : ℝ) ^ (n + (j : ℤ)) * 3) := by
      have h := hE (j + 1) hjN
      have hcast :
          (3 : ℝ) ^ (n + ((j + 1 : ℕ) : ℤ)) =
            (3 : ℝ) ^ (n + (j : ℤ)) * 3 := by
        have hidx : n + ((j + 1 : ℕ) : ℤ) =
            (n + (j : ℤ)) + 1 := by
          push_cast
          ring
        rw [hidx, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num
      rwa [hcast] at h
    have hwpos : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) :=
      zpow_pos (by norm_num) _
    have hscaled : rho * E (j + 1) ≤
        rho * (c * ((3 : ℝ) ^ (n + (j : ℤ)) * 3)) :=
      mul_le_mul_of_nonneg_left hEj1 hrho
    have hinner : E j + rho * E (j + 1) ≤
        (1 + 3 * rho) * ((3 : ℝ) ^ (n + (j : ℤ)) * c) := by
      linarith
    have hfac : (0 : ℝ) ≤ A * (3 : ℝ) ^ (-(j : ℤ)) :=
      mul_nonneg hA hwpos.le
    calc
      A * (3 : ℝ) ^ (-(j : ℤ)) * (E j + rho * E (j + 1)) ≤
          A * (3 : ℝ) ^ (-(j : ℤ)) *
            ((1 + 3 * rho) * ((3 : ℝ) ^ (n + (j : ℤ)) * c)) :=
        mul_le_mul_of_nonneg_left hinner hfac
      _ = A * (1 + 3 * rho) *
          (((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (n + (j : ℤ))) * c) := by
        ring
      _ = A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c) := by
        rw [oneStep_zpow_neg_natCast_mul_zpow_add]
  calc
    ∑ j ∈ Finset.range N,
        A * (3 : ℝ) ^ (-(j : ℤ)) * (E j + rho * E (j + 1)) ≤
        ∑ _j ∈ Finset.range N,
          A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c) :=
      Finset.sum_le_sum hterm
    _ = (N : ℝ) * (A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Display-shaped close of the nested decomposition.  All analytic inputs
are explicit: `T` is the coarsest harmonic term, `S j` the increment born at
level `j`, and `E j` the corresponding local forcing correction. -/
theorem oneStep_le_zpow_mul_add_nsmul_of_nested_decomposition
    {Phi E S : ℕ → ℝ} {T : ℝ} {n : ℤ} {N : ℕ} {A rho c : ℝ}
    (hA : 0 ≤ A) (hrho : 0 ≤ rho)
    (hE : ∀ j ≤ N, E j ≤ c * (3 : ℝ) ^ (n + (j : ℤ)))
    (hsplit : Phi 0 ≤ T + (∑ j ∈ Finset.range N, S j) + 2 * E 0)
    (hT : T ≤ A * (3 : ℝ) ^ (-(N : ℤ)) * (Phi N + E N))
    (hS : ∀ j < N,
      S j ≤ A * (3 : ℝ) ^ (-(j : ℤ)) * (E j + rho * E (j + 1))) :
    Phi 0 ≤ A * (3 : ℝ) ^ (-(N : ℤ)) * Phi N +
      (A * (1 + 3 * rho) * (N : ℝ) + A + 2) * ((3 : ℝ) ^ n * c) := by
  have hTbound : T ≤
      A * (3 : ℝ) ^ (-(N : ℤ)) * Phi N + A * ((3 : ℝ) ^ n * c) := by
    have hEN : E N ≤ c * (3 : ℝ) ^ (n + (N : ℤ)) := hE N le_rfl
    have hwpos : (0 : ℝ) < (3 : ℝ) ^ (-(N : ℤ)) :=
      zpow_pos (by norm_num) _
    have hfac : (0 : ℝ) ≤ A * (3 : ℝ) ^ (-(N : ℤ)) :=
      mul_nonneg hA hwpos.le
    have hstep : A * (3 : ℝ) ^ (-(N : ℤ)) * (Phi N + E N) ≤
        A * (3 : ℝ) ^ (-(N : ℤ)) *
          (Phi N + c * (3 : ℝ) ^ (n + (N : ℤ))) :=
      mul_le_mul_of_nonneg_left (by linarith) hfac
    have hflat :
        A * (3 : ℝ) ^ (-(N : ℤ)) *
            (Phi N + c * (3 : ℝ) ^ (n + (N : ℤ))) =
          A * (3 : ℝ) ^ (-(N : ℤ)) * Phi N +
            A * (((3 : ℝ) ^ (-(N : ℤ)) *
              (3 : ℝ) ^ (n + (N : ℤ))) * c) := by
      ring
    rw [hflat, oneStep_zpow_neg_natCast_mul_zpow_add] at hstep
    exact hT.trans hstep
  have hsum : ∑ j ∈ Finset.range N, S j ≤
      (N : ℝ) * (A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c)) :=
    le_trans
      (Finset.sum_le_sum fun j hj => hS j (Finset.mem_range.mp hj))
      (oneStep_sum_zpow_neg_mul_le_nsmul_of_triadic_bound hA hrho hE)
  have hdefect : 2 * E 0 ≤ 2 * ((3 : ℝ) ^ n * c) := by
    have h0 := hE 0 (Nat.zero_le N)
    have hz : (3 : ℝ) ^ (n + ((0 : ℕ) : ℤ)) = (3 : ℝ) ^ n := by
      norm_num
    rw [hz] at h0
    linarith
  have hcollect :
      (N : ℝ) * (A * (1 + 3 * rho) * ((3 : ℝ) ^ n * c)) +
          A * ((3 : ℝ) ^ n * c) + 2 * ((3 : ℝ) ^ n * c) =
        (A * (1 + 3 * rho) * (N : ℝ) + A + 2) *
          ((3 : ℝ) ^ n * c) := by
    ring
  linarith [hsplit, hTbound, hsum, hdefect, hcollect.ge, hcollect.le]

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
