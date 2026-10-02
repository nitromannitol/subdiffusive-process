import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Stampacchia's iteration lemma

If `φ ≥ 0` is nonincreasing on `[0,∞)` and `(h-k)^α φ(h) ≤ A φ(k)^β` for `h > k ≥ 0` with
`α > 0`, `β > 1`, then `φ(δ) = 0` as soon as `δ^α ≥ A φ(0)^{β-1} 2^{αβ/(β-1)}`.
-/

open Filter Topology

namespace SubdiffusiveProcess.FractionalSup

/-- **Stampacchia's iteration lemma.** -/
theorem stampacchia_iteration {φ : ℝ → ℝ} (hφ0 : ∀ k, 0 ≤ φ k)
    (hmono : ∀ k h, 0 ≤ k → k ≤ h → φ h ≤ φ k)
    {A α β : ℝ} (hA : 0 ≤ A) (hα : 0 < α) (hβ : 1 < β)
    (hstep : ∀ k h, 0 ≤ k → k < h → (h - k) ^ α * φ h ≤ A * φ k ^ β)
    {δ : ℝ} (hδ : 0 < δ)
    (hδα : A * φ 0 ^ (β - 1) * (2 : ℝ) ^ (α * β / (β - 1)) ≤ δ ^ α) :
    φ δ = 0 := by
  set μ : ℝ := α / (β - 1) with hμ
  have hβ1 : 0 < β - 1 := by linarith
  have hμpos : 0 < μ := div_pos hα hβ1
  have hμβ : μ * (β - 1) = α := by rw [hμ]; field_simp
  set x : ℝ := Real.log 2 with hx
  have hx0 : 0 < x := Real.log_pos (by norm_num)
  have h2 : ∀ t : ℝ, (2 : ℝ) ^ t = Real.exp (t * x) := fun t => by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  set φ0 := φ 0 with hφ0def
  -- the sequence of levels
  let k : ℕ → ℝ := fun n => δ * (1 - Real.exp (-(n : ℝ) * x))
  have hk0 : k 0 = 0 := by simp [k]
  have hk_nonneg : ∀ n, 0 ≤ k n := by
    intro n
    have : Real.exp (-(n : ℝ) * x) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hx0, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    exact mul_nonneg hδ.le (by linarith)
  have hk_le : ∀ n, k n ≤ δ := by
    intro n
    have : 0 < Real.exp (-(n : ℝ) * x) := Real.exp_pos _
    simp only [k]; nlinarith
  have hkgap : ∀ n, k (n + 1) - k n = δ * Real.exp (-((n : ℝ) + 1) * x) := by
    intro n
    simp only [k]
    push_cast
    have : Real.exp (-((n : ℝ) + 1) * x) = Real.exp (-(n : ℝ) * x) / 2 := by
      rw [show -((n : ℝ) + 1) * x = -(n : ℝ) * x + (-x) by ring, Real.exp_add, hx,
        Real.exp_neg, Real.exp_log (by norm_num)]
      ring
    rw [this]; ring
  -- geometric decay
  have key : ∀ n : ℕ, φ (k n) ≤ φ0 * Real.exp (-μ * n * x) := by
    intro n
    induction n with
    | zero => simp [hk0, hφ0def]
    | succ n ih =>
      have hgap_pos : 0 < k (n + 1) - k n := by
        rw [hkgap]; exact mul_pos hδ (Real.exp_pos _)
      have hst := hstep (k n) (k (n + 1)) (hk_nonneg n) (by linarith)
      rw [hkgap] at hst
      have hpow : (δ * Real.exp (-((n : ℝ) + 1) * x)) ^ α =
          δ ^ α * Real.exp (-((n : ℝ) + 1) * x * α) := by
        rw [Real.mul_rpow hδ.le (Real.exp_pos _).le, ← Real.exp_mul]
      rw [hpow] at hst
      have hφn : φ (k n) ^ β ≤ (φ0 * Real.exp (-μ * n * x)) ^ β :=
        Real.rpow_le_rpow (hφ0 _) ih (by linarith)
      have hφn' : (φ0 * Real.exp (-μ * n * x)) ^ β =
          φ0 ^ β * Real.exp (-μ * n * x * β) := by
        by_cases hz : φ0 = 0
        · rw [hz]; simp [Real.zero_rpow (by linarith : β ≠ 0)]
        · rw [Real.mul_rpow (hφ0 0) (Real.exp_pos _).le, ← Real.exp_mul]
      -- collect
      have hL : 0 < δ ^ α * Real.exp (-((n : ℝ) + 1) * x * α) :=
        mul_pos (Real.rpow_pos_of_pos hδ _) (Real.exp_pos _)
      have hφb : φ (k (n + 1)) ≤ A * φ0 ^ β * Real.exp (-μ * n * x * β) /
          (δ ^ α * Real.exp (-((n : ℝ) + 1) * x * α)) := by
        rw [le_div_iff₀ hL, mul_comm]
        calc _ ≤ A * φ (k n) ^ β := hst
          _ ≤ A * (φ0 ^ β * Real.exp (-μ * n * x * β)) := by
              rw [← hφn']; exact mul_le_mul_of_nonneg_left hφn hA
          _ = _ := by ring
      have hφ0β : φ0 ^ β = φ0 * φ0 ^ (β - 1) := by
        by_cases hz : φ0 = 0
        · rw [hz]; simp [Real.zero_rpow (by linarith : β ≠ 0)]
        · have hpos : 0 < φ0 := lt_of_le_of_ne (hφ0 0) (Ne.symm hz)
          have := Real.rpow_add hpos 1 (β - 1)
          rw [Real.rpow_one, show (1 : ℝ) + (β - 1) = β by ring] at this
          exact this
      have hδ' : A * φ0 ^ (β - 1) * Real.exp ((α + μ) * x) ≤ δ ^ α := by
        have : (2 : ℝ) ^ (α * β / (β - 1)) = Real.exp ((α + μ) * x) := by
          rw [h2]; congr 1
          rw [hμ]; field_simp; ring
        rwa [this] at hδα
      refine hφb.trans ?_
      rw [div_le_iff₀ hL, hφ0β]
      have hE : Real.exp (-(α + μ) * x) * Real.exp (-μ * n * x * β) =
          Real.exp (-μ * ((n + 1 : ℕ) : ℝ) * x) * Real.exp (-((n : ℝ) + 1) * x * α) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        linear_combination (-(n : ℝ) * x) * hμβ
      have hA' : A * φ0 ^ (β - 1) ≤ δ ^ α * Real.exp (-(α + μ) * x) := by
        have h0 : Real.exp ((α + μ) * x) * Real.exp (-(α + μ) * x) = 1 := by
          rw [← Real.exp_add]; ring_nf; simp
        calc A * φ0 ^ (β - 1)
            = A * φ0 ^ (β - 1) * (Real.exp ((α + μ) * x) * Real.exp (-(α + μ) * x)) := by
              rw [h0, mul_one]
          _ ≤ δ ^ α * Real.exp (-(α + μ) * x) := by
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_right hδ' (Real.exp_pos _).le
      calc A * (φ0 * φ0 ^ (β - 1)) * Real.exp (-μ * n * x * β)
          = φ0 * (A * φ0 ^ (β - 1)) * Real.exp (-μ * n * x * β) := by ring
        _ ≤ φ0 * (δ ^ α * Real.exp (-(α + μ) * x)) * Real.exp (-μ * n * x * β) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_left hA' (hφ0 0)
        _ = φ0 * δ ^ α * (Real.exp (-(α + μ) * x) * Real.exp (-μ * n * x * β)) := by ring
        _ = φ0 * δ ^ α * (Real.exp (-μ * ((n + 1 : ℕ) : ℝ) * x) *
              Real.exp (-((n : ℝ) + 1) * x * α)) := by rw [hE]
        _ = φ0 * Real.exp (-μ * ((n + 1 : ℕ) : ℝ) * x) *
              (δ ^ α * Real.exp (-((n : ℝ) + 1) * x * α)) := by ring
  -- conclude
  have hle : ∀ n : ℕ, φ δ ≤ φ0 * Real.exp (-μ * (n : ℝ) * x) := fun n =>
    (hmono _ _ (hk_nonneg n) (hk_le n)).trans (key n)
  have hlim : Tendsto (fun n : ℕ => φ0 * Real.exp (-μ * n * x)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => Real.exp (-(μ * x) * n)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (-(μ * x)) * (n : ℝ)) atTop atBot :=
        tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by nlinarith)
      exact Real.tendsto_exp_atBot.comp h1
    simpa [mul_assoc, mul_comm, mul_left_comm] using this.const_mul φ0
  exact le_antisymm (ge_of_tendsto' hlim hle) (hφ0 δ)

end SubdiffusiveProcess.FractionalSup
