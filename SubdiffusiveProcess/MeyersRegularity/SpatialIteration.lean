module

public import SubdiffusiveProcess.MeyersRegularity.Basic

@[expose] public section

/-! Interior Meyers regularity: SpatialIteration. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

/-- Bounded terminal terms disappear in a geometric recurrence. -/
theorem geometric_recurrence_bound {Y : ℕ → ℝ} {A B θ k : ℝ}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hk : 0 ≤ k) (hkhalf : k ≤ 1/2)
    (hbound : ∀ n, Y n ≤ θ^n * B)
    (hstep : ∀ n, Y n ≤ Y (n+1) + A*k^n) :
    Y 0 ≤ 2*A := by
  have hsum : ∀ n, (∑ i ∈ Finset.range n, k^i) ≤ 2 := by
    intro n
    have hn := geom_sum_mul_neg k n
    have hnonneg : 0 ≤ ∑ i ∈ Finset.range n, k^i :=
      Finset.sum_nonneg (fun i _ => pow_nonneg hk i)
    have hpow : 0 ≤ k^n := pow_nonneg hk n
    have hh : 1/2 ≤ 1-k := by linarith
    have hm := mul_le_mul_of_nonneg_left hh hnonneg
    nlinarith
  have hind : ∀ n, Y 0 ≤ Y n + A*(∑ i ∈ Finset.range n, k^i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hh := hstep n
      nlinarith
  have hfinal : ∀ n, Y 0 ≤ θ^n * B + 2*A := by
    intro n
    have hh := hind n
    have hm := mul_le_mul_of_nonneg_left (hsum n) hA
    linarith [hbound n]
  have ht : Tendsto (fun n : ℕ => θ^n * B + 2*A) atTop (𝓝 (2*A)) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).mul_const B).add_const (2*A)
  exact ge_of_tendsto ht (Filter.Eventually.of_forall hfinal)


/-- Iterate a finite-valued spatial inequality before taking the truncation limit. -/
theorem spatial_iteration {β A B θ : ℝ} {X : ℝ → ℝ}
    (hβ : 0 ≤ β) (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 ≤ θ)
    (hsmall : θ * (2 : ℝ)^β ≤ 1/2)
    (hX : ∀ r ∈ Icc (1 : ℝ) (3/2), 0 ≤ X r ∧ X r ≤ B)
    (hstep : ∀ r s : ℝ, 1 ≤ r → r < s → s ≤ 3/2 →
      X r ≤ θ * X s + A * (s-r)^(-β)) :
    X 1 ≤ 2 * (4 : ℝ)^β * A := by
  let r : ℕ → ℝ := fun n => 3/2 - (1/2)*(1/2)^n
  have hr : ∀ n, r n ∈ Icc (1 : ℝ) (3/2) := by
    intro n
    have hn0 : 0 ≤ (1/2 : ℝ)^n := by positivity
    have hn1 : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp only [r]
    constructor <;> linarith
  have hgap : ∀ n, r (n+1)-r n = (1/4)*(1/2)^n := by
    intro n
    dsimp only [r]
    rw [pow_succ]
    ring
  have hlt : ∀ n, r n < r (n+1) := by
    intro n
    have hh : 0 < r (n+1)-r n := by rw [hgap]; positivity
    linarith
  have hgap_pow : ∀ n, (r (n+1)-r n)^(-β) = (4 : ℝ)^β * ((2 : ℝ)^β)^n := by
    intro n
    rw [hgap, Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1/2),
      Real.rpow_neg_eq_inv_rpow, Real.rpow_neg_eq_inv_rpow]
    norm_num
  have ht : θ ≤ 1/2 := by
    have htwo : 1 ≤ (2 : ℝ)^β := Real.one_le_rpow (by norm_num) hβ
    have hh := mul_le_mul_of_nonneg_left htwo hθ
    nlinarith
  let Y : ℕ → ℝ := fun n => θ^n * X (r n)
  have hybound : ∀ n, Y n ≤ θ^n * B := by
    intro n
    exact mul_le_mul_of_nonneg_left (hX (r n) (hr n)).2 (pow_nonneg hθ n)
  have hystep : ∀ n, Y n ≤ Y (n+1) + ((4 : ℝ)^β*A)*(θ*(2 : ℝ)^β)^n := by
    intro n
    have hh := hstep (r n) (r (n+1)) (hr n).1 (hlt n) (hr (n+1)).2
    calc
      Y n ≤ θ^n * (θ*X (r (n+1)) + A*(r (n+1)-r n)^(-β)) :=
        mul_le_mul_of_nonneg_left hh (pow_nonneg hθ n)
      _ = _ := by
        rw [hgap_pow, mul_pow]
        dsimp only [Y]
        rw [pow_succ]
        ring
  have hh := geometric_recurrence_bound (Y := Y) (A := (4 : ℝ)^β*A) (B := B)
    (by positivity) hB hθ (by linarith : θ < 1)
    (mul_nonneg hθ (Real.rpow_nonneg (by norm_num) _)) hsmall hybound hystep
  have hr0 : r 0 = 1 := by norm_num [r]
  simpa [Y, hr0, mul_assoc] using hh


end SubdiffusiveProcess.MeyersRegularity
