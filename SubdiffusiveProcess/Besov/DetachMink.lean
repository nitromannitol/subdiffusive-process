module

public import Mathlib

@[expose] public section

/-!
# Minkowski inequalities on a finite weighted set (detach inequality)

`sqrt (c * Σ_S (Σ_i f i S)^2) ≤ Σ_i sqrt (c * Σ_S (f i S)^2)` and its `tsum` version, for `c ≥ 0`.
-/

namespace SubdiffusiveProcess.Besov.Detach

/-- Finite Minkowski for the weighted `ℓ²` norm over a finite set. -/
theorem sqrt_weighted_sq_sum_le {ι κ : Type*} (𝒮 : Finset ι) (J : Finset κ) (c : ℝ) (hc : 0 ≤ c)
    (f : κ → ι → ℝ) :
    Real.sqrt (c * ∑ S ∈ 𝒮, (∑ i ∈ J, f i S) ^ 2) ≤
      ∑ i ∈ J, Real.sqrt (c * ∑ S ∈ 𝒮, (f i S) ^ 2) := by
  classical
  have h2 : ∀ (u v : ι → ℝ),
      Real.sqrt (c * ∑ S ∈ 𝒮, (u S + v S) ^ 2) ≤
        Real.sqrt (c * ∑ S ∈ 𝒮, u S ^ 2) + Real.sqrt (c * ∑ S ∈ 𝒮, v S ^ 2) := by
    intro u v
    have hsu : 0 ≤ ∑ S ∈ 𝒮, u S ^ 2 := by positivity
    have hsv : 0 ≤ ∑ S ∈ 𝒮, v S ^ 2 := by positivity
    have hcs2 : (∑ S ∈ 𝒮, u S * v S) ^ 2 ≤ (∑ S ∈ 𝒮, u S ^ 2) * (∑ S ∈ 𝒮, v S ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq 𝒮 u v
    have h1 : ∑ S ∈ 𝒮, u S * v S ≤
        Real.sqrt (∑ S ∈ 𝒮, u S ^ 2) * Real.sqrt (∑ S ∈ 𝒮, v S ^ 2) := by
      have h := Real.le_sqrt_of_sq_le hcs2
      rwa [Real.sqrt_mul hsu] at h
    have hAB : Real.sqrt (c * ∑ S ∈ 𝒮, u S ^ 2) * Real.sqrt (c * ∑ S ∈ 𝒮, v S ^ 2)
        = c * (Real.sqrt (∑ S ∈ 𝒮, u S ^ 2) * Real.sqrt (∑ S ∈ 𝒮, v S ^ 2)) := by
      rw [Real.sqrt_mul hc (∑ S ∈ 𝒮, u S ^ 2), Real.sqrt_mul hc (∑ S ∈ 𝒮, v S ^ 2)]
      have hcc : Real.sqrt c * Real.sqrt c = c := by rw [← pow_two, Real.sq_sqrt hc]
      calc Real.sqrt c * Real.sqrt (∑ S ∈ 𝒮, u S ^ 2) * (Real.sqrt c * Real.sqrt (∑ S ∈ 𝒮, v S ^ 2))
          = (Real.sqrt c * Real.sqrt c) * (Real.sqrt (∑ S ∈ 𝒮, u S ^ 2) * Real.sqrt (∑ S ∈ 𝒮, v S ^ 2)) := by ring
        _ = c * (Real.sqrt (∑ S ∈ 𝒮, u S ^ 2) * Real.sqrt (∑ S ∈ 𝒮, v S ^ 2)) := by rw [hcc]
    have hcs : c * (∑ S ∈ 𝒮, u S * v S) ≤
        Real.sqrt (c * ∑ S ∈ 𝒮, u S ^ 2) * Real.sqrt (c * ∑ S ∈ 𝒮, v S ^ 2) := by
      rw [hAB]
      exact mul_le_mul_of_nonneg_left h1 hc
    have hstep : ∀ S ∈ 𝒮, (u S + v S) ^ 2 = u S ^ 2 + 2 * (u S * v S) + v S ^ 2 := fun S _ => by ring
    have hsum : ∑ S ∈ 𝒮, (u S + v S) ^ 2 =
        (∑ S ∈ 𝒮, u S ^ 2) + 2 * (∑ S ∈ 𝒮, u S * v S) + ∑ S ∈ 𝒮, v S ^ 2 := by
      rw [Finset.sum_congr rfl hstep]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    have hsqA : Real.sqrt (c * ∑ S ∈ 𝒮, u S ^ 2) ^ 2 = c * ∑ S ∈ 𝒮, u S ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hsqB : Real.sqrt (c * ∑ S ∈ 𝒮, v S ^ 2) ^ 2 = c * ∑ S ∈ 𝒮, v S ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hmain : c * ∑ S ∈ 𝒮, (u S + v S) ^ 2 ≤
        (Real.sqrt (c * ∑ S ∈ 𝒮, u S ^ 2) + Real.sqrt (c * ∑ S ∈ 𝒮, v S ^ 2)) ^ 2 := by
      nlinarith [hsum, hsqA, hsqB, hcs]
    calc Real.sqrt (c * ∑ S ∈ 𝒮, (u S + v S) ^ 2)
        ≤ Real.sqrt ((Real.sqrt (c * ∑ S ∈ 𝒮, u S ^ 2) + Real.sqrt (c * ∑ S ∈ 𝒮, v S ^ 2)) ^ 2) :=
          Real.sqrt_le_sqrt hmain
      _ = Real.sqrt (c * ∑ S ∈ 𝒮, u S ^ 2) + Real.sqrt (c * ∑ S ∈ 𝒮, v S ^ 2) :=
          Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  induction J using Finset.induction_on with
  | empty => simp
  | insert a J ha ih =>
      have h2a := h2 (f a) (fun S => ∑ i ∈ J, f i S)
      simp only [Finset.sum_insert ha] at h2a ⊢
      linarith [h2a, ih]

/-- `tsum` Minkowski for nonnegative summable families on a finite set. -/
theorem sqrt_weighted_sq_tsum_le {ι : Type*} (𝒮 : Finset ι) (c : ℝ) (hc : 0 ≤ c)
    (a : ℕ → ι → ℝ) (_ha0 : ∀ k S, 0 ≤ a k S) (ha : ∀ S ∈ 𝒮, Summable (fun k => a k S))
    (hb : Summable (fun k => Real.sqrt (c * ∑ S ∈ 𝒮, (a k S) ^ 2))) :
    Real.sqrt (c * ∑ S ∈ 𝒮, (∑' k, a k S) ^ 2) ≤ ∑' k, Real.sqrt (c * ∑ S ∈ 𝒮, (a k S) ^ 2) := by
  have hL : Filter.Tendsto (fun K => Real.sqrt (c * ∑ S ∈ 𝒮, (∑ i ∈ Finset.range K, a i S) ^ 2)) Filter.atTop
      (nhds (Real.sqrt (c * ∑ S ∈ 𝒮, (∑' k, a k S) ^ 2))) := by
    apply Filter.Tendsto.sqrt
    have hF : Filter.Tendsto (fun K => ∑ S ∈ 𝒮, (∑ i ∈ Finset.range K, a i S) ^ 2) Filter.atTop
        (nhds (∑ S ∈ 𝒮, (∑' k, a k S) ^ 2)) := by
      apply tendsto_finsetSum
      intro S hS
      exact ((ha S hS).hasSum.tendsto_sum_nat).pow 2
    exact tendsto_const_nhds.mul hF
  have hbound : ∀ K, Real.sqrt (c * ∑ S ∈ 𝒮, (∑ i ∈ Finset.range K, a i S) ^ 2)
      ≤ ∑' k, Real.sqrt (c * ∑ S ∈ 𝒮, (a k S) ^ 2) := by
    intro K
    calc Real.sqrt (c * ∑ S ∈ 𝒮, (∑ i ∈ Finset.range K, a i S) ^ 2)
        ≤ ∑ i ∈ Finset.range K, Real.sqrt (c * ∑ S ∈ 𝒮, (a i S) ^ 2) :=
          sqrt_weighted_sq_sum_le 𝒮 (Finset.range K) c hc a
      _ ≤ ∑' k, Real.sqrt (c * ∑ S ∈ 𝒮, (a k S) ^ 2) :=
          Summable.sum_le_tsum (Finset.range K) (fun i _ => Real.sqrt_nonneg _) hb
  exact le_of_tendsto' hL hbound

/-- Constants factor out of the weighted `ℓ²` norm. -/
theorem sqrt_weighted_mul_left {ι : Type*} (𝒮 : Finset ι) (c C : ℝ) (_hc : 0 ≤ c) (hC : 0 ≤ C)
    (t : ι → ℝ) :
    Real.sqrt (c * ∑ S ∈ 𝒮, (C * t S) ^ 2) = C * Real.sqrt (c * ∑ S ∈ 𝒮, (t S) ^ 2) := by
  have hsum : ∑ S ∈ 𝒮, (C * t S) ^ 2 = C ^ 2 * ∑ S ∈ 𝒮, (t S) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  rw [show c * ∑ S ∈ 𝒮, (C * t S) ^ 2 = C ^ 2 * (c * ∑ S ∈ 𝒮, (t S) ^ 2) by rw [hsum]; ring]
  rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]

end SubdiffusiveProcess.Besov.Detach
