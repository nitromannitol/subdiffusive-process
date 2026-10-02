import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Set
open scoped Topology
namespace SubdiffusiveProcess

/-- Balancing the two powers in a near/far estimate gives the exact interpolation exponent. -/
theorem interpolation_le_of_scale_bounds (s t A F a b X : ℝ)
    (ht : 0 < t) (hts : t < s) (hA : 0 ≤ A) (hF : 0 ≤ F)
    (ha : 0 ≤ a) (hab : a ≤ b) (hX : 0 ≤ X)
    (hbound : ∀ delta > (0 : ℝ),
      X ^ 2 ≤ a ^ 2 + A * delta ^ (2 * (s - t)) * b ^ 2 + F * delta ^ (-(2 * t)) * a ^ 2) :
    X ≤ Real.sqrt (1 + A + F) * a ^ (1 - t / s) * b ^ (t / s) := by
  have hs : 0 < s := ht.trans hts
  have hb : 0 ≤ b := ha.trans hab
  have htheta : 0 < t / s := div_pos ht hs
  have hone : t / s < 1 := (div_lt_one hs).mpr hts
  have hq : 0 < 2 * (s - t) := by linarith
  by_cases ha0 : a = 0
  · have hpow : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ (2 * (s - t))) atTop (𝓝 0) := by
      simpa only [Real.zero_rpow hq.ne'] using
        (Real.continuous_rpow_const hq.le).tendsto 0 |>.comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hlim : Tendsto (fun n : ℕ => A * (1 / ((n : ℝ) + 1)) ^ (2 * (s - t)) * b ^ 2)
        atTop (𝓝 0) := by simpa only [mul_zero, zero_mul] using (hpow.const_mul A).mul_const (b ^ 2)
    have hXsq : X ^ 2 ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Eventually.of_forall (fun n => by
        simpa only [ha0, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, add_zero] using
          hbound (1 / ((n : ℝ) + 1)) (by positivity)))
    have hx0 : X = 0 := by nlinarith
    rw [hx0]
    positivity
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbpos : 0 < b := hapos.trans_le hab
  let delta : ℝ := (a / b) ^ (1 / s)
  have hd : 0 < delta := Real.rpow_pos_of_pos (div_pos hapos hbpos) _
  let D : ℝ := a ^ (1 - t / s) * b ^ (t / s)
  have hD : 0 ≤ D := mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _)
  have hscale (q : ℝ) : delta ^ q = a ^ (q / s) * b ^ (-(q / s)) := by
    dsimp [delta]
    rw [← Real.rpow_mul (div_nonneg ha hb),
      show (1 / s) * q = q / s by ring, Real.div_rpow ha hb,
      div_eq_mul_inv, ← Real.rpow_neg hb]
  have hDsq : D ^ 2 = a ^ (2 * (1 - t / s)) * b ^ (2 * (t / s)) := by
    dsimp [D]
    rw [mul_pow, ← Real.rpow_mul_natCast ha, ← Real.rpow_mul_natCast hb]
    congr 2 <;> ring
  have hnear : delta ^ (2 * (s - t)) * b ^ 2 = D ^ 2 := by
    rw [hscale, hDsq, mul_assoc, ← Real.rpow_natCast b 2, ← Real.rpow_add hbpos]
    congr 2
    all_goals field_simp
    all_goals ring
  have hfar : delta ^ (-(2 * t)) * a ^ 2 = D ^ 2 := by
    rw [hscale, hDsq]
    calc
      _ = (a ^ (-(2 * t) / s) * a ^ (2 : ℝ)) * b ^ (-(-(2 * t) / s)) := by
        rw [Real.rpow_two]
        ring
      _ = _ := by
        rw [← Real.rpow_add hapos]
        congr 2
        all_goals field_simp
        all_goals ring
  have haD : a ≤ D := by
    calc
      a = a ^ (1 - t / s) * a ^ (t / s) := by
        rw [← Real.rpow_add hapos, sub_add_cancel, Real.rpow_one]
      _ ≤ D := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha hab htheta.le)
        (Real.rpow_nonneg ha _)
  have hsq : X ^ 2 ≤ (1 + A + F) * D ^ 2 := by
    have h := hbound delta hd
    rw [mul_assoc A, hnear, mul_assoc F, hfar] at h
    have haSq : a ^ 2 ≤ D ^ 2 := (sq_le_sq₀ ha hD).mpr haD
    nlinarith
  have hc : 0 ≤ 1 + A + F := by linarith
  rw [mul_assoc]
  apply (sq_le_sq₀ hX (mul_nonneg (Real.sqrt_nonneg _) hD)).mp
  change X ^ 2 ≤ (Real.sqrt (1 + A + F) * D) ^ 2
  rw [mul_pow, Real.sq_sqrt hc]
  exact hsq

end SubdiffusiveProcess
