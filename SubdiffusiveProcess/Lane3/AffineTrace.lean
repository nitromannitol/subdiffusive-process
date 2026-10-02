import SubdiffusiveProcess.Lane3.Forms
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Affine trace approximation, Lemma `mfd:lem-affine`

`mfd:lem-affine`.  The quantitative
content of the lemma is that the subdivision factor `L` may be chosen first
and the homogenization tolerance `ε_hom` afterwards so that
`C A_L^{2θ} B_L^{2(1−θ)} ≤ ϱ` (paper lines 3576-3586), where `A_L`, `B_L` are
the two rescaled bounds of paper lines 3560-3564 and
`θ = (α−β)/(α+d/2)` is the interpolation exponent of Lemma `mfd:lem-interp`.
-/

open Real

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

/-- `θ a₁ + (1−θ) b₁ = e_d`: the exponent of `L` in `A_L^θ B_L^{1−θ}` at
`ε_hom = 0` is exactly `affineExponent`, paper lines 3566-3570. -/
theorem affine_exponent_split (d alpha beta gamma zeta theta : ℝ)
    (hden : alpha + d / 2 ≠ 0)
    (htheta : theta = (alpha - beta) / (alpha + d / 2)) :
    ((d + zeta) / 2 - gamma * (d - 2) / 2 - 2 * gamma) * (2 * theta) +
        ((d + zeta) / 2 - gamma * (d - 2) / 2 - alpha * gamma) * (2 * (1 - theta)) =
      2 * affineExponent d alpha beta gamma zeta := by
  subst htheta
  unfold affineExponent
  field_simp
  ring

/-- A negative power of a large scale beats any constant. -/
theorem exists_one_lt_rpow_le {s c eps : ℝ} (hs : s < 0) (hc : 0 < c)
    (heps : 0 < eps) : ∃ L : ℝ, 1 < L ∧ c * L ^ s ≤ eps := by
  set K : ℝ := max 1 (Real.log (c / eps) / (-s)) with hK
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  refine ⟨Real.exp K, ?_, ?_⟩
  · have h0 : Real.exp 0 < Real.exp K := Real.exp_lt_exp.mpr hKpos
    simpa using h0
  · have hLpos : (0 : ℝ) < Real.exp K := Real.exp_pos K
    rw [Real.rpow_def_of_pos hLpos, Real.log_exp]
    have hneg : 0 < -s := by linarith
    have h2 : Real.log (c / eps) / (-s) ≤ K := le_max_right _ _
    have h3 : Real.log (c / eps) ≤ K * (-s) := (div_le_iff₀ hneg).mp h2
    have hlog : Real.log (eps / c) = -Real.log (c / eps) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    have hKs : K * s ≤ Real.log (eps / c) := by
      rw [hlog]
      nlinarith
    calc c * Real.exp (K * s) ≤ c * Real.exp (Real.log (eps / c)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hKs) hc.le
      _ = c * (eps / c) := by rw [Real.exp_log (by positivity)]
      _ = eps := by field_simp

theorem affine_trace_approximation
    (d : ℕ) (hd : 2 ≤ d) (Cc : ℝ) (hCc : 1 ≤ Cc)
    (alpha beta gamma zeta : ℝ)
    (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1)
    (hgamma : 0 < gamma) (hgamma1 : gamma < 1) (hzeta : 0 < zeta)
    (hneg : affineExponent (d : ℝ) alpha beta gamma zeta < 0)
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ L : ℝ, 1 < L ∧ ∃ ehom : ℝ, 0 < ehom ∧
      ∀ (A B theta Sq trace : ℝ),
        theta = (alpha - beta) / (alpha + (d : ℝ) / 2) →
        0 ≤ A → 0 ≤ B → 0 ≤ Sq →
        A ≤ Cc * L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - 2 * gamma) +
            Cc * ehom * L ^ (((d : ℝ) + zeta) / 2 + gamma) →
        B ≤ Cc * L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - alpha * gamma) →
        trace ≤ Cc * A ^ (2 * theta) * B ^ (2 * (1 - theta)) * Sq →
        trace ≤ rho * Sq := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hCc0 : (0 : ℝ) < Cc := lt_of_lt_of_le zero_lt_one hCc
  obtain ⟨L, hL1, hLbound⟩ :=
    exists_one_lt_rpow_le (s := 2 * affineExponent (d : ℝ) alpha beta gamma zeta)
      (c := 4 * Cc ^ 5) (eps := rho) (by linarith) (by positivity) hrho
  have hL0 : (0 : ℝ) < L := lt_trans zero_lt_one hL1
  set a1 : ℝ := ((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - 2 * gamma with ha1
  set a2 : ℝ := ((d : ℝ) + zeta) / 2 + gamma with ha2
  set b1 : ℝ := ((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - alpha * gamma with hb1
  refine ⟨L, hL1, L ^ (a1 - a2), Real.rpow_pos_of_pos hL0 _, ?_⟩
  intro A B theta Sq trace htheta hA0 hB0 hSq hA hB htr
  have hden : alpha + (d : ℝ) / 2 ≠ 0 := by nlinarith
  have hdenpos : (0 : ℝ) < alpha + (d : ℝ) / 2 := by nlinarith
  have hth0 : 0 < theta := by
    rw [htheta]; exact div_pos (by linarith) hdenpos
  have hth1 : theta ≤ 1 := by
    rw [htheta, div_le_one hdenpos]; linarith
  have hexp : a1 - a2 + a2 = a1 := by ring
  have hAsum : Cc * L ^ a1 + Cc * L ^ (a1 - a2) * L ^ a2 = 2 * (Cc * L ^ a1) := by
    rw [mul_assoc, ← Real.rpow_add hL0, hexp]; ring
  have hA2 : A ≤ 2 * (Cc * L ^ a1) := by rw [← hAsum]; exact hA
  have hApow : A ^ (2 * theta) ≤ (2 * (Cc * L ^ a1)) ^ (2 * theta) :=
    Real.rpow_le_rpow hA0 hA2 (by linarith)
  have hBpow : B ^ (2 * (1 - theta)) ≤ (Cc * L ^ b1) ^ (2 * (1 - theta)) :=
    Real.rpow_le_rpow hB0 hB (by linarith)
  have hL1nn : (0 : ℝ) ≤ L ^ a1 := (Real.rpow_pos_of_pos hL0 a1).le
  have hLb1nn : (0 : ℝ) ≤ L ^ b1 := (Real.rpow_pos_of_pos hL0 b1).le
  have hsplitA : (2 * (Cc * L ^ a1)) ^ (2 * theta) =
      (2 * Cc) ^ (2 * theta) * L ^ (a1 * (2 * theta)) := by
    rw [show 2 * (Cc * L ^ a1) = (2 * Cc) * L ^ a1 by ring,
      Real.mul_rpow (by positivity) hL1nn, ← Real.rpow_mul hL0.le]
  have hsplitB : (Cc * L ^ b1) ^ (2 * (1 - theta)) =
      Cc ^ (2 * (1 - theta)) * L ^ (b1 * (2 * (1 - theta))) := by
    rw [Real.mul_rpow hCc0.le hLb1nn, ← Real.rpow_mul hL0.le]
  have hmerge : L ^ (a1 * (2 * theta)) * L ^ (b1 * (2 * (1 - theta))) =
      L ^ (2 * affineExponent (d : ℝ) alpha beta gamma zeta) := by
    rw [← Real.rpow_add hL0]
    congr 1
    exact affine_exponent_split (d : ℝ) alpha beta gamma zeta theta hden htheta
  have hc1 : (2 * Cc) ^ (2 * theta) ≤ (2 * Cc) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hc2 : Cc ^ (2 * (1 - theta)) ≤ Cc ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hCc (by linarith)
  have he1 : (2 * Cc) ^ (2 : ℝ) = (2 * Cc) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (2 * Cc) 2]; norm_num
  have he2 : Cc ^ (2 : ℝ) = Cc ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast Cc 2]; norm_num
  have hLed : (0 : ℝ) < L ^ (2 * affineExponent (d : ℝ) alpha beta gamma zeta) :=
    Real.rpow_pos_of_pos hL0 _
  have hkey : Cc * A ^ (2 * theta) * B ^ (2 * (1 - theta)) ≤ rho := by
    have hpb : (0 : ℝ) ≤ B ^ (2 * (1 - theta)) := Real.rpow_nonneg hB0 _
    have hbase : (0 : ℝ) ≤ 2 * (Cc * L ^ a1) := by
      have := mul_nonneg hCc0.le hL1nn
      linarith
    have hb' : (0 : ℝ) ≤ Cc * (2 * (Cc * L ^ a1)) ^ (2 * theta) :=
      mul_nonneg hCc0.le (Real.rpow_nonneg hbase _)
    have hstep1 : Cc * A ^ (2 * theta) * B ^ (2 * (1 - theta)) ≤
        Cc * (2 * (Cc * L ^ a1)) ^ (2 * theta) * (Cc * L ^ b1) ^ (2 * (1 - theta)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hApow hCc0.le) hBpow hpb hb'
    have hstep2 : Cc * (2 * (Cc * L ^ a1)) ^ (2 * theta) * (Cc * L ^ b1) ^ (2 * (1 - theta))
        = Cc * ((2 * Cc) ^ (2 * theta) * Cc ^ (2 * (1 - theta))) *
          L ^ (2 * affineExponent (d : ℝ) alpha beta gamma zeta) := by
      rw [hsplitA, hsplitB, ← hmerge]; ring
    have hpos2 : (0 : ℝ) ≤ Cc ^ (2 * (1 - theta)) := Real.rpow_nonneg hCc0.le _
    have hmul : (2 * Cc) ^ (2 * theta) * Cc ^ (2 * (1 - theta)) ≤
        (2 * Cc) ^ (2 : ℕ) * Cc ^ (2 : ℕ) := by
      rw [← he1, ← he2]
      exact mul_le_mul hc1 hc2 hpos2 (Real.rpow_nonneg (by linarith) _)
    have hfin : Cc * ((2 * Cc) ^ (2 : ℕ) * Cc ^ (2 : ℕ)) = 4 * Cc ^ 5 := by ring
    have hstep3 : Cc * ((2 * Cc) ^ (2 * theta) * Cc ^ (2 * (1 - theta))) *
        L ^ (2 * affineExponent (d : ℝ) alpha beta gamma zeta) ≤
        4 * Cc ^ 5 * L ^ (2 * affineExponent (d : ℝ) alpha beta gamma zeta) := by
      rw [← hfin]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmul hCc0.le) hLed.le
    calc Cc * A ^ (2 * theta) * B ^ (2 * (1 - theta))
        ≤ Cc * (2 * (Cc * L ^ a1)) ^ (2 * theta) *
            (Cc * L ^ b1) ^ (2 * (1 - theta)) := hstep1
      _ = Cc * ((2 * Cc) ^ (2 * theta) * Cc ^ (2 * (1 - theta))) *
            L ^ (2 * affineExponent (d : ℝ) alpha beta gamma zeta) := hstep2
      _ ≤ 4 * Cc ^ 5 *
            L ^ (2 * affineExponent (d : ℝ) alpha beta gamma zeta) := hstep3
      _ ≤ rho := hLbound
  calc trace ≤ Cc * A ^ (2 * theta) * B ^ (2 * (1 - theta)) * Sq := htr
    _ ≤ rho * Sq := mul_le_mul_of_nonneg_right hkey hSq

end Lane3
end SubdiffusiveProcess
