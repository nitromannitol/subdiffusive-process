import SubdiffusiveProcess.FiniteStopping.WeightTransfer

/-! The sourced comparison at a stage of the observation tree for the INFRARED-FREE coefficient `A^0 = e^{-H} A`
(paper `\label{mfd:lem-finite-source-comparison}`, last paragraph).  The source solution `u` solves the equation of
`A^0_S`; regularity (`Reg`) is the one of `A^0` (branch `infrared = false` of `lem_finite_good_cell`), and the
normalized trace closeness is the one of the characterized coefficient `A` (`trace_close model H`), transferred to the
weights `wA` by `respOn_zero_bounds`; the reference scalar of `A^0` is that of `A` times `w(z)`, so `w(z)` cancels in the
ratio `r_{N,M}(k)`, at the price of the factor `e^{2c}` (`c` the oscillation of `H` on the cell). -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

theorem conjunct2_core_src_gen
    (r sT sS sR Cfin eta Q Eparent Kf X Y dreal : ℝ)
    (hr : 0 < r) (hsT : 0 < sT) (hsS : 0 < sS) (hsR : 0 < sR) (hCfin : 0 < Cfin) (heta : 0 < eta)
    (hQ0 : 0 ≤ Q) (hE0 : 0 ≤ Eparent) (hKf : 0 ≤ Kf)
    (hQ : Q ≤ Cfin * r ^ (((2 : ℝ) - dreal) / 2) * sR ^ (-(1 : ℝ) / 2) * Real.sqrt Eparent +
      Cfin * r ^ (2 : ℝ) * sR⁻¹ * Kf)
    (hTrace : |X / (r ^ (dreal - 2) * sT) - Y / (r ^ (dreal - 2) * sS)| ≤ eta * Q ^ 2) :
    X ≤ (sT / sS) * Y +
      2 * Cfin ^ 2 * eta * (sT / sR) * (Eparent + r ^ (dreal + 2) * sR⁻¹ * Kf ^ 2) := by
  set rp := r ^ (dreal - 2) with hrp_def
  have hrp : 0 < rp := Real.rpow_pos_of_pos hr _
  have hstep : X / (rp * sT) ≤ Y / (rp * sS) + eta * Q ^ 2 := by
    have h2 := (abs_le.mp hTrace).2
    linarith only [h2]
  have heqX : rp * sT * (X / (rp * sT)) = X := by
    field_simp
  have heqY : rp * sT * (Y / (rp * sS)) = (sT / sS) * Y := by
    field_simp
  have hmul : rp * sT * (X / (rp * sT)) ≤ rp * sT * (Y / (rp * sS) + eta * Q ^ 2) :=
    mul_le_mul_of_nonneg_left hstep (mul_pos hrp hsT).le
  rw [heqX, mul_add, heqY] at hmul
  set a := Cfin * r ^ (((2 : ℝ) - dreal) / 2) * sR ^ (-(1 : ℝ) / 2) * Real.sqrt Eparent with ha_def
  set b := Cfin * r ^ (2 : ℝ) * sR⁻¹ * Kf with hb_def
  have ha0 : 0 ≤ a := by
    rw [ha_def]
    have : 0 ≤ Cfin * r ^ (((2 : ℝ) - dreal) / 2) * sR ^ (-(1 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg hCfin.le (Real.rpow_nonneg hr.le _)) (Real.rpow_nonneg hsR.le _)
    exact mul_nonneg this (Real.sqrt_nonneg _)
  have hb0 : 0 ≤ b := by
    rw [hb_def]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCfin.le (Real.rpow_nonneg hr.le _))
      (inv_nonneg.2 hsR.le)) hKf
  have hQsq : Q ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    have h1 : Q ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
    nlinarith only [h1, sq_nonneg (a - b)]
  have ha2 : a ^ 2 = Cfin ^ 2 * r ^ (2 - dreal) * sR⁻¹ * Eparent := by
    rw [ha_def]
    have hexpand : (Cfin * r ^ (((2 : ℝ) - dreal) / 2) * sR ^ (-(1 : ℝ) / 2) *
        Real.sqrt Eparent) ^ 2 =
        Cfin ^ 2 * (r ^ (((2 : ℝ) - dreal) / 2)) ^ 2 * (sR ^ (-(1 : ℝ) / 2)) ^ 2 *
          (Real.sqrt Eparent) ^ 2 := by ring
    rw [hexpand]
    have hr2 : (r ^ (((2 : ℝ) - dreal) / 2)) ^ 2 = r ^ (2 - dreal) := by
      rw [← Real.rpow_natCast (r ^ (((2 : ℝ) - dreal) / 2)) 2, ← Real.rpow_mul hr.le]
      norm_num
    have hs2 : (sR ^ (-(1 : ℝ) / 2)) ^ 2 = sR⁻¹ := by
      rw [← Real.rpow_natCast (sR ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul hsR.le]
      norm_num
      rw [Real.rpow_neg hsR.le, Real.rpow_one]
    have he2 : (Real.sqrt Eparent) ^ 2 = Eparent := Real.sq_sqrt hE0
    rw [hr2, hs2, he2]
  have hb2 : b ^ 2 = Cfin ^ 2 * r ^ (4 : ℝ) * sR⁻¹ ^ 2 * Kf ^ 2 := by
    rw [hb_def]
    have hr4 : (r ^ (2 : ℝ)) ^ 2 = r ^ (4 : ℝ) := by
      rw [← Real.rpow_natCast (r ^ (2 : ℝ)) 2, ← Real.rpow_mul hr.le]
      norm_num
    calc (Cfin * r ^ (2 : ℝ) * sR⁻¹ * Kf) ^ 2
        = Cfin ^ 2 * (r ^ (2 : ℝ)) ^ 2 * sR⁻¹ ^ 2 * Kf ^ 2 := by ring
      _ = _ := by rw [hr4]
  have hrr : rp * r ^ (2 - dreal) = 1 := by
    rw [hrp_def, ← Real.rpow_add hr]
    norm_num
  have hrr2 : rp * r ^ (4 : ℝ) = r ^ (dreal + 2) := by
    rw [hrp_def, ← Real.rpow_add hr]
    congr 1
    ring
  have herr : rp * sT * (eta * Q ^ 2) ≤
      2 * Cfin ^ 2 * eta * (sT / sR) * (Eparent + r ^ (dreal + 2) * sR⁻¹ * Kf ^ 2) := by
    have hstep2 : rp * sT * (eta * Q ^ 2) ≤
        rp * sT * (eta * (2 * a ^ 2 + 2 * b ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQsq heta.le) (mul_pos hrp hsT).le
    rw [ha2, hb2] at hstep2
    have heq : rp * sT * (eta * (2 * (Cfin ^ 2 * r ^ (2 - dreal) * sR⁻¹ * Eparent) +
        2 * (Cfin ^ 2 * r ^ (4 : ℝ) * sR⁻¹ ^ 2 * Kf ^ 2))) =
        2 * Cfin ^ 2 * eta * (sT / sR) * (Eparent * (rp * r ^ (2 - dreal)) +
          (rp * r ^ (4 : ℝ)) * sR⁻¹ * Kf ^ 2) := by
      rw [div_eq_mul_inv]; ring
    rw [heq, hrr, hrr2, mul_one] at hstep2
    exact hstep2
  linarith only [hmul, herr]


/-- Algebra of the weight transfer. -/
theorem conjunct2_core_src_zero
    (r sT sS wz e Cfin eta Q Eparent Kf X Y X0 Y0 dreal : ℝ)
    (hr : 0 < r) (hsT : 0 < sT) (hsS : 0 < sS) (hwz : 0 < wz) (he : 1 ≤ e) (hCfin : 0 < Cfin)
    (heta : 0 < eta) (hQ0 : 0 ≤ Q) (hE0 : 0 ≤ Eparent) (hKf : 0 ≤ Kf)
    (hQ : Q ≤ Cfin * r ^ (((2 : ℝ) - dreal) / 2) * (sS * wz) ^ (-(1 : ℝ) / 2) * Real.sqrt Eparent +
      Cfin * r ^ (2 : ℝ) * (sS * wz)⁻¹ * Kf)
    (hTrace : |X / (r ^ (dreal - 2) * sT) - Y / (r ^ (dreal - 2) * sS)| ≤ eta * Q ^ 2)
    (hX0 : X0 ≤ e * (wz * X)) (hY : Y ≤ (e / wz) * Y0) (hY0 : 0 ≤ Y0) :
    X0 ≤ e ^ 2 * (sT / sS) * Y0 +
      2 * Cfin ^ 2 * eta * e * (sT / sS) *
        (Eparent + r ^ (dreal + 2) * (sS * wz)⁻¹ * Kf ^ 2) := by
  have hcore := conjunct2_core_src_gen r sT sS (sS * wz) Cfin eta Q Eparent Kf X Y dreal hr hsT hsS
    (mul_pos hsS hwz) hCfin heta hQ0 hE0 hKf hQ hTrace
  have hepos : 0 < e := lt_of_lt_of_le one_pos he
  have hstep : e * (wz * X) ≤ e * (wz * ((sT / sS) * Y +
      2 * Cfin ^ 2 * eta * (sT / (sS * wz)) * (Eparent + r ^ (dreal + 2) * (sS * wz)⁻¹ * Kf ^ 2))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcore hwz.le) hepos.le
  have hY' : wz * ((sT / sS) * Y) ≤ wz * ((sT / sS) * ((e / wz) * Y0)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY (div_nonneg hsT.le hsS.le)) hwz.le
  have e1 : e * (wz * ((sT / sS) * ((e / wz) * Y0))) = e ^ 2 * (sT / sS) * Y0 := by
    field_simp
  have e2 : e * (wz * (2 * Cfin ^ 2 * eta * (sT / (sS * wz)) *
      (Eparent + r ^ (dreal + 2) * (sS * wz)⁻¹ * Kf ^ 2))) =
      2 * Cfin ^ 2 * eta * e * (sT / sS) * (Eparent + r ^ (dreal + 2) * (sS * wz)⁻¹ * Kf ^ 2) := by
    field_simp
  have h3 : e * (wz * ((sT / sS) * Y)) ≤ e * (wz * ((sT / sS) * ((e / wz) * Y0))) :=
    mul_le_mul_of_nonneg_left hY' hepos.le
  calc X0 ≤ e * (wz * X) := hX0
    _ ≤ e * (wz * ((sT / sS) * Y +
      2 * Cfin ^ 2 * eta * (sT / (sS * wz)) * (Eparent + r ^ (dreal + 2) * (sS * wz)⁻¹ * Kf ^ 2))) := hstep
    _ = e * (wz * ((sT / sS) * Y)) + e * (wz * (2 * Cfin ^ 2 * eta * (sT / (sS * wz)) *
      (Eparent + r ^ (dreal + 2) * (sS * wz)⁻¹ * Kf ^ 2))) := by ring
    _ ≤ e * (wz * ((sT / sS) * ((e / wz) * Y0))) + e * (wz * (2 * Cfin ^ 2 * eta * (sT / (sS * wz)) *
      (Eparent + r ^ (dreal + 2) * (sS * wz)⁻¹ * Kf ^ 2))) := by linarith only [h3]
    _ = _ := by rw [e1, e2]

end SubdiffusiveProcess.FiniteStopping
