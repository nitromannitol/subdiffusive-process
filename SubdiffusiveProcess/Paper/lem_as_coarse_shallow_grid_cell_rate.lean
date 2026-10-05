module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_cell_moment
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Turn the exact sum of two source moment exponentials into one triadic
growth rate. This is numerical only; the source moments are proved elsewhere. -/
theorem lem_as_coarse_shallow_grid_cell_rate
    (q eta delta Cpoint Rpoint Cinv Rinv Cosc : ℝ) (k : ℕ)
    (hq : 1 ≤ q) (_heta : 0 ≤ eta) (_hdelta : 0 ≤ delta)
    (hCp : 0 < Cpoint) (_hRp : 0 < Rpoint)
    (hCi : 0 < Cinv) (_hRi : 0 < Rinv) (hCo : 0 < Cosc)
    (hRatePoint : Rpoint * ((2*q)+(2*q)^2) * delta^2 ≤
      (2*q) * eta * Real.log 3)
    (hRateInv : Rinv * ((2*q)+(2*q)^2) * delta^2 ≤
      (2*q) * eta * Real.log 3) :
    ENNReal.ofReal Cosc *
      (ENNReal.ofReal ((Cpoint * Real.exp (Rpoint *
        ((2*q)+(2*q)^2) * delta^2 * (k : ℝ))) ^ (2*q)⁻¹) +
       ENNReal.ofReal ((Cinv * Real.exp (Rinv *
        ((2*q)+(2*q)^2) * delta^2 * (k : ℝ))) ^ (2*q)⁻¹)) ≤
    ENNReal.ofReal
      ((Cosc * (Cpoint ^ (2*q)⁻¹ + Cinv ^ (2*q)⁻¹)) *
        (3 : ℝ) ^ (eta * (k : ℝ))) := by
  have h2q_pos : 0 < 2*q := by linarith
  have h2q_nonneg : 0 ≤ 2*q := by linarith
  have h2q_inv_pos : 0 < (2*q)⁻¹ := inv_pos.mpr h2q_pos
  have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have h3pos : 0 < (3 : ℝ) := by norm_num
  have h3nonneg : 0 ≤ (3 : ℝ) := by norm_num
  -- rate inequality multiplied by k
  have hRatePoint_k : Rpoint * ((2*q)+(2*q)^2) * delta^2 * (k : ℝ) ≤
      (2*q) * eta * Real.log 3 * (k : ℝ) := by
    nlinarith
  have hRateInv_k : Rinv * ((2*q)+(2*q)^2) * delta^2 * (k : ℝ) ≤
      (2*q) * eta * Real.log 3 * (k : ℝ) := by
    nlinarith
  -- apply exp monotonicity
  have hExpPoint : Real.exp (Rpoint * ((2*q)+(2*q)^2) * delta^2 * (k : ℝ)) ≤
      Real.exp ((2*q) * eta * Real.log 3 * (k : ℝ)) :=
    Real.exp_le_exp.mpr hRatePoint_k
  have hExpInv : Real.exp (Rinv * ((2*q)+(2*q)^2) * delta^2 * (k : ℝ)) ≤
      Real.exp ((2*q) * eta * Real.log 3 * (k : ℝ)) :=
    Real.exp_le_exp.mpr hRateInv_k
  -- simplify the RHS: exp(a * log 3) = 3^a
  have hExpSimpl : Real.exp ((2*q) * eta * Real.log 3 * (k : ℝ)) =
      (3 : ℝ) ^ ((2*q) * eta * (k : ℝ)) := by
    calc
      Real.exp ((2*q) * eta * Real.log 3 * (k : ℝ)) =
          Real.exp (Real.log 3 * ((2*q) * eta * (k : ℝ))) := by ring
      _ = (3 : ℝ) ^ ((2*q) * eta * (k : ℝ)) := by
        rw [Real.rpow_def_of_pos h3pos]
  -- combine: Cpoint * exp(...) ≤ Cpoint * 3^(...)
  have hPointMul : Cpoint * Real.exp (Rpoint * ((2*q)+(2*q)^2) * delta^2 * (k : ℝ)) ≤
      Cpoint * (3 : ℝ) ^ ((2*q) * eta * (k : ℝ)) :=
    mul_le_mul_of_nonneg_left (hExpPoint.trans hExpSimpl.le) hCp.le
  have hInvMul : Cinv * Real.exp (Rinv * ((2*q)+(2*q)^2) * delta^2 * (k : ℝ)) ≤
      Cinv * (3 : ℝ) ^ ((2*q) * eta * (k : ℝ)) :=
    mul_le_mul_of_nonneg_left (hExpInv.trans hExpSimpl.le) hCi.le
  -- raise to power (2q)⁻¹ using Real.mul_rpow
  have hPointPow : (Cpoint * Real.exp (Rpoint * ((2*q)+(2*q)^2) * delta^2 * (k : ℝ))) ^ (2*q)⁻¹ ≤
      (Cpoint * (3 : ℝ) ^ ((2*q) * eta * (k : ℝ))) ^ (2*q)⁻¹ :=
    Real.rpow_le_rpow (by positivity) hPointMul (by positivity : 0 ≤ (2*q)⁻¹)
  have hInvPow : (Cinv * Real.exp (Rinv * ((2*q)+(2*q)^2) * delta^2 * (k : ℝ))) ^ (2*q)⁻¹ ≤
      (Cinv * (3 : ℝ) ^ ((2*q) * eta * (k : ℝ))) ^ (2*q)⁻¹ :=
    Real.rpow_le_rpow (by positivity) hInvMul (by positivity : 0 ≤ (2*q)⁻¹)
  -- split the product inside the power
  have hPointSplit : (Cpoint * (3 : ℝ) ^ ((2*q) * eta * (k : ℝ))) ^ (2*q)⁻¹ =
      Cpoint ^ (2*q)⁻¹ * ((3 : ℝ) ^ ((2*q) * eta * (k : ℝ))) ^ (2*q)⁻¹ :=
    Real.mul_rpow hCp.le (Real.rpow_nonneg h3nonneg _)
  have hInvSplit : (Cinv * (3 : ℝ) ^ ((2*q) * eta * (k : ℝ))) ^ (2*q)⁻¹ =
      Cinv ^ (2*q)⁻¹ * ((3 : ℝ) ^ ((2*q) * eta * (k : ℝ))) ^ (2*q)⁻¹ :=
    Real.mul_rpow hCi.le (Real.rpow_nonneg h3nonneg _)
  -- combine the exponents: (3^(a))^(2q)⁻¹ = 3^(a * (2q)⁻¹)
  have hExpCombine : ((3 : ℝ) ^ ((2*q) * eta * (k : ℝ))) ^ (2*q)⁻¹ =
      (3 : ℝ) ^ (eta * (k : ℝ)) := by
    calc
      ((3 : ℝ) ^ ((2*q) * eta * (k : ℝ))) ^ (2*q)⁻¹ =
          (3 : ℝ) ^ (((2*q) * eta * (k : ℝ)) * (2*q)⁻¹) := by
        rw [← Real.rpow_mul h3nonneg ((2*q) * eta * (k : ℝ)) (2*q)⁻¹]
      _ = (3 : ℝ) ^ (eta * (k : ℝ)) := by
        congr 1
        field_simp [h2q_pos.ne']
  -- assemble the full point term bound
  have hPointTerm : ENNReal.ofReal ((Cpoint * Real.exp (Rpoint *
      ((2*q)+(2*q)^2) * delta^2 * (k : ℝ))) ^ (2*q)⁻¹) ≤
      ENNReal.ofReal (Cpoint ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    calc
      (Cpoint * Real.exp (Rpoint * ((2*q)+(2*q)^2) * delta^2 * (k : ℝ))) ^ (2*q)⁻¹ ≤
          (Cpoint * (3 : ℝ) ^ ((2*q) * eta * (k : ℝ))) ^ (2*q)⁻¹ := hPointPow
      _ = Cpoint ^ (2*q)⁻¹ * ((3 : ℝ) ^ ((2*q) * eta * (k : ℝ))) ^ (2*q)⁻¹ := hPointSplit
      _ = Cpoint ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ)) := by rw [hExpCombine]
  have hInvTerm : ENNReal.ofReal ((Cinv * Real.exp (Rinv *
      ((2*q)+(2*q)^2) * delta^2 * (k : ℝ))) ^ (2*q)⁻¹) ≤
      ENNReal.ofReal (Cinv ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    calc
      (Cinv * Real.exp (Rinv * ((2*q)+(2*q)^2) * delta^2 * (k : ℝ))) ^ (2*q)⁻¹ ≤
          (Cinv * (3 : ℝ) ^ ((2*q) * eta * (k : ℝ))) ^ (2*q)⁻¹ := hInvPow
      _ = Cinv ^ (2*q)⁻¹ * ((3 : ℝ) ^ ((2*q) * eta * (k : ℝ))) ^ (2*q)⁻¹ := hInvSplit
      _ = Cinv ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ)) := by rw [hExpCombine]
  -- sum the two bounds
  have hSum : ENNReal.ofReal ((Cpoint * Real.exp (Rpoint *
      ((2*q)+(2*q)^2) * delta^2 * (k : ℝ))) ^ (2*q)⁻¹) +
      ENNReal.ofReal ((Cinv * Real.exp (Rinv *
      ((2*q)+(2*q)^2) * delta^2 * (k : ℝ))) ^ (2*q)⁻¹) ≤
      ENNReal.ofReal (Cpoint ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ))) +
      ENNReal.ofReal (Cinv ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ))) :=
    add_le_add hPointTerm hInvTerm
  -- factor 3^(eta*k) out of the sum
  have hFactor : ENNReal.ofReal (Cpoint ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ))) +
      ENNReal.ofReal (Cinv ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ))) =
      ENNReal.ofReal ((Cpoint ^ (2*q)⁻¹ + Cinv ^ (2*q)⁻¹) * (3 : ℝ) ^ (eta * (k : ℝ))) := by
    have hpos1 : 0 ≤ Cpoint ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ)) := by positivity
    have hpos2 : 0 ≤ Cinv ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ)) := by positivity
    calc
      ENNReal.ofReal (Cpoint ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ))) +
          ENNReal.ofReal (Cinv ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ))) =
        ENNReal.ofReal (Cpoint ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ)) +
          Cinv ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ))) := by
        rw [ENNReal.ofReal_add hpos1 hpos2]
      _ = ENNReal.ofReal ((Cpoint ^ (2*q)⁻¹ + Cinv ^ (2*q)⁻¹) * (3 : ℝ) ^ (eta * (k : ℝ))) := by
        ring
  -- multiply by ENNReal.ofReal Cosc
  have hCo_nonneg : 0 ≤ ENNReal.ofReal Cosc := by positivity
  calc
    ENNReal.ofReal Cosc *
      (ENNReal.ofReal ((Cpoint * Real.exp (Rpoint *
        ((2*q)+(2*q)^2) * delta^2 * (k : ℝ))) ^ (2*q)⁻¹) +
       ENNReal.ofReal ((Cinv * Real.exp (Rinv *
        ((2*q)+(2*q)^2) * delta^2 * (k : ℝ))) ^ (2*q)⁻¹)) ≤
      ENNReal.ofReal Cosc *
        (ENNReal.ofReal (Cpoint ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ))) +
         ENNReal.ofReal (Cinv ^ (2*q)⁻¹ * (3 : ℝ) ^ (eta * (k : ℝ)))) :=
      mul_le_mul_of_nonneg_left hSum hCo_nonneg
    _ = ENNReal.ofReal Cosc *
        ENNReal.ofReal ((Cpoint ^ (2*q)⁻¹ + Cinv ^ (2*q)⁻¹) * (3 : ℝ) ^ (eta * (k : ℝ))) := by
      rw [hFactor]
    _ = ENNReal.ofReal (Cosc * ((Cpoint ^ (2*q)⁻¹ + Cinv ^ (2*q)⁻¹) * (3 : ℝ) ^ (eta * (k : ℝ)))) := by
      rw [ENNReal.ofReal_mul hCo.le]
    _ = ENNReal.ofReal
        ((Cosc * (Cpoint ^ (2*q)⁻¹ + Cinv ^ (2*q)⁻¹)) *
          (3 : ℝ) ^ (eta * (k : ℝ))) := by ring

end SubdiffusiveProcess.Paper
