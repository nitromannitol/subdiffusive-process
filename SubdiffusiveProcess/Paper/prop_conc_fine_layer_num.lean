import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The decay exponent of the fine-layer step: with the layer-norm loss `r^{-γ}`, `γ = b/12`, the deletion and the
Efron--Stein envelopes are `≤ K δ (M - m) r^{3b/8}`, `r = 3^{-n} ≤ 1`, the endpoint gap entering linearly and the
disorder `δ` linearly.  Pure real analysis; the constants `Cex, Cm, B, Cd, cA, CES` are arbitrary
nonnegative reals. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

theorem aux_prop_conc_fine_layer_num_sqrt_rpow (r b : ℝ) (hr : 0 < r) :
    Real.sqrt (r ^ b) = r ^ (b / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]; congr 1; ring

theorem prop_conc_fine_layer_num (r b Cex Cm B Cd cA CES delta gap : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hb : 0 < b) (hCex : 0 ≤ Cex) (hCm : 0 ≤ Cm) (hB : 0 ≤ B) (hCd : 0 ≤ Cd) (hcA : 0 ≤ cA)
    (hCES : 0 ≤ CES) (hdelta : 0 ≤ delta) (hgap : 0 ≤ gap) :
    2 * (Cex * gap * (Cd * r ^ b + cA * Real.sqrt (Cd * r ^ b)) *
        ((Cm * delta * r ^ (-(b / 12))) * (1 + B))) +
      2 * CES * ((Real.sqrt (2 * (Cex + Cex)) * Cex * Real.sqrt Cex * Real.sqrt 2 * gap *
          Real.sqrt (Cd * r ^ b + Cd * r ^ b)) *
        ((Real.sqrt (Cm * r ^ (-(b / 12))) * (Cm * delta * r ^ (-(b / 12))) +
            Real.sqrt (Cm * delta ^ 2 * r ^ (-(b / 12))) * (Cm * r ^ (-(b / 12)))) * (1 + B))) ≤
      (2 * Cex * Cm * (1 + B) * (Cd + cA * Real.sqrt Cd) +
        2 * CES * (2 * (Real.sqrt (2 * (Cex + Cex)) * Cex * Real.sqrt Cex * Real.sqrt 2 *
          Real.sqrt (2 * Cd) * (Cm * Real.sqrt Cm) * (1 + B)))) * delta * gap * r ^ (3 * b / 8) := by
  have hrb : ∀ x : ℝ, 0 < x → r ^ x > 0 := fun x _ => Real.rpow_pos_of_pos hr x
  have hg : (0 : ℝ) < b / 12 := by positivity
  -- exponent facts
  have e1 : r ^ b ≤ r ^ (b / 2) := Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have e2 : r ^ (b / 2) * r ^ (-(b / 12)) ≤ r ^ (3 * b / 8) := by
    rw [← Real.rpow_add hr]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have hsA : Real.sqrt (Cd * r ^ b) = Real.sqrt Cd * r ^ (b / 2) := by
    rw [Real.sqrt_mul hCd, aux_prop_conc_fine_layer_num_sqrt_rpow r b hr]
  have hsAA : Real.sqrt (Cd * r ^ b + Cd * r ^ b) = Real.sqrt (2 * Cd) * r ^ (b / 2) := by
    rw [show Cd * r ^ b + Cd * r ^ b = (2 * Cd) * r ^ b by ring, Real.sqrt_mul (by positivity),
      aux_prop_conc_fine_layer_num_sqrt_rpow r b hr]
  have hMa : Real.sqrt (Cm * r ^ (-(b / 12))) = Real.sqrt Cm * r ^ (-(b / 12) / 2) := by
    rw [Real.sqrt_mul hCm, aux_prop_conc_fine_layer_num_sqrt_rpow r _ hr]
  have hMe : Real.sqrt (Cm * delta ^ 2 * r ^ (-(b / 12))) =
      Real.sqrt Cm * delta * r ^ (-(b / 12) / 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCm, Real.sqrt_sq hdelta,
      aux_prop_conc_fine_layer_num_sqrt_rpow r _ hr]
  have hsum : (Real.sqrt (Cm * r ^ (-(b / 12))) * (Cm * delta * r ^ (-(b / 12))) +
        Real.sqrt (Cm * delta ^ 2 * r ^ (-(b / 12))) * (Cm * r ^ (-(b / 12)))) =
      2 * (Cm * Real.sqrt Cm) * delta * (r ^ (-(b / 12) / 2) * r ^ (-(b / 12))) := by
    rw [hMa, hMe]; ring
  have hcomb : r ^ (b / 2) * (r ^ (-(b / 12) / 2) * r ^ (-(b / 12))) ≤ r ^ (3 * b / 8) := by
    rw [← Real.rpow_add hr, ← Real.rpow_add hr]
    refine le_of_eq ?_
    congr 1; ring
  rw [hsA, hsAA, hsum]
  set c₀ : ℝ := Real.sqrt (2 * (Cex + Cex)) * Cex * Real.sqrt Cex * Real.sqrt 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  have hrx : 0 < r ^ (b / 2) := hrb _ (by positivity)
  have hrg : 0 < r ^ (-(b / 12)) := Real.rpow_pos_of_pos hr _
  -- first term
  have t1 : 2 * (Cex * gap * (Cd * r ^ b + cA * (Real.sqrt Cd * r ^ (b / 2))) *
        ((Cm * delta * r ^ (-(b / 12))) * (1 + B))) ≤
      2 * Cex * Cm * (1 + B) * (Cd + cA * Real.sqrt Cd) * delta * gap * r ^ (3 * b / 8) := by
    have h1 : Cd * r ^ b + cA * (Real.sqrt Cd * r ^ (b / 2)) ≤ (Cd + cA * Real.sqrt Cd) * r ^ (b / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left e1 hCd]
    have h2 : 2 * (Cex * gap * (Cd * r ^ b + cA * (Real.sqrt Cd * r ^ (b / 2))) *
        ((Cm * delta * r ^ (-(b / 12))) * (1 + B))) ≤
        2 * (Cex * gap * ((Cd + cA * Real.sqrt Cd) * r ^ (b / 2)) *
        ((Cm * delta * r ^ (-(b / 12))) * (1 + B))) := by
      gcongr
    refine h2.trans ?_
    have : 2 * (Cex * gap * ((Cd + cA * Real.sqrt Cd) * r ^ (b / 2)) *
        ((Cm * delta * r ^ (-(b / 12))) * (1 + B))) =
        (2 * Cex * Cm * (1 + B) * (Cd + cA * Real.sqrt Cd) * delta * gap) *
          (r ^ (b / 2) * r ^ (-(b / 12))) := by ring
    rw [this]
    have : 2 * Cex * Cm * (1 + B) * (Cd + cA * Real.sqrt Cd) * delta * gap * r ^ (3 * b / 8) =
        (2 * Cex * Cm * (1 + B) * (Cd + cA * Real.sqrt Cd) * delta * gap) * r ^ (3 * b / 8) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left e2 (by positivity)
  have t2 : 2 * CES * ((c₀ * gap * (Real.sqrt (2 * Cd) * r ^ (b / 2))) *
        ((2 * (Cm * Real.sqrt Cm) * delta * (r ^ (-(b / 12) / 2) * r ^ (-(b / 12)))) * (1 + B))) ≤
      2 * CES * (2 * (c₀ * Real.sqrt (2 * Cd) * (Cm * Real.sqrt Cm) * (1 + B))) * delta * gap *
        r ^ (3 * b / 8) := by
    have : 2 * CES * ((c₀ * gap * (Real.sqrt (2 * Cd) * r ^ (b / 2))) *
        ((2 * (Cm * Real.sqrt Cm) * delta * (r ^ (-(b / 12) / 2) * r ^ (-(b / 12)))) * (1 + B))) =
        (2 * CES * (2 * (c₀ * Real.sqrt (2 * Cd) * (Cm * Real.sqrt Cm) * (1 + B))) * delta * gap) *
          (r ^ (b / 2) * (r ^ (-(b / 12) / 2) * r ^ (-(b / 12)))) := by ring
    rw [this]
    have h3 : 2 * CES * (2 * (c₀ * Real.sqrt (2 * Cd) * (Cm * Real.sqrt Cm) * (1 + B))) * delta * gap *
        r ^ (3 * b / 8) = (2 * CES * (2 * (c₀ * Real.sqrt (2 * Cd) * (Cm * Real.sqrt Cm) * (1 + B))) *
          delta * gap) * r ^ (3 * b / 8) := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left hcomb (by positivity)
  calc _ ≤ 2 * Cex * Cm * (1 + B) * (Cd + cA * Real.sqrt Cd) * delta * gap * r ^ (3 * b / 8) +
      2 * CES * (2 * (c₀ * Real.sqrt (2 * Cd) * (Cm * Real.sqrt Cm) * (1 + B))) * delta * gap *
        r ^ (3 * b / 8) := add_le_add t1 t2
    _ = _ := by ring

end
end Paper
