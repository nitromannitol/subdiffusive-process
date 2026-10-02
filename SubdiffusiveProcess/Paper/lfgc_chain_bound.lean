import SubdiffusiveProcess.Paper.lfgc_chain_prob

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Numerical bounds for the chain events

With `ρ = 3^{-a/2}`, `K = 32 Cδ / (1 - ρ)`, `(a/2) p log 3 ≥ R W₀` and `K^p ≤ e^{-2 R W₀}/8`,
every Chebyshev term of the chain is at most `e^{-R W₀ (ℓ+2)}/8`.
-/

open MeasureTheory Real
open scoped ENNReal

namespace Paper
theorem aux_lfgc_chain_bound_three_rpow_eq_rho_pow {a : ℝ} (ℓ : ℕ) :
    (3 : ℝ) ^ (-(a * (ℓ : ℝ))) = ((3 : ℝ) ^ (-a / 2)) ^ (2 * ℓ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1; push_cast; ring

theorem aux_lfgc_chain_bound_rho_rpow_le {a p R W : ℝ} (hc : R * W ≤ a / 2 * p * Real.log 3) :
    ((3 : ℝ) ^ (-a / 2)) ^ p ≤ Real.exp (-(R * W)) := by
  rw [← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [Real.log_pos (show (1 : ℝ) < 3 by norm_num)]

theorem aux_lfgc_chain_bound_ennreal_ratio_rpow {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hp : 0 ≤ p) :
    (ENNReal.ofReal x / ENNReal.ofReal y) ^ p = ENNReal.ofReal ((x / y) ^ p) := by
  rw [← ENNReal.ofReal_div_of_pos hy, ENNReal.ofReal_rpow_of_nonneg (div_nonneg hx hy.le) hp]

/-- The key geometric bound: `(K ρ^ℓ)^p ≤ e^{-R W (ℓ+2)}/8`. -/
theorem aux_lfgc_chain_bound_geom_term_le {a p R W K : ℝ} (hp : 0 ≤ p) (hK : 0 ≤ K)
    (hc : R * W ≤ a / 2 * p * Real.log 3) (hKp : K ^ p ≤ Real.exp (-(2 * R * W)) / 8) (ℓ : ℕ) :
    (K * ((3 : ℝ) ^ (-a / 2)) ^ ℓ) ^ p ≤ Real.exp (-(R * W * ((ℓ : ℝ) + 2))) / 8 := by
  set ρ := (3 : ℝ) ^ (-a / 2)
  have hρ : 0 ≤ ρ := by positivity
  rw [Real.mul_rpow hK (pow_nonneg hρ ℓ), ← Real.rpow_natCast ρ ℓ, ← Real.rpow_mul hρ,
    mul_comm (ℓ : ℝ) p, Real.rpow_mul hρ, Real.rpow_natCast]
  have h1 := aux_lfgc_chain_bound_rho_rpow_le hc
  have h2 : (ρ ^ p) ^ ℓ ≤ (Real.exp (-(R * W))) ^ ℓ :=
    pow_le_pow_left₀ (by positivity) h1 ℓ
  rw [← Real.exp_nat_mul] at h2
  calc K ^ p * (ρ ^ p) ^ ℓ ≤ (Real.exp (-(2 * R * W)) / 8) * Real.exp (↑ℓ * -(R * W)) :=
        mul_le_mul hKp h2 (by positivity) (by positivity)
    _ = Real.exp (-(R * W * ((ℓ : ℝ) + 2))) / 8 := by
        rw [div_mul_eq_mul_div, ← Real.exp_add]; congr 2; ring

end Paper
namespace Paper
variable {Ω : Type*} [MeasurableSpace Ω]

theorem lfgc_chain_bound (P : Measure Ω) (X Z : Ω → ℝ) (hXm : AEStronglyMeasurable X P)
    (Yb : ℕ → Ω → ℝ) (hYbm : ∀ h, AEStronglyMeasurable (Yb h) P) {a p Cδ R W : ℝ} (ha : 0 < a)
    (hp : 1 ≤ p) (hCδ : 0 ≤ Cδ)
    (herr : ∀ h : ℕ, 1 ≤ h → eLpNorm (fun ω => X ω - Yb h ω) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cδ * (3 : ℝ) ^ (-(a * (h : ℝ)))))
    (ℓs : ℕ) (hℓs : 1 ≤ ℓs) (Obad : Set Ω) (hZ : ∀ ω ∉ Obad, |Z ω - X ω| ≤ 1 / 32)
    (hc : R * W ≤ a / 2 * p * Real.log 3)
    (hKp : (32 * Cδ / (1 - (3 : ℝ) ^ (-a / 2))) ^ p ≤ Real.exp (-(2 * R * W)) / 8)
    (hbase : P {ω | 1 / 32 < X ω} ≤ ENNReal.ofReal (Real.exp (-(2 * R * W)) / 8))
    (hbad : P Obad ≤ ENNReal.ofReal (Real.exp (-(R * W * ((ℓs : ℝ) + 2))) / 8)) :
    ∀ ℓ ≤ ℓs, P (chainEvent (aux_lfgc_chain_prob_chainY Yb Z ℓs) (aux_lfgc_chain_num_chainTheta ((3 : ℝ) ^ (-a / 2)) ℓs) ℓ) ≤
      ENNReal.ofReal (Real.exp (-(R * W * ((ℓ : ℝ) + 2))) / 4) := by
  set ρ := (3 : ℝ) ^ (-a / 2) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hp0 : 0 ≤ p := by linarith
  set K := 32 * Cδ / (1 - ρ)
  have hK : 0 ≤ K := div_nonneg (by positivity) (by linarith)
  obtain ⟨h0, hmid, hend⟩ := lfgc_chain_prob P X Z hXm Yb hYbm hp hCδ herr ℓs hℓs Obad hZ ρ hρ0 hρ1
  have hgeom := aux_lfgc_chain_bound_geom_term_le hp0 hK hc hKp
  have e8 : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal (x / 8) + ENNReal.ofReal (x / 8) = ENNReal.ofReal (x / 4) := by
    intro x hx; rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hterm : ∀ (ℓ : ℕ) (x : ℝ), 0 ≤ x → x ≤ K * ρ ^ ℓ →
      ENNReal.ofReal (x ^ p) ≤ ENNReal.ofReal (Real.exp (-(R * W * ((ℓ : ℝ) + 2))) / 8) := by
    intro ℓ x hx hxK
    refine ENNReal.ofReal_le_ofReal ((Real.rpow_le_rpow hx hxK hp0).trans (hgeom ℓ))
  have hsq : ∀ ℓ : ℕ, (3 : ℝ) ^ (-(a * (ℓ : ℝ))) = ρ ^ (2 * ℓ) := fun ℓ => aux_lfgc_chain_bound_three_rpow_eq_rho_pow ℓ
  have h32 : ∀ ℓ : ℕ, 32 * (Cδ * ρ ^ (2 * ℓ)) ≤ K * ρ ^ ℓ := by
    intro ℓ
    have hρl : ρ ^ (2 * ℓ) ≤ ρ ^ ℓ := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
    have hl0 : 0 ≤ ρ ^ ℓ := pow_nonneg hρ0.le ℓ
    have h1 : 1 ≤ 1 / (1 - ρ) := by rw [le_div_iff₀ (by linarith)]; linarith
    have hc0 : 0 ≤ 32 * Cδ * ρ ^ ℓ := by positivity
    calc 32 * (Cδ * ρ ^ (2 * ℓ)) ≤ 32 * Cδ * ρ ^ ℓ := by nlinarith
      _ = 32 * Cδ * ρ ^ ℓ * 1 := by ring
      _ ≤ 32 * Cδ * ρ ^ ℓ * (1 / (1 - ρ)) := mul_le_mul_of_nonneg_left h1 hc0
      _ = K * ρ ^ ℓ := by simp only [K]; ring
  intro ℓ hℓ
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · refine h0.trans ?_
    rw [aux_lfgc_chain_bound_ennreal_ratio_rpow (by positivity) (by norm_num) hp0]
    have : Cδ * (3 : ℝ) ^ (-(a * (1 : ℝ))) / (1 / 32) ≤ K * ρ ^ 0 := by
      have e := hsq 1
      simp only [Nat.cast_one] at e
      rw [e]
      have := h32 1
      have hρ2 : ρ ^ (2 * 1) ≤ ρ ^ 0 := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
      have hl : K * ρ ^ 1 ≤ K * ρ ^ 0 := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)) hK
      rw [div_eq_mul_inv, show ((1 : ℝ) / 32)⁻¹ = 32 by norm_num]
      linarith
    have ht := hterm 0 _ (by positivity) this
    simp only [Nat.cast_zero, zero_add] at ht ⊢
    calc P {ω | 1 / 32 < X ω} + ENNReal.ofReal ((Cδ * (3 : ℝ) ^ (-(a * 1)) / (1 / 32)) ^ p)
        ≤ ENNReal.ofReal (Real.exp (-(2 * R * W)) / 8) +
            ENNReal.ofReal (Real.exp (-(R * W * 2)) / 8) := add_le_add hbase ht
      _ = ENNReal.ofReal (Real.exp (-(R * W * 2)) / 4) := by
          rw [show 2 * R * W = R * W * 2 by ring]; exact e8 _ (Real.exp_pos _).le
  · rcases lt_or_eq_of_le hℓ with hlt | heq
    · refine (hmid ℓ hpos hlt).trans ?_
      have hden : 0 < (1 / 16) * (1 - ρ) * ρ ^ ℓ := by
        have := pow_pos hρ0 ℓ; nlinarith
      rw [aux_lfgc_chain_bound_ennreal_ratio_rpow (by positivity) hden hp0]
      refine (hterm ℓ _ (by positivity) ?_).trans ?_
      · rw [div_le_iff₀ hden, hsq, hsq]
        have hmono : ρ ^ (2 * (ℓ + 1)) ≤ ρ ^ (2 * ℓ) :=
          pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
        have e : ρ ^ (2 * ℓ) = ρ ^ ℓ * ρ ^ ℓ := by rw [← pow_add]; ring_nf
        have hne : 1 - ρ ≠ 0 := by linarith
        have hR : K * ρ ^ ℓ * ((1 / 16) * (1 - ρ) * ρ ^ ℓ) = 2 * Cδ * (ρ ^ ℓ * ρ ^ ℓ) := by
          simp only [K]; field_simp; ring
        push_cast
        rw [hR, ← e]
        nlinarith [mul_le_mul_of_nonneg_left hmono hCδ]
      · refine ENNReal.ofReal_le_ofReal ?_
        have := Real.exp_pos (-(R * W * ((ℓ : ℝ) + 2)))
        linarith
    · rw [heq]
      refine hend.trans ?_
      rw [aux_lfgc_chain_bound_ennreal_ratio_rpow (by positivity) (by norm_num) hp0]
      have : Cδ * (3 : ℝ) ^ (-(a * (ℓs : ℝ))) / (1 / 32) ≤ K * ρ ^ ℓs := by
        rw [hsq, div_eq_mul_inv, show ((1 : ℝ) / 32)⁻¹ = 32 by norm_num]
        linarith [h32 ℓs]
      calc P Obad + ENNReal.ofReal ((Cδ * (3 : ℝ) ^ (-(a * (ℓs : ℝ))) / (1 / 32)) ^ p)
          ≤ ENNReal.ofReal (Real.exp (-(R * W * ((ℓs : ℝ) + 2))) / 8) +
              ENNReal.ofReal (Real.exp (-(R * W * ((ℓs : ℝ) + 2))) / 8) :=
            add_le_add hbad (hterm ℓs _ (by positivity) this)
        _ = _ := e8 _ (Real.exp_pos _).le

end Paper
