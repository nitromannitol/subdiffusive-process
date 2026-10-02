import Mathlib

/-!
# Scalar bookkeeping for the paper-normalized coarse-graining estimates with right-hand side

The paper's norms carry a leading `s ^ (1 / 2)` on the Hilbertian seminorms.  The three displays of
`l.coarse.graining.RHS` are converted from the CoarseGraining library's normalization by the
elementary inequalities below (no analysis; only exponent arithmetic in `s ∈ (0, 1)`).
-/

namespace SubdiffusiveProcess.CoarseRHS

theorem rpow_mul_rpow' {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    Real.rpow s a * Real.rpow s b = Real.rpow s (a + b) := by
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_add hs]

theorem rpow_le_rpow_of_ge {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {t u : ℝ} (htu : t ≤ u) :
    Real.rpow s u ≤ Real.rpow s t := by
  simp only [Real.rpow_eq_pow]
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 htu

/-- Gradient display: library normalization to paper normalization. -/
theorem scalar_grad {s N E B S PS W lf L Cp Kd : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hCp : 0 ≤ Cp) (hKd : 0 ≤ Kd)
    (hlf : 0 ≤ lf) (hE : 0 ≤ E) (hL : 0 < L) (hW : 0 ≤ W) (hS0 : 0 ≤ S)
    (hN : N ≤ Cp * Real.rpow s (-(3 / 2 : ℝ)) * lf * E + Cp * Real.rpow s (-3 : ℝ) * L⁻¹ * B)
    (hB : B ≤ Kd * W * S)
    (hS : PS = Real.rpow s (1 / 2 : ℝ) * S) :
    Real.rpow s (1 / 2 : ℝ) * N ≤
      (Cp * (1 + Kd)) * Real.rpow s (-(3 / 2 : ℝ)) * lf * E +
        (Cp * (1 + Kd)) * Real.rpow s (-3 : ℝ) * L⁻¹ * (W * PS) := by
  set r := Real.rpow s (1 / 2 : ℝ) with hr
  have hrp : 0 < r := Real.rpow_pos_of_pos hs _
  have h1 : r * Real.rpow s (-(3 / 2 : ℝ)) = Real.rpow s (-1 : ℝ) := by
    rw [hr, rpow_mul_rpow' hs]; norm_num
  have hneg : Real.rpow s (-1 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) :=
    rpow_le_rpow_of_ge hs hs1.le (by norm_num)
  have hp3 : 0 ≤ Real.rpow s (-3 : ℝ) := (Real.rpow_pos_of_pos hs _).le
  have hpm : 0 ≤ Real.rpow s (-(3 / 2 : ℝ)) := (Real.rpow_pos_of_pos hs _).le
  have hLinv : 0 ≤ L⁻¹ := inv_nonneg.mpr hL.le
  have hrB : r * B ≤ Kd * W * PS := by
    calc r * B ≤ r * (Kd * W * S) := mul_le_mul_of_nonneg_left hB hrp.le
      _ = Kd * W * (r * S) := by ring
      _ = Kd * W * PS := by rw [hS]
  have hE1 : r * Real.rpow s (-(3 / 2 : ℝ)) * (Cp * lf * E) ≤
      Real.rpow s (-(3 / 2 : ℝ)) * (Cp * lf * E) := by
    rw [h1]; gcongr
  calc
    r * N ≤ r * (Cp * Real.rpow s (-(3 / 2 : ℝ)) * lf * E +
        Cp * Real.rpow s (-3 : ℝ) * L⁻¹ * B) := mul_le_mul_of_nonneg_left hN hrp.le
    _ = r * Real.rpow s (-(3 / 2 : ℝ)) * (Cp * lf * E) +
        Real.rpow s (-3 : ℝ) * (Cp * L⁻¹) * (r * B) := by ring
    _ ≤ Real.rpow s (-(3 / 2 : ℝ)) * (Cp * lf * E) +
        Real.rpow s (-3 : ℝ) * (Cp * L⁻¹) * (Kd * W * PS) := by
      gcongr
    _ ≤ _ := by
      have hPS : 0 ≤ PS := by rw [hS]; positivity
      have h0 : 0 ≤ Real.rpow s (-(3 / 2 : ℝ)) * (Cp * lf * E) := by positivity
      have h2 : Real.rpow s (-3 : ℝ) * (Cp * L⁻¹) * (Kd * W * PS) ≤
          (Cp * (1 + Kd)) * Real.rpow s (-3 : ℝ) * L⁻¹ * (W * PS) := by
        have h0' : 0 ≤ Real.rpow s (-3 : ℝ) * (Cp * L⁻¹) * (W * PS) := by positivity
        nlinarith [mul_nonneg hKd h0']
      have h3 : Real.rpow s (-(3 / 2 : ℝ)) * (Cp * lf * E) ≤
          (Cp * (1 + Kd)) * Real.rpow s (-(3 / 2 : ℝ)) * lf * E := by
        nlinarith [mul_nonneg hKd h0]
      linarith

/-- Flux display: library normalization to paper normalization. -/
theorem scalar_flux {s N E B S PS W lf U Cw Kd : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hCw : 0 ≤ Cw) (hKd : 0 ≤ Kd)
    (hlf : 0 ≤ lf) (hU : 0 ≤ U) (hE : 0 ≤ E) (hW : 0 ≤ W) (hS0 : 0 ≤ S) (hB0 : 0 ≤ B)
    (hN : N ≤ Cw * s⁻¹ * U * E + Cw * Real.rpow s (-(5 / 2 : ℝ)) * U * lf * B)
    (hB : B ≤ Kd * W * S)
    (hS : PS = Real.rpow s (1 / 2 : ℝ) * S) :
    Real.rpow s (1 / 2 : ℝ) * N ≤
      (Cw * (1 + Kd)) * Real.rpow s (-(3 / 2 : ℝ)) * U * E +
        (Cw * (1 + Kd)) * Real.rpow s (-(9 / 2 : ℝ)) * (U * lf) * (W * PS) := by
  set r := Real.rpow s (1 / 2 : ℝ) with hr
  have hrp : 0 < r := Real.rpow_pos_of_pos hs _
  have hinv : s⁻¹ = Real.rpow s (-1 : ℝ) := by simp [Real.rpow_neg_one]
  have h1 : r * s⁻¹ ≤ Real.rpow s (-(3 / 2 : ℝ)) := by
    rw [hinv, hr, rpow_mul_rpow' hs]
    exact rpow_le_rpow_of_ge hs hs1.le (by norm_num)
  have h2 : Real.rpow s (-(5 / 2 : ℝ)) ≤ Real.rpow s (-(9 / 2 : ℝ)) :=
    rpow_le_rpow_of_ge hs hs1.le (by norm_num)
  have hp5 : 0 ≤ Real.rpow s (-(5 / 2 : ℝ)) := (Real.rpow_pos_of_pos hs _).le
  have hp9 : 0 ≤ Real.rpow s (-(9 / 2 : ℝ)) := (Real.rpow_pos_of_pos hs _).le
  have hp3 : 0 ≤ Real.rpow s (-(3 / 2 : ℝ)) := (Real.rpow_pos_of_pos hs _).le
  have hPS : 0 ≤ PS := by rw [hS]; positivity
  have hrB : r * B ≤ Kd * W * PS := by
    calc r * B ≤ r * (Kd * W * S) := mul_le_mul_of_nonneg_left hB hrp.le
      _ = Kd * W * (r * S) := by ring
      _ = Kd * W * PS := by rw [hS]
  calc
    r * N ≤ r * (Cw * s⁻¹ * U * E + Cw * Real.rpow s (-(5 / 2 : ℝ)) * U * lf * B) :=
      mul_le_mul_of_nonneg_left hN hrp.le
    _ = Cw * (r * s⁻¹) * U * E + Cw * Real.rpow s (-(5 / 2 : ℝ)) * U * lf * (r * B) := by ring
    _ ≤ Cw * Real.rpow s (-(3 / 2 : ℝ)) * U * E +
        Cw * Real.rpow s (-(9 / 2 : ℝ)) * U * lf * (Kd * W * PS) := by
      gcongr
    _ ≤ _ := by
      have e1 : 0 ≤ Cw * Real.rpow s (-(3 / 2 : ℝ)) * U * E := by positivity
      have e2 : 0 ≤ Cw * Real.rpow s (-(9 / 2 : ℝ)) * (U * lf) * (W * PS) := by positivity
      nlinarith [mul_nonneg hKd e1, mul_nonneg hKd e2]

/-- The `B_g`-contribution of the energy display. -/
theorem scalar_energy_T1 {s lf Bg Sg PSg W Kd : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hKd : 0 ≤ Kd) (hlf : 0 ≤ lf) (hW : 0 ≤ W) (hSg0 : 0 ≤ Sg)
    (hBg : Bg ≤ Kd * W * Sg) (hPSg : PSg = Real.rpow s (1 / 2 : ℝ) * Sg) :
    Real.rpow s (-(3 / 2 : ℝ)) * lf * Bg ≤ Kd * Real.rpow s (-3 : ℝ) * lf * (W * PSg) := by
  set ρ := Real.rpow s (-(1 / 2 : ℝ)) with hρ
  have hrρ : Real.rpow s (1 / 2 : ℝ) * ρ = 1 := by
    rw [hρ, rpow_mul_rpow' hs]; norm_num
  have hSg : Sg = ρ * PSg := by
    rw [hPSg]
    calc Sg = (ρ * Real.rpow s (1 / 2 : ℝ)) * Sg := by rw [mul_comm ρ, hrρ, one_mul]
      _ = ρ * (Real.rpow s (1 / 2 : ℝ) * Sg) := by ring
  have e32 : Real.rpow s (-(3 / 2 : ℝ)) * ρ = Real.rpow s (-2 : ℝ) := by
    rw [hρ, rpow_mul_rpow' hs]; norm_num
  have le23 : Real.rpow s (-2 : ℝ) ≤ Real.rpow s (-3 : ℝ) :=
    rpow_le_rpow_of_ge hs hs1.le (by norm_num)
  have p32 : 0 ≤ Real.rpow s (-(3 / 2 : ℝ)) := (Real.rpow_pos_of_pos hs _).le
  have hPS0 : 0 ≤ Kd * W * lf := by positivity
  calc Real.rpow s (-(3 / 2 : ℝ)) * lf * Bg
      ≤ Real.rpow s (-(3 / 2 : ℝ)) * lf * (Kd * W * Sg) := by gcongr
    _ = Kd * (Real.rpow s (-(3 / 2 : ℝ)) * ρ) * lf * (W * PSg) := by rw [hSg]; ring
    _ = Kd * Real.rpow s (-2 : ℝ) * lf * (W * PSg) := by rw [e32]
    _ ≤ Kd * Real.rpow s (-3 : ℝ) * lf * (W * PSg) := by
        have : 0 ≤ Kd * lf * (W * PSg) := by
          have hPS : 0 ≤ PSg := by
            rw [hPSg]; exact mul_nonneg (Real.rpow_pos_of_pos hs _).le hSg0
          positivity
        nlinarith [mul_le_mul_of_nonneg_right le23 this]

/-- The `∇h`-contribution of the energy display. -/
theorem scalar_energy_T2 {s Us U N2 A0 Bh Sh PSh W Fp Kd : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hKd : 0 ≤ Kd) (hUs0 : 0 ≤ Us) (hUsU : Us ≤ U)
    (hW : 0 ≤ W) (hFp0 : 0 ≤ Fp) (hBh0 : 0 ≤ Bh) (hA00 : 0 ≤ A0)
    (hN2 : N2 = A0 + Bh) (hA0 : A0 ≤ W * Fp) (hBh : Bh ≤ Kd * W * Sh)
    (hPSh : PSh = Real.rpow s (1 / 2 : ℝ) * Sh) (hPShFp : PSh ≤ Fp) :
    Real.rpow s (-(1 / 2 : ℝ)) * Us * N2 ≤
      (1 + Kd) * Real.rpow s (-(3 / 2 : ℝ)) * U * (W * Fp) := by
  set ρ := Real.rpow s (-(1 / 2 : ℝ)) with hρ
  have hρp : 0 < ρ := Real.rpow_pos_of_pos hs _
  have hrρ : Real.rpow s (1 / 2 : ℝ) * ρ = 1 := by
    rw [hρ, rpow_mul_rpow' hs]; norm_num
  have hSh : Sh = ρ * PSh := by
    rw [hPSh]
    calc Sh = (ρ * Real.rpow s (1 / 2 : ℝ)) * Sh := by rw [mul_comm ρ, hrρ, one_mul]
      _ = ρ * (Real.rpow s (1 / 2 : ℝ) * Sh) := by ring
  have e12 : ρ * ρ = Real.rpow s (-1 : ℝ) := by
    rw [hρ, rpow_mul_rpow' hs]; norm_num
  have le1 : Real.rpow s (-1 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) :=
    rpow_le_rpow_of_ge hs hs1.le (by norm_num)
  have le12 : ρ ≤ Real.rpow s (-(3 / 2 : ℝ)) :=
    rpow_le_rpow_of_ge hs hs1.le (by norm_num)
  have hN2le : N2 ≤ (1 + Kd * ρ) * (W * Fp) := by
    rw [hN2]
    calc A0 + Bh ≤ W * Fp + Kd * W * Sh := add_le_add hA0 hBh
      _ = W * Fp + Kd * ρ * (W * PSh) := by rw [hSh]; ring
      _ ≤ W * Fp + Kd * ρ * (W * Fp) := by gcongr
      _ = (1 + Kd * ρ) * (W * Fp) := by ring
  have hN20 : 0 ≤ N2 := by rw [hN2]; positivity
  have hWF : 0 ≤ W * Fp := by positivity
  have hU : 0 ≤ U := hUs0.trans hUsU
  calc ρ * Us * N2
      ≤ ρ * U * ((1 + Kd * ρ) * (W * Fp)) := by gcongr
    _ = (ρ + Kd * (ρ * ρ)) * U * (W * Fp) := by ring
    _ = (ρ + Kd * Real.rpow s (-1 : ℝ)) * U * (W * Fp) := by rw [e12]
    _ ≤ (Real.rpow s (-(3 / 2 : ℝ)) + Kd * Real.rpow s (-(3 / 2 : ℝ))) * U * (W * Fp) := by
        gcongr
    _ = (1 + Kd) * Real.rpow s (-(3 / 2 : ℝ)) * U * (W * Fp) := by ring

/-- Final constant bookkeeping for the energy display. -/
theorem scalar_energy_final {Ev Ew X Y T1 T2 Cd Cn Kd : ℝ}
    (hCd : 0 ≤ Cd) (hCn : 0 ≤ Cn) (hKd : 0 ≤ Kd) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hEv : Ev ≤ Cd * T1 + Cd * T2) (hEw : Ew ≤ Cn * T1)
    (hT1 : T1 ≤ Kd * X) (hT2 : T2 ≤ (1 + Kd) * Y) :
    Ev + Ew ≤ ((Cd + Cn) * (1 + Kd)) * X + ((Cd + Cn) * (1 + Kd)) * Y := by
  have h1 : Cd * T1 ≤ Cd * (Kd * X) := mul_le_mul_of_nonneg_left hT1 hCd
  have h2 : Cn * T1 ≤ Cn * (Kd * X) := mul_le_mul_of_nonneg_left hT1 hCn
  have h3 : Cd * T2 ≤ Cd * ((1 + Kd) * Y) := mul_le_mul_of_nonneg_left hT2 hCd
  have a1 : 0 ≤ Cd * Kd * X := by positivity
  have a2 : 0 ≤ Cn * Kd * X := by positivity
  have a3 : 0 ≤ Cn * Kd * Y := by positivity
  have a4 : 0 ≤ Cn * Y := by positivity
  have a5 : 0 ≤ Cd * Kd * Y := by positivity
  have a6 : 0 ≤ Cd * X := by positivity
  have a7 : 0 ≤ Cn * X := by positivity
  nlinarith

/-- Monotonicity in the leading constant of a two-term display. -/
theorem coeff_mono {c c' p q U E V r : ℝ} (hc : c ≤ c') (hp : 0 ≤ p) (hU : 0 ≤ U) (hE : 0 ≤ E)
    (hq : 0 ≤ q) (hV : 0 ≤ V) (hr : 0 ≤ r) :
    c * p * U * E + c * q * V * r ≤ c' * p * U * E + c' * q * V * r := by
  gcongr

end SubdiffusiveProcess.CoarseRHS
