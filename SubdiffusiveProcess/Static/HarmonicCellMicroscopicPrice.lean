module

public import SubdiffusiveProcess.Static.HarmonicCellJoiningArithmetic

@[expose] public section

/-! # Polynomial envelope price for reflected microscopic energy -/

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The native squared-data upper bound after substituting the local
correction budget and a bounded smooth boundary gradient. -/
def harmonicCellMicroscopicPrice (d : ℕ) (C J eps T R G : ℝ) : ℝ :=
  R * (eps / T) ^ (1 / 2 : ℝ) * C *
    (2 * ((eps / T) ^ d)⁻¹ * (3 : ℝ) ^ d *
        (2 * (R * G * eps ^ ((d : ℝ) - 1 / 4) + (d : ℝ) ^ 2 * (2 * (eps / T)) ^ d)) +
      2 * (J * R ^ 2 * (d : ℝ)) ^ 2)

/-- All microscopic scalar costs retain the quarter-power scale margin
and have only polynomial dependence on the two coefficient envelopes. -/
theorem harmonicCellMicroscopicPrice_le (d : ℕ) {C J eps T R G : ℝ}
    (hC : 0 ≤ C) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hT : 1 ≤ T) (hR : 1 ≤ R) (hG : 1 ≤ G) :
    harmonicCellMicroscopicPrice d C J eps T R G ≤
      (C * (4 * (3 : ℝ) ^ d + 4 * (3 : ℝ) ^ d * (d : ℝ) ^ 2 * (2 : ℝ) ^ d +
        2 * J ^ 2 * (d : ℝ) ^ 2)) * (eps ^ (1 / 4 : ℝ) * R ^ 5 * G * T ^ d) := by
  let rho := eps / T
  have hT0 := zero_lt_one.trans_le hT
  have hrho : 0 < rho := div_pos heps hT0
  have hmargin := harmonicCell_radius_margin d heps hT0
  have hvol : rho ^ (1 / 2 : ℝ) * ((rho ^ d)⁻¹ * (2 * rho) ^ d) =
      (2 : ℝ) ^ d * rho ^ (1 / 2 : ℝ) := by
    rw [mul_pow]
    field_simp [(pow_pos hrho d).ne']
  have hroot : rho ^ (1 / 2 : ℝ) ≤ eps ^ (1 / 4 : ℝ) :=
    harmonicCell_sqrt_radius_le_margin heps heps1 hT
  have hR2 : R ^ 2 ≤ R ^ 5 := pow_le_pow_right₀ hR (by norm_num)
  have hR5 : R ≤ R ^ 5 := by simpa only [pow_one] using pow_le_pow_right₀ hR (by norm_num : 1 ≤ 5)
  have hTd : 1 ≤ T ^ d := one_le_pow₀ hT
  have hTpower : T ^ ((d : ℝ) - 1 / 2) ≤ T ^ d := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  let S := eps ^ (1 / 4 : ℝ) * R ^ 5 * G * T ^ d
  have hterm1 : R ^ 2 * G * eps ^ (1 / 4 : ℝ) * T ^ ((d : ℝ) - 1 / 2) ≤ S := by
    dsimp only [S]
    calc
      _ ≤ R ^ 5 * G * eps ^ (1 / 4 : ℝ) * T ^ d := by gcongr
      _ = _ := by ring
  have hterm2 : R * rho ^ (1 / 2 : ℝ) ≤ S := by
    dsimp only [S]
    calc
      _ ≤ R ^ 5 * eps ^ (1 / 4 : ℝ) := by gcongr
      _ = eps ^ (1 / 4 : ℝ) * R ^ 5 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have hterm3 : R ^ 5 * rho ^ (1 / 2 : ℝ) ≤ S := by
    dsimp only [S]
    calc
      _ ≤ R ^ 5 * eps ^ (1 / 4 : ℝ) := by gcongr
      _ = eps ^ (1 / 4 : ℝ) * R ^ 5 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have heq : harmonicCellMicroscopicPrice d C J eps T R G =
      C * (4 * (3 : ℝ) ^ d * (R ^ 2 * G * eps ^ (1 / 4 : ℝ) * T ^ ((d : ℝ) - 1 / 2)) +
        (4 * (3 : ℝ) ^ d * (d : ℝ) ^ 2) * (R * rho ^ (1 / 2 : ℝ)) * (2 : ℝ) ^ d +
        (2 * J ^ 2 * (d : ℝ) ^ 2) * (R ^ 5 * rho ^ (1 / 2 : ℝ))) := by
    unfold harmonicCellMicroscopicPrice
    linear_combination (C * 4 * (3 : ℝ) ^ d * R ^ 2 * G) * hmargin +
      (C * 4 * (3 : ℝ) ^ d * (d : ℝ) ^ 2 * R) * hvol
  rw [heq]
  calc
    _ ≤ C * (4 * (3 : ℝ) ^ d * S +
        (4 * (3 : ℝ) ^ d * (d : ℝ) ^ 2) * S * (2 : ℝ) ^ d +
        (2 * J ^ 2 * (d : ℝ) ^ 2) * S) := by gcongr
    _ = _ := by dsimp only [S]; ring


/-- The literal native reflected data price, with arbitrary datum amplitude,
is controlled by the same polynomial envelope cost. -/
theorem harmonicCell_nativeMicroscopicPrice_le (d : ℕ) {C J eps T R G kappa B : ℝ}
    (hC : 0 ≤ C) (hJ : 0 ≤ J) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hT : 1 ≤ T) (hR : 1 ≤ R) (hG : 1 ≤ G)
    (hkappa : 0 < kappa) (hkappaR : kappa ≤ R) (hkinv : kappa⁻¹ ≤ R) (hB : 0 ≤ B) :
    kappa * (eps / T) ^ (1 / 2 : ℝ) * C *
        (Real.sqrt ((((eps / T) ^ d)⁻¹ * (3 : ℝ) ^ d) *
            (2 * (R * (G * B ^ 2 * eps ^ ((d : ℝ) - 1 / 4)) +
              ((d : ℝ) * B) ^ 2 * (2 * (eps / T)) ^ d))) +
          J * kappa⁻¹ * R * ((d : ℝ) * B)) ^ 2 ≤
      (C * (4 * (3 : ℝ) ^ d + 4 * (3 : ℝ) ^ d * (d : ℝ) ^ 2 * (2 : ℝ) ^ d +
        2 * J ^ 2 * (d : ℝ) ^ 2)) * (eps ^ (1 / 4 : ℝ) * R ^ 5 * G * T ^ d) * B ^ 2 := by
  let rho := eps / T
  let A := (rho ^ d)⁻¹ * (3 : ℝ) ^ d *
    (2 * (R * G * eps ^ ((d : ℝ) - 1 / 4) + (d : ℝ) ^ 2 * (2 * rho) ^ d))
  have hR0 := zero_lt_one.trans_le hR
  have hG0 := zero_lt_one.trans_le hG
  have hT0 := zero_lt_one.trans_le hT
  have hA : 0 ≤ A := by dsimp only [A, rho]; positivity
  have hsqrt : Real.sqrt ((((eps / T) ^ d)⁻¹ * (3 : ℝ) ^ d) *
      (2 * (R * (G * B ^ 2 * eps ^ ((d : ℝ) - 1 / 4)) +
        ((d : ℝ) * B) ^ 2 * (2 * (eps / T)) ^ d))) = B * Real.sqrt A := by
    have heq : (((eps / T) ^ d)⁻¹ * (3 : ℝ) ^ d) *
        (2 * (R * (G * B ^ 2 * eps ^ ((d : ℝ) - 1 / 4)) +
          ((d : ℝ) * B) ^ 2 * (2 * (eps / T)) ^ d)) = B ^ 2 * A := by
      dsimp only [A, rho]
      ring
    rw [heq, Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq_eq_abs, abs_of_nonneg hB]
  rw [hsqrt]
  have hsource : J * kappa⁻¹ * R * (d : ℝ) ≤ J * R ^ 2 * (d : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hkinv (by positivity : 0 ≤ J * R * (d : ℝ))
    nlinarith only [h]
  have hsq : (Real.sqrt A + J * kappa⁻¹ * R * (d : ℝ)) ^ 2 ≤
      2 * (A + (J * R ^ 2 * (d : ℝ)) ^ 2) := by
    refine (harmonicCell_sqrt_price_sq_le hA).trans ?_
    gcongr
  calc
    _ = B ^ 2 * (kappa * rho ^ (1 / 2 : ℝ) * C *
        (Real.sqrt A + J * kappa⁻¹ * R * (d : ℝ)) ^ 2) := by ring
    _ ≤ B ^ 2 * (R * rho ^ (1 / 2 : ℝ) * C *
        (2 * (A + (J * R ^ 2 * (d : ℝ)) ^ 2))) := by gcongr
    _ = harmonicCellMicroscopicPrice d C J eps T R G * B ^ 2 := by
      dsimp only [harmonicCellMicroscopicPrice, A, rho]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (harmonicCellMicroscopicPrice_le d hC heps heps1 hT hR hG) (sq_nonneg B)

end SubdiffusiveProcess.Static
