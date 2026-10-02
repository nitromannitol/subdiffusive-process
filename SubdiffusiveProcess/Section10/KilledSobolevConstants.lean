import SubdiffusiveProcess.Section10.KilledSobolev

/-! Constant bounds for later physical and bilateral banks. No model certificate
or random constant is assumed to exist here. -/

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- The strict exponent needed in torsion iteration and Nash interpolation. -/
lemma killedSobolevExponent_gt_two {d : ℕ} (hd : 2 ≤ d) :
    2 < killedSobolevExponent d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold killedSobolevExponent
  rw [lt_div_iff₀ (by linarith : 0 < (d : ℝ) - 1)]
  linarith

/-- Nash's dimension is 2*d: 1-2/p = 1/d. -/
lemma killedSobolev_one_sub_two_div {d : ℕ} (hd : 2 ≤ d) :
    1 - 2 / killedSobolevExponent d = 1 / (d : ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  unfold killedSobolevExponent
  field_simp
  ring

lemma killedSobolevConstant_nonneg (d : ℕ) (r0 C Km mass : ℝ) {Kc : ℝ}
    (hKc : 0 ≤ Kc) : 0 ≤ killedSobolevConstant d r0 C Km mass Kc :=
  mul_nonneg (sq_nonneg _) hKc

/-- The source mass and coercivity constants multiply with power 1+2/p.
The deterministic scale contains the padded-domain rational denominator. -/
theorem killedSobolevConstant_le_power {d : ℕ} (hd : 2 ≤ d)
    {r0 C Km mass scale : ℝ} (hr0 : 0 < r0) (hC : 0 ≤ C)
    (hKm : 0 < Km) (hmass0 : 0 ≤ mass) (hmass : mass ≤ Km) (hscale : 0 ≤ scale) :
    killedSobolevConstant d r0 C Km mass (Km * scale) ≤
      (C * (1 + r0 ^ (-((d : ℝ) / 2)))) ^ 2 * scale *
        Km ^ (1 + 2 / killedSobolevExponent d) := by
  have hp0 : 0 < killedSobolevExponent d :=
    lt_of_lt_of_le (by norm_num) (killedSobolevExponent_ge_two hd)
  have hm : mass ^ (1 / killedSobolevExponent d) ≤ Km ^ (1 / killedSobolevExponent d) :=
    Real.rpow_le_rpow hmass0 hmass (by positivity)
  have ha : 0 ≤ C * (Km ^ (1 / killedSobolevExponent d) +
      mass ^ (1 / killedSobolevExponent d) * r0 ^ (-((d : ℝ) / 2))) := by positivity
  have hL : C * (Km ^ (1 / killedSobolevExponent d) +
      mass ^ (1 / killedSobolevExponent d) * r0 ^ (-((d : ℝ) / 2))) ≤
      C * (Km ^ (1 / killedSobolevExponent d) +
        Km ^ (1 / killedSobolevExponent d) * r0 ^ (-((d : ℝ) / 2))) := by
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hr0.le _))) hC
  have hsquare : (Km ^ (1 / killedSobolevExponent d)) ^ 2 =
      Km ^ (2 / killedSobolevExponent d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hKm.le]
    congr 1
    ring
  have hexp : Km ^ (1 + 2 / killedSobolevExponent d) =
      Km * (Km ^ (1 / killedSobolevExponent d)) ^ 2 := by
    rw [Real.rpow_add hKm, Real.rpow_one, hsquare]
  calc
    _ ≤ (C * (Km ^ (1 / killedSobolevExponent d) +
        Km ^ (1 / killedSobolevExponent d) * r0 ^ (-((d : ℝ) / 2)))) ^ 2 * (Km * scale) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hL 2) (mul_nonneg hKm.le hscale)
    _ = _ := by
      rw [hexp]
      ring

/-- Asking for 2*q moments in the static supplier is sufficient for q moments
of the resulting Sobolev constant, with the threshold chosen at that larger
order first. This is independent of which of the two model banks is attached. -/
theorem killedSobolevConstant_le_sq {d : ℕ} (hd : 2 ≤ d)
    {r0 C Km mass scale : ℝ} (hr0 : 0 < r0) (hC : 0 ≤ C)
    (hKm : 1 ≤ Km) (hmass0 : 0 ≤ mass) (hmass : mass ≤ Km) (hscale : 0 ≤ scale) :
    killedSobolevConstant d r0 C Km mass (Km * scale) ≤
      ((C * (1 + r0 ^ (-((d : ℝ) / 2)))) ^ 2 * scale) * Km ^ 2 := by
  have hp := killedSobolevExponent_ge_two hd
  have hp0 : 0 < killedSobolevExponent d := lt_of_lt_of_le (by norm_num) hp
  have hdiv : 2 / killedSobolevExponent d ≤ 1 := by
    rw [div_le_iff₀ hp0, one_mul]
    exact hp
  have he : 1 + 2 / killedSobolevExponent d ≤ 2 := by linarith
  have hpower : Km ^ (1 + 2 / killedSobolevExponent d) ≤ Km ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hKm he
  exact (killedSobolevConstant_le_power hd hr0 hC (lt_of_lt_of_le zero_lt_one hKm)
    hmass0 hmass hscale).trans (by
      rw [Real.rpow_two] at hpower
      exact mul_le_mul_of_nonneg_left hpower (mul_nonneg (sq_nonneg _) hscale))


end SubdiffusiveProcess.Section10
