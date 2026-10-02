import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Pure real arithmetic of the scaling in the Meyers glue: powers of the side `l` cancel. -/

noncomputable section

namespace SubdiffusiveProcess.Meyers

theorem pow_rpow_eq' {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (z : ℝ) : (x ^ n) ^ z = x ^ ((n : ℝ) * z) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

/-- The four power identities: with `s = d/p`, `t = d/2`, `β = d(1/p - 1/2) - 1`. -/
theorem rpow_facts {p : ℝ} (d : ℕ) {l : ℝ} (hl : 0 < l) :
    ((2 * l) ^ d) ^ (1 / p) = 2 ^ ((d : ℝ) / p) * l ^ ((d : ℝ) / p) ∧
    ((2 * (2 * l)) ^ d) ^ (1 / p) =
      2 ^ ((d : ℝ) / p) * (2 ^ ((d : ℝ) / p) * l ^ ((d : ℝ) / p)) ∧
    ((2 * (2 * l)) ^ d) ^ (1 / (2 : ℝ)) =
      2 ^ ((d : ℝ) / 2) * (2 ^ ((d : ℝ) / 2) * l ^ ((d : ℝ) / 2)) ∧
    (l / 3) ^ ((d : ℝ) * (1 / p - 1 / 2) - 1) * l * (l ^ ((d : ℝ) / 2) * 3 ^ ((d : ℝ) * (1 / p - 1 / 2) - 1))
      = l ^ ((d : ℝ) / p) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pow_rpow_eq' (by positivity), Real.mul_rpow h2 hl.le]
    congr 2 <;> ring
  · rw [pow_rpow_eq' (by positivity), Real.mul_rpow h2 (by positivity), Real.mul_rpow h2 hl.le]
    have : (d : ℝ) * (1 / p) = (d : ℝ) / p := by ring
    rw [this]
  · rw [pow_rpow_eq' (by positivity), Real.mul_rpow h2 (by positivity), Real.mul_rpow h2 hl.le]
    have : (d : ℝ) * (1 / 2) = (d : ℝ) / 2 := by ring
    rw [this]
  · set β : ℝ := (d : ℝ) * (1 / p - 1 / 2) - 1 with hβ
    have h3 : (0 : ℝ) < 3 ^ β := Real.rpow_pos_of_pos (by norm_num) β
    rw [Real.div_rpow hl.le (by norm_num)]
    have e : l ^ β * l * l ^ ((d : ℝ) / 2) = l ^ ((d : ℝ) / p) := by
      rw [← Real.rpow_add_one hl.ne', ← Real.rpow_add hl]
      congr 1
      rw [hβ]; ring
    field_simp
    linarith [e]

/-- the algebra of the scaling step, in terms of the atoms
`a = 2^s`, `b = 2^t·2^t`, `e = 3^β`, `L = l^s`, `M = l^t`, `Bp = (l/3)^β`. -/
theorem alg_step {a b e L M l a0 A2 Kf κ d' N C0 P Bp : ℝ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (hL : 0 < L) (hM : 0 < M) (hl : 0 < l) (ha0 : 0 < a0) (hA2 : 0 ≤ A2) (hKf : 0 ≤ Kf)
    (hκ : 0 ≤ κ) (hd' : 0 ≤ d') (hN : 0 ≤ N) (hC0 : 0 ≤ C0)
    (hBM : Bp * l * (M * e) = L)
    (hP : P ≤ N * (C0 * (Bp * (κ * (2 * (2 * l)) * d' * A2) + (l / 3) * ((Kf / a0) * (a * (a * L)))))) :
    P / (a * L) ≤ N * C0 * (κ * 4 * d' * b / (e * a) + a / 3) * (A2 / (b * M)) +
      N * C0 * (κ * 4 * d' * b / (e * a) + a / 3) * l * a0⁻¹ * Kf := by
  have hBl : Bp = L / (M * e * l) := by
    field_simp
    linarith [hBM]
  have h1 : P / (a * L) ≤ (N * (C0 * (Bp * (κ * (2 * (2 * l)) * d' * A2) +
      (l / 3) * ((Kf / a0) * (a * (a * L)))))) / (a * L) :=
    div_le_div_of_nonneg_right hP (by positivity)
  have h2 : (N * (C0 * (Bp * (κ * (2 * (2 * l)) * d' * A2) +
      (l / 3) * ((Kf / a0) * (a * (a * L)))))) / (a * L) =
      N * C0 * (κ * 4 * d' * b / (e * a)) * (A2 / (b * M)) + N * C0 * (a / 3) * l * a0⁻¹ * Kf := by
    rw [hBl]
    field_simp
    ring
  have hT1 : 0 ≤ κ * 4 * d' * b / (e * a) := by positivity
  have hT2 : 0 ≤ a / 3 := by positivity
  have hx : 0 ≤ A2 / (b * M) := by positivity
  have hy : 0 ≤ l * a0⁻¹ * Kf := by positivity
  rw [h2] at h1
  refine h1.trans ?_
  have hNC : 0 ≤ N * C0 := mul_nonneg hN hC0
  have e1 : N * C0 * (κ * 4 * d' * b / (e * a)) * (A2 / (b * M)) ≤
      N * C0 * (κ * 4 * d' * b / (e * a) + a / 3) * (A2 / (b * M)) := by
    apply mul_le_mul_of_nonneg_right _ hx
    apply mul_le_mul_of_nonneg_left _ hNC
    linarith
  have e2 : N * C0 * (a / 3) * l * a0⁻¹ * Kf ≤
      N * C0 * (κ * 4 * d' * b / (e * a) + a / 3) * l * a0⁻¹ * Kf := by
    have : N * C0 * (a / 3) * (l * a0⁻¹ * Kf) ≤
        N * C0 * (κ * 4 * d' * b / (e * a) + a / 3) * (l * a0⁻¹ * Kf) := by
      apply mul_le_mul_of_nonneg_right _ hy
      apply mul_le_mul_of_nonneg_left _ hNC
      linarith
    calc N * C0 * (a / 3) * l * a0⁻¹ * Kf = N * C0 * (a / 3) * (l * a0⁻¹ * Kf) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  linarith

end SubdiffusiveProcess.Meyers
