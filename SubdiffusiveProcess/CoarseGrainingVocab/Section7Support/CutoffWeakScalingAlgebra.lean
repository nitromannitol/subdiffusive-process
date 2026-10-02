import Mathlib

/-!
# Arithmetic for the finite-cutoff weak-scaling bounds

Block summation and logarithmic interpolation estimates for the Section 7 clock.
-/

set_option autoImplicit false
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Support.CutoffWeakScaling
noncomputable section
theorem affine_bounds {u v t : ℝ} (huv : u ≤ v) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    u ≤ (1 - t) * u + t * v ∧ (1 - t) * u + t * v ≤ v := by
  constructor
  · have h1 : 0 ≤ t * (v - u) := by nlinarith
    nlinarith [h1, ht1]
  · have h2 : 0 ≤ (1 - t) * (v - u) := by nlinarith
    nlinarith [h2, ht0]

theorem block_count {delta H q k E : ℝ}
    (hd : 0 ≤ delta) (hq : 0 ≤ q) (hE : 0 ≤ E)
    (hH : 1 / 2 ≤ delta * H) (hk : q * H ≤ k) :
    (q + 1) * E ≤ (2 * delta * k + 1) * E := by
  have h1 : (1 / 2) * q ≤ delta * (q * H) := by
    nlinarith [hH, hq]
  have h2 : delta * (q * H) ≤ delta * k := by
    nlinarith [hk, hd]
  have h3 : q ≤ 2 * delta * k := by
    nlinarith [h1, h2]
  nlinarith [h3, hE]

theorem short_block_error {C delta h H z : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ delta) (hh : 0 ≤ h) (hhH : h ≤ H)
    (hH : delta * H ≤ 1) (hz : 1 / 2 ≤ z) :
    C * delta ^ 4 * h ^ 2 + C * delta ^ 2 * z ≤ 3 * C * delta ^ 2 * z := by
  have hdh : 0 ≤ delta * h := mul_nonneg hd hh
  have h1 : delta * h ≤ 1 := by nlinarith [hhH, hd, hH]
  have h2 : (delta * h) ^ 2 ≤ 1 := by nlinarith [hdh, h1]
  have hCD : 0 ≤ C * delta ^ 2 := mul_nonneg hC (by nlinarith [hd])
  have key : C * delta ^ 4 * h ^ 2 ≤ 2 * C * delta ^ 2 * z := by
    have e : C * delta ^ 4 * h ^ 2 = C * delta ^ 2 * (delta * h) ^ 2 := by ring
    rw [e]
    nlinarith [h2, hCD, hz]
  nlinarith [key]

theorem clamped_order {a b : ℕ} (hab : a ≤ b) (L : ℕ) :
    min a L ≤ min b L ∧ min (b + 1) L ≤ min b L + 1 := by
  omega

theorem max_gap {x y : ℝ} (hxy : x ≤ y) : max y 0 - max x 0 ≤ y - x := by
  simp only [max_def]
  split_ifs <;> linarith

theorem reciprocal_log {a b drift E : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : b⁻¹ ≤ a⁻¹ * (1 + drift + E)) :
    Real.log a - Real.log b ≤ drift + E := by
  have hpos : 0 < a * b := mul_pos ha hb
  have h1 : a / b ≤ 1 + drift + E := by
    have := mul_le_mul_of_nonneg_left h (le_of_lt ha)
    field_simp at this ⊢
    linarith
  have h2 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h2
  linarith

theorem interpolation_lower {f : ℕ → ℝ} {i j : ℕ} {a b D : ℝ}
    (hf : Monotone f) (hij : i ≤ j) (ha : a ≤ f (i + 1))
    (hb : f j ≤ b) (hstep : f (j + 1) - f j ≤ D) : -D ≤ b - a := by
  have hm := hf (show i + 1 ≤ j + 1 by omega)
  linarith

theorem uniform_prefactor {A B K t delta z : ℝ}
    (hK : 0 ≤ K) (ht : t ≤ 1 / 2)
    (hA : A = K * delta ^ 2 * z)
    (hB : B = t + K * delta ^ 3 * z)
    (h2 : delta ^ 2 * z ≤ 1) (h3 : delta ^ 3 * z ≤ 1) :
    A + 2 * B ≤ 3 * K + 1 := by
  subst hA
  subst hB
  have e1 : K * delta ^ 2 * z ≤ K := by
    calc K * delta ^ 2 * z = K * (delta ^ 2 * z) := by ring
    _ ≤ K * 1 := mul_le_mul_of_nonneg_left h2 hK
    _ = K := by ring
  have e2 : K * delta ^ 3 * z ≤ K := by
    calc K * delta ^ 3 * z = K * (delta ^ 3 * z) := by ring
    _ ≤ K * 1 := mul_le_mul_of_nonneg_left h3 hK
    _ = K := by ring
  nlinarith [e1, e2, ht]

theorem delta_loss {delta z : ℝ} (hd : 0 ≤ delta) (hd1 : delta ≤ 1)
    (_hz : 0 ≤ z) (h : delta ^ 2 * z ≤ delta) :
    delta ^ 2 * z ≤ 1 ∧ delta ^ 3 * z ≤ 1 := by
  constructor
  · exact h.trans hd1
  · have hm := mul_le_mul_of_nonneg_left h hd
    nlinarith [sq_nonneg (delta - 1)]

theorem block_telescope {F : ℕ → ℝ} {J H : ℕ} {E : ℝ}
    (hstep : ∀ n h : ℕ, J ≤ n → h ≤ H → F (n + h) - F n ≤ E)
    {n : ℕ} (hn : J ≤ n) (q : ℕ) :
    F (n + q * H) - F n ≤ (q : ℝ) * E := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : F (n + q * H + H) - F (n + q * H) ≤ E :=
      hstep (n + q * H) H (by omega) (le_refl H)
    have h2 : n + (q + 1) * H = n + q * H + H := by ring
    rw [h2]
    push_cast
    have h3 : F (n + q * H + H) - F n
        = (F (n + q * H + H) - F (n + q * H)) + (F (n + q * H) - F n) := by ring
    rw [h3]
    linarith [h1, ih]

theorem block_remainder {F : ℕ → ℝ} {J H : ℕ} {E : ℝ}
    (hfull : ∀ n q : ℕ, J ≤ n → F (n + q * H) - F n ≤ (q : ℝ) * E)
    (hstep : ∀ n h : ℕ, J ≤ n → h ≤ H → F (n + h) - F n ≤ E)
    {n k : ℕ} (hn : J ≤ n) (hH : 0 < H) :
    F (n + k) - F n ≤ ((k / H : ℕ) + 1 : ℝ) * E := by
  set q := k / H with hq
  set r := k % H with hr
  have hmod : r < H := Nat.mod_lt k hH
  have hk : q * H + r = k := by
    simpa only [q, r, Nat.mul_comm] using Nat.div_add_mod k H
  have h1 : F (n + q * H) - F n ≤ (q : ℝ) * E := hfull n q hn
  have h2 : F (n + q * H + r) - F (n + q * H) ≤ E :=
    hstep (n + q * H) r (hn.trans (Nat.le_add_right n (q * H))) (Nat.le_of_lt hmod)
  have hkey : n + k = n + q * H + r := by
    rw [← hk, Nat.add_assoc]
  rw [hkey]
  calc F (n + q * H + r) - F n
      = (F (n + q * H + r) - F (n + q * H)) + (F (n + q * H) - F n) := by ring
    _ ≤ E + (q : ℝ) * E := add_le_add h2 h1
    _ = ((k / H : ℕ) + 1 : ℝ) * E := by rw [hq]; ring

theorem log_quadratic {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    Real.log (r ^ 2 / a) - 2 * Real.log r = -Real.log a := by
  rw [Real.log_div (by positivity) ha.ne', Real.log_pow]
  ring

theorem log_ratio_upper {r R u v A beta : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hu : 0 < u) (hv : 0 < v)
    (h : Real.log u - Real.log v ≤ A + beta * (Real.log R - Real.log r)) :
    u / v ≤ Real.exp A * (R / r) ^ beta := by
  apply (Real.log_le_log_iff (div_pos hu hv) (by positivity)).mp
  rw [Real.log_div hu.ne' hv.ne', Real.log_mul (Real.exp_pos A).ne' (by positivity),
    Real.log_exp, Real.log_rpow (div_pos hR hr), Real.log_div hR.ne' hr.ne']
  exact h

theorem log_ratio_lower {r R u v D : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hu : 0 < u) (hv : 0 < v)
    (h : -D + 2 * (Real.log R - Real.log r) ≤ Real.log u - Real.log v) :
    Real.exp (-D) * (R / r) ^ 2 ≤ u / v := by
  have hpos : 0 < Real.exp (-D) * (R / r) ^ 2 :=
    mul_pos (Real.exp_pos _) (pow_pos (div_pos hR hr) 2)
  exact (Real.log_le_log_iff hpos (div_pos hu hv)).mp (by
    rw [Real.log_mul (Real.exp_pos (-D)).ne' (by positivity), Real.log_exp,
      Real.log_pow, Real.log_div hR.ne' hr.ne', Real.log_div hu.ne' hv.ne']
    norm_num
    linarith [h])

theorem index_cast_gap {i j L : ℕ} {x y : ℝ}
    (hi : x - 1 ≤ (i : ℝ)) (hj : (j : ℝ) ≤ y) (hxy : x ≤ y) :
    ((min j L + 1 : ℕ) : ℝ) - (min i L : ℕ) ≤ y - x + 2 := by
  push_cast
  simp only [min_def]
  split_ifs <;> linarith

theorem early_log_cost {t delta z J l m : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ delta ^ 2) (hgap : m-l ≤ J+1)
    (hJ : J+1 ≤ 132*z) (hz : 0 ≤ z) (_hraw : 0 ≤ m-l) :
    2*t*(m-l) ≤ 264*delta^2*z := by
  have h1 : 2*t*(m-l) ≤ 2*t*(J+1) := by nlinarith
  have h2 : 2*t*(J+1) ≤ 2*t*(132*z) := by nlinarith
  have h3 : 2*t*(132*z) ≤ 264*delta^2*z := by nlinarith [ht]
  exact h1.trans (h2.trans h3)

theorem floor_max_bounds (x : ℝ) :
    max x 0 - 1 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ max x 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    constructor
    · have h := Nat.lt_floor_add_one x
      linarith
    · exact Nat.floor_le hx
  · have hz : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    rw [hz, max_eq_right (by linarith : x ≤ 0)]
    norm_num

theorem log_scale_bound {x y i j A B q : ℝ} (_hq : 0 < q) (hB : 0 ≤ B)
    (hgap : j-i ≤ (y-x)/q+2) (_h : x ≤ y)
    {u v : ℝ} (huv : u-v ≤ A+B*(j-i)) :
    2*y+u-(2*x+v) ≤ A+2*B+(2+B/q)*(y-x) := by
  have hs := mul_le_mul_of_nonneg_left hgap hB
  have hident : B*((y-x)/q) = (B/q)*(y-x) := by ring
  rw [mul_add, hident] at hs
  linarith [huv]

theorem block_global_algebra {A C delta z k t : ℝ} (hC : 0 ≤ C)
    (hd : 0 ≤ delta) (hz : 0 ≤ z) (hk : 0 ≤ k)
    (h : A ≤ 264*delta^2*z+(2*delta*k+1)*(3*C*delta^2*z)+t*k) :
    A ≤ (264+6*C)*delta^2*z+(t+(264+6*C)*delta^3*z)*k := by
  have h1 : 0 ≤ 3*C*delta^2*z := by positivity
  have h2 : 0 ≤ 264*delta^3*z*k := by positivity
  nlinarith only [h, h1, h2]

theorem log_affine_slope_identity (u v x m z : ℝ) (hz : z ≠ 0) :
    (2*m*z-u)+(2*z+u-v)/z*(x-m*z)-2*x =
      (1-(x/z-m))*(-u)+(x/z-m)*(-v) := by
  field_simp [hz]
  ring

theorem drift_bound {d t : ℝ} (hd : 2 ≤ d) (ht0 : 0 ≤ t) (ht : t ≤ 1/4) :
    0 ≤ 2*t/d ∧ 2*t/d ≤ 1/2 := by
  have hdpos : 0 < d := by linarith
  constructor
  · positivity
  · rw [div_le_iff₀ hdpos]
    nlinarith


theorem lower_constant_uniform {t : ℝ} (ht : t ≤ 1/4) : Real.exp (-1) ≤ Real.exp (-(2*t)) := by
  apply Real.exp_le_exp.mpr
  linarith

theorem planar_prefactor_uniform {t K : ℝ} (ht : t ≤ 1/4) (hK : 0 ≤ K) :
    Real.exp (0+2*t) ≤ Real.exp (3*K+1) := by
  apply Real.exp_le_exp.mpr
  linarith

theorem beta_conversion (tau K delta d : ℝ) :
    2+(2*tau/d+K*delta^3*|Real.log delta|)/Real.log 3 =
      2+2*tau/(d*Real.log 3)+(K/Real.log 3)*delta^3*|Real.log delta| := by
  ring

theorem upper_drift_nonnegative {t K delta d : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hdelta : 0 ≤ delta) (hd : 0 ≤ d) : 0 ≤ 2*t/d+K*delta^3*|Real.log delta| := by
  have h1 : 0 ≤ 2*t/d := div_nonneg (by nlinarith) hd
  have h2 : 0 ≤ K*delta^3*|Real.log delta| :=
    mul_nonneg (mul_nonneg hK (pow_nonneg hdelta 3)) (abs_nonneg _)
  nlinarith [h1, h2]
end
end SubdiffusiveProcess.CoarseGrainingVocab.Section7Support.CutoffWeakScaling
