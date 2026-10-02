import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper



theorem lem_layer_norms_absorption :
    ∀ C0 Cp Cpk : ℝ, 0 < C0 → 0 < Cp → 0 < Cpk →
    ∀ k lam : ℝ, 0 ≤ k → 0 ≤ lam →
    ∀ gam : ℝ, 0 < gam → ∃ Cpkg : ℝ, 0 < Cpkg ∧
    ∀ disorder : ℝ, 0 < disorder → disorder ≤ 1 →
    ∀ j : ℕ,
      let r := (3 : ℝ) ^ (-(j : ℝ))
      Cpk * disorder ^ k * (1 + abs (Real.log r)) ^ (k / 2) *
        Real.exp (C0 * lam * disorder * Real.sqrt (1 + abs (Real.log r)) +
          Cp * lam ^ 2 * disorder ^ 2) ≤
      Cpkg * disorder ^ k * r ^ (-gam) := by
  intro C0 Cp Cpk hC0 hCp hCpk k lam hk hlam gam hgam
  let c : ℝ := Cp * lam ^ 2 + C0 * lam + (C0 * lam + k) ^ 2 / (2 * gam)
  refine ⟨Cpk * Real.exp c, mul_pos hCpk (Real.exp_pos _), ?_⟩
  intro disorder hd hd1 j
  dsimp
  let x : ℝ := (j : ℝ) * Real.log 3
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hrlog : Real.log ((3 : ℝ) ^ (-(j : ℝ))) = -x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    rw [Real.log_exp]
    dsimp [x]
    ring
  have habs : abs (Real.log ((3 : ℝ) ^ (-(j : ℝ)))) = x := by
    rw [hrlog, abs_neg, abs_of_nonneg hx]
  have hrpos : 0 < (3 : ℝ) ^ (-(j : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrpow : ((3 : ℝ) ^ (-(j : ℝ))) ^ (-gam) = Real.exp (gam * x) := by
    rw [Real.rpow_def_of_pos hrpos, hrlog]
    congr 1
    ring
  rw [habs, hrpow]
  have hsqrt1 : 0 ≤ Real.sqrt (1 + x) := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt (1 + x) ≤ 1 + Real.sqrt x := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]
  have hlog1 : Real.log (1 + x) ≤ 2 * Real.sqrt x := by
    have hlog := Real.log_le_sub_one_of_pos
      (Real.sqrt_pos.2 (by linarith : 0 < 1 + x))
    have hlogsqrt := Real.log_sqrt (by linarith : 0 ≤ 1 + x)
    nlinarith [hsqrt]
  have hpowexp : Real.log (1 + x) * (k / 2) ≤ k * Real.sqrt x := by
    calc
      Real.log (1 + x) * (k / 2) ≤ (2 * Real.sqrt x) * (k / 2) :=
        mul_le_mul_of_nonneg_right hlog1 (by positivity)
      _ = k * Real.sqrt x := by ring
  have hpow : (1 + x) ^ (k / 2) ≤ Real.exp (k * Real.sqrt x) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < 1 + x)]
    exact Real.exp_le_exp.mpr hpowexp
  have hA : 0 ≤ C0 * lam := mul_nonneg hC0.le hlam
  have hB : 0 ≤ Cp * lam ^ 2 := mul_nonneg hCp.le (sq_nonneg _)
  have hd2 : disorder ^ 2 ≤ (1 : ℝ) := by
    nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]
  have hAsqrt :
      C0 * lam * disorder * Real.sqrt (1 + x) ≤
        C0 * lam * (1 + Real.sqrt x) := by
    have had : C0 * lam * disorder ≤ C0 * lam := by
      calc
        C0 * lam * disorder ≤ C0 * lam * 1 :=
          mul_le_mul_of_nonneg_left hd1 hA
        _ = C0 * lam := by ring
    calc
      C0 * lam * disorder * Real.sqrt (1 + x) =
          (C0 * lam * disorder) * Real.sqrt (1 + x) := by ring
      _ ≤ (C0 * lam) * Real.sqrt (1 + x) := by
        exact mul_le_mul_of_nonneg_right had hsqrt1
      _ ≤ (C0 * lam) * (1 + Real.sqrt x) := by
        exact mul_le_mul_of_nonneg_left hsqrt hA
  have hBdis : Cp * lam ^ 2 * disorder ^ 2 ≤ Cp * lam ^ 2 := by
    calc
      Cp * lam ^ 2 * disorder ^ 2 ≤ Cp * lam ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hd2 hB
      _ = Cp * lam ^ 2 := by ring
  have hbase :
      C0 * lam * disorder * Real.sqrt (1 + x) + Cp * lam ^ 2 * disorder ^ 2 ≤
        Cp * lam ^ 2 + C0 * lam + (C0 * lam) * Real.sqrt x := by
    calc
      C0 * lam * disorder * Real.sqrt (1 + x) + Cp * lam ^ 2 * disorder ^ 2 ≤
          C0 * lam * (1 + Real.sqrt x) + Cp * lam ^ 2 :=
        add_le_add hAsqrt hBdis
      _ = Cp * lam ^ 2 + C0 * lam + (C0 * lam) * Real.sqrt x := by ring
  have hform :
      gam / 2 * x + (C0 * lam + k) ^ 2 / (2 * gam) =
        (gam ^ 2 * x + (C0 * lam + k) ^ 2) / (2 * gam) := by
    field_simp [ne_of_gt hgam]
  have hsabsorb :
      (C0 * lam + k) * Real.sqrt x ≤
        gam / 2 * x + (C0 * lam + k) ^ 2 / (2 * gam) := by
    have hquad :
        (C0 * lam + k) * Real.sqrt x * (2 * gam) ≤
          gam ^ 2 * x + (C0 * lam + k) ^ 2 := by
      nlinarith [sq_nonneg (gam * Real.sqrt x - (C0 * lam + k)),
        Real.sq_sqrt hx]
    rw [hform]
    apply (le_div_iff₀ (by positivity : 0 < 2 * gam)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hquad
  have hT :
      k * Real.sqrt x +
          (C0 * lam * disorder * Real.sqrt (1 + x) + Cp * lam ^ 2 * disorder ^ 2) ≤
        c + gam * x := by
    dsimp [c]
    calc
      k * Real.sqrt x +
          (C0 * lam * disorder * Real.sqrt (1 + x) + Cp * lam ^ 2 * disorder ^ 2) ≤
          k * Real.sqrt x +
            (Cp * lam ^ 2 + C0 * lam + (C0 * lam) * Real.sqrt x) :=
        by
          convert add_le_add_left hbase (k * Real.sqrt x) using 1 <;> ring
      _ = Cp * lam ^ 2 + C0 * lam + (C0 * lam + k) * Real.sqrt x := by ring
      _ ≤ Cp * lam ^ 2 + C0 * lam + gam / 2 * x +
          (C0 * lam + k) ^ 2 / (2 * gam) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_left hsabsorb (Cp * lam ^ 2 + C0 * lam))
      _ ≤ Cp * lam ^ 2 + C0 * lam +
          (C0 * lam + k) ^ 2 / (2 * gam) + gam * x := by
        have hgamhalf : gam / 2 ≤ gam := by linarith
        have hxhalf : gam / 2 * x ≤ gam * x :=
          mul_le_mul_of_nonneg_right hgamhalf hx
        calc
          Cp * lam ^ 2 + C0 * lam + gam / 2 * x +
              (C0 * lam + k) ^ 2 / (2 * gam) =
              (Cp * lam ^ 2 + C0 * lam +
                (C0 * lam + k) ^ 2 / (2 * gam)) + gam / 2 * x := by ring
          _ ≤ (Cp * lam ^ 2 + C0 * lam +
                (C0 * lam + k) ^ 2 / (2 * gam)) + gam * x :=
            by
              convert add_le_add_left hxhalf
                (Cp * lam ^ 2 + C0 * lam +
                  (C0 * lam + k) ^ 2 / (2 * gam)) using 1 <;> ring
          _ = Cp * lam ^ 2 + C0 * lam +
              (C0 * lam + k) ^ 2 / (2 * gam) + gam * x := by ring
  have hprod :
      (1 + x) ^ (k / 2) *
          Real.exp (C0 * lam * disorder * Real.sqrt (1 + x) +
            Cp * lam ^ 2 * disorder ^ 2) ≤
        Real.exp c * Real.exp (gam * x) := by
    calc
      (1 + x) ^ (k / 2) *
          Real.exp (C0 * lam * disorder * Real.sqrt (1 + x) +
            Cp * lam ^ 2 * disorder ^ 2) ≤
          Real.exp (k * Real.sqrt x) *
            Real.exp (C0 * lam * disorder * Real.sqrt (1 + x) +
              Cp * lam ^ 2 * disorder ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
      _ = Real.exp (k * Real.sqrt x +
          (C0 * lam * disorder * Real.sqrt (1 + x) +
            Cp * lam ^ 2 * disorder ^ 2)) := by
        rw [← Real.exp_add]
      _ ≤ Real.exp (c + gam * x) := by
        exact Real.exp_le_exp.mpr hT
      _ = Real.exp c * Real.exp (gam * x) := by
        rw [Real.exp_add]
  calc
    Cpk * disorder ^ k * (1 + x) ^ (k / 2) *
          Real.exp (C0 * lam * disorder * Real.sqrt (1 + x) +
            Cp * lam ^ 2 * disorder ^ 2) =
        disorder ^ k *
          (Cpk * ((1 + x) ^ (k / 2) *
            Real.exp (C0 * lam * disorder * Real.sqrt (1 + x) +
              Cp * lam ^ 2 * disorder ^ 2))) := by ring
    _ ≤ disorder ^ k * (Cpk * (Real.exp c * Real.exp (gam * x))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hprod hCpk.le)
        (Real.rpow_nonneg hd.le k)
    _ = Cpk * Real.exp c * disorder ^ k * Real.exp (gam * x) := by ring

end Paper
