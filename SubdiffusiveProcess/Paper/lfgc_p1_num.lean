module

public import SubdiffusiveProcess.Paper.lem_witness_prefix_dyadic_cover

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Numerical budgets of the prefix witness

With `A = v + R c₁ + 1`, a moment order `p` for which `(q/r)^p ≤ e^{-(2 + v + R c₁)}`, an error
scale `Merr` with `24 (Cg + 1) (2 Merr/(q K'))^p ≤ e^{-R(c₁ + L₀ + b + 3)}`, a small base
probability `M'` and a large-range threshold `K`, both budgets of the prefix witness hold for the
windows `c₁ (H + 1) + L₀ + b + 3` and the bounds `e^{-R h}/2`.
-/

namespace SubdiffusiveProcess.Paper
theorem aux_lfgc_p1_num_aux_prefix_error_le {p M q r K : ℝ} (_hp : 0 < p) (hM : 0 ≤ M) (hq : 0 < q) (hr : 0 < r)
    (hK : 0 < K) (H : ℕ) :
    _root_.SubdiffusiveProcess.Paper.aux_prefix_error p M q r K H = 2 * (2 * M / (q * K)) ^ p * ((q / r) ^ p) ^ H := by
  unfold _root_.SubdiffusiveProcess.Paper.aux_prefix_error
  have h1 : 2 * (M / q * q ^ H) / (K * r ^ H) = (2 * M / (q * K)) * (q / r) ^ H := by
    rw [div_pow]
    field_simp
  rw [h1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), mul_comm (H : ℝ) p, Real.rpow_mul (by positivity),
    Real.rpow_natCast]
  ring

theorem aux_lfgc_p1_num_nat_add_one_le_exp (H : ℕ) : ((H : ℝ) + 1) ≤ Real.exp H := by
  have := Real.add_one_le_exp (H : ℝ)
  linarith

/-- The two budgets of the prefix witness. -/
theorem lfgc_p1_num {R v Cg A M' Merr q r K' p : ℝ} {c1 L0 b K : ℕ}
    (_hR : 0 < R) (_hv : 0 ≤ v) (hCg : 0 ≤ Cg) (hA : A = v + R * c1 + 1)
    (hq : 0 < q) (hqr : q < r) (hK' : 0 < K') (hp : 1 ≤ p)
    (hρ : (q / r) ^ p ≤ Real.exp (-(2 + v + R * c1)))
    (hMerr : 0 ≤ Merr)
    (hX : 24 * (Cg + 1) * (2 * Merr / (q * K')) ^ p ≤ Real.exp (-(R * (c1 + L0 + b + 3))))
    (hM'0 : 0 ≤ M')
    (hM' : Cg * M' * Real.exp (A * ((K : ℝ) - 1)) ≤ Real.exp (-(R * (c1 + L0 + b + 3))) / 12)
    (hK : Real.log (24 * (Cg + 1)) + R * (c1 + L0 + b + 3) ≤ K) :
    (∀ H : ℕ, Cg * (M' * Real.exp (A * ((K : ℝ) - 1))) * Real.exp (-((A - v) * (H : ℝ))) +
        ((H : ℝ) + 1) * Cg * Real.exp (v * (H : ℝ)) * _root_.SubdiffusiveProcess.Paper.aux_prefix_error p Merr q r K' H ≤
      (1 / 3) * (Real.exp (-R * ((c1 * (H + 1) + L0 + b + 3 : ℕ) : ℝ)) / 2)) ∧
    (∀ H : ℕ, K ≤ H → Cg * 2 * Real.exp (-((A - v) * (H : ℝ))) +
        ((H : ℝ) + 1) * Cg * Real.exp (v * (H : ℝ)) * _root_.SubdiffusiveProcess.Paper.aux_prefix_error p Merr q r K' H ≤
      (1 / 3) * (Real.exp (-R * ((c1 * (H + 1) + L0 + b + 3 : ℕ) : ℝ)) / 2)) := by
  have hr : 0 < r := hq.trans hqr
  have hp0 : 0 < p := by linarith
  set E0 := Real.exp (-(R * (c1 + L0 + b + 3)))
  have hE0 : 0 < E0 := Real.exp_pos _
  -- the target equals `E0 e^{-R c1 H} / 6`
  have htarget : ∀ H : ℕ, (1 / 3) * (Real.exp (-R * ((c1 * (H + 1) + L0 + b + 3 : ℕ) : ℝ)) / 2) =
      E0 * Real.exp (-(R * c1 * H)) / 6 := by
    intro H
    rw [← Real.exp_add]
    push_cast
    ring_nf
  -- the error term
  have hterm3 : ∀ H : ℕ, ((H : ℝ) + 1) * Cg * Real.exp (v * (H : ℝ)) *
      _root_.SubdiffusiveProcess.Paper.aux_prefix_error p Merr q r K' H ≤ E0 * Real.exp (-(R * c1 * H)) / 12 := by
    intro H
    rw [aux_lfgc_p1_num_aux_prefix_error_le hp0 hMerr hq hr hK']
    set X := (2 * Merr / (q * K')) ^ p
    have hX0 : 0 ≤ X := by positivity
    have hρ0 : 0 ≤ (q / r) ^ p := by positivity
    have hρH : ((q / r) ^ p) ^ H ≤ Real.exp (-(2 + v + R * c1) * H) := by
      calc ((q / r) ^ p) ^ H ≤ (Real.exp (-(2 + v + R * c1))) ^ H := pow_le_pow_left₀ hρ0 hρ H
        _ = Real.exp (-(2 + v + R * c1) * H) := by rw [← Real.exp_nat_mul]; ring_nf
    have hH1 := aux_lfgc_p1_num_nat_add_one_le_exp H
    have hXb : 24 * (Cg + 1) * X ≤ E0 := hX
    have hexp : ((H : ℝ) + 1) * Real.exp (v * (H : ℝ)) * Real.exp (-(2 + v + R * c1) * H) ≤
        Real.exp (-(R * c1 * H)) := by
      calc ((H : ℝ) + 1) * Real.exp (v * (H : ℝ)) * Real.exp (-(2 + v + R * c1) * H)
          ≤ Real.exp H * Real.exp (v * (H : ℝ)) * Real.exp (-(2 + v + R * c1) * H) := by gcongr
        _ = Real.exp (-(R * c1 * H)) * Real.exp (-H) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-(R * c1 * H)) * 1 := by
            gcongr; exact Real.exp_le_one_iff.mpr (by have : (0 : ℝ) ≤ H := Nat.cast_nonneg H; linarith)
        _ = _ := mul_one _
    have hEH : 0 ≤ Real.exp (-(R * c1 * H)) := (Real.exp_pos _).le
    calc ((H : ℝ) + 1) * Cg * Real.exp (v * (H : ℝ)) * (2 * X * ((q / r) ^ p) ^ H)
        ≤ ((H : ℝ) + 1) * Cg * Real.exp (v * (H : ℝ)) * (2 * X * Real.exp (-(2 + v + R * c1) * H)) := by
          gcongr
      _ = 2 * Cg * X * (((H : ℝ) + 1) * Real.exp (v * (H : ℝ)) * Real.exp (-(2 + v + R * c1) * H)) := by
          ring
      _ ≤ 2 * Cg * X * Real.exp (-(R * c1 * H)) := by gcongr
      _ ≤ E0 * Real.exp (-(R * c1 * H)) / 12 := by
          have : 2 * Cg * X ≤ E0 / 12 := by nlinarith
          nlinarith
  have hAv : A - v = R * c1 + 1 := by rw [hA]; ring
  refine ⟨fun H => ?_, fun H hKH => ?_⟩
  · rw [htarget H]
    have h1 : Cg * (M' * Real.exp (A * ((K : ℝ) - 1))) * Real.exp (-((A - v) * (H : ℝ))) ≤
        E0 * Real.exp (-(R * c1 * H)) / 12 := by
      rw [hAv]
      have hle : Real.exp (-((R * c1 + 1) * (H : ℝ))) ≤ Real.exp (-(R * c1 * H)) :=
        Real.exp_le_exp.mpr (by have : (0 : ℝ) ≤ H := Nat.cast_nonneg H; nlinarith)
      have hc : 0 ≤ Cg * (M' * Real.exp (A * ((K : ℝ) - 1))) := by positivity
      calc Cg * (M' * Real.exp (A * ((K : ℝ) - 1))) * Real.exp (-((R * c1 + 1) * (H : ℝ)))
          ≤ Cg * (M' * Real.exp (A * ((K : ℝ) - 1))) * Real.exp (-(R * c1 * H)) := by gcongr
        _ ≤ E0 / 12 * Real.exp (-(R * c1 * H)) := by
            gcongr
            linarith [hM']
        _ = E0 * Real.exp (-(R * c1 * H)) / 12 := by ring
    linarith [hterm3 H]
  · rw [htarget H]
    have h1 : Cg * 2 * Real.exp (-((A - v) * (H : ℝ))) ≤ E0 * Real.exp (-(R * c1 * H)) / 12 := by
      rw [hAv]
      have hKH' : (K : ℝ) ≤ H := by exact_mod_cast hKH
      have hlog : Real.log (24 * (Cg + 1)) + R * (c1 + L0 + b + 3) ≤ H := hK.trans hKH'
      have h24 : 24 * (Cg + 1) * Real.exp (R * (c1 + L0 + b + 3)) ≤ Real.exp H := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < 24 * (Cg + 1)), ← Real.exp_add]
        exact Real.exp_le_exp.mpr hlog
      have hsplit : Real.exp (-((R * c1 + 1) * (H : ℝ))) =
          Real.exp (-(R * c1 * H)) * Real.exp (-(H : ℝ)) := by
        rw [← Real.exp_add]; ring_nf
      rw [hsplit]
      have hEinv : E0 * Real.exp (R * (c1 + L0 + b + 3)) = 1 := by
        rw [← Real.exp_add]; simp
      have hexpH : Real.exp (-(H : ℝ)) * Real.exp H = 1 := by rw [← Real.exp_add]; simp
      have hEH : 0 < Real.exp (-(R * c1 * H)) := Real.exp_pos _
      have hkey : Cg * 2 * Real.exp (-(H : ℝ)) ≤ E0 / 12 := by
        have hem : 0 < Real.exp (-(H : ℝ)) := Real.exp_pos _
        have hb : 24 * (Cg + 1) * Real.exp (R * (c1 + L0 + b + 3)) * Real.exp (-(H : ℝ)) ≤ 1 := by
          calc 24 * (Cg + 1) * Real.exp (R * (c1 + L0 + b + 3)) * Real.exp (-(H : ℝ))
              ≤ Real.exp H * Real.exp (-(H : ℝ)) := by gcongr
            _ = 1 := by rw [mul_comm]; exact hexpH
        have hEpos : 0 < Real.exp (R * (c1 + L0 + b + 3)) := Real.exp_pos _
        nlinarith
      calc Cg * 2 * (Real.exp (-(R * c1 * H)) * Real.exp (-(H : ℝ)))
          = (Cg * 2 * Real.exp (-(H : ℝ))) * Real.exp (-(R * c1 * H)) := by ring
        _ ≤ E0 / 12 * Real.exp (-(R * c1 * H)) := by gcongr
        _ = E0 * Real.exp (-(R * c1 * H)) / 12 := by ring
    linarith [hterm3 H]

end SubdiffusiveProcess.Paper
