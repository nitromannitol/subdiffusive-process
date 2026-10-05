module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.Assembly
public import SubdiffusiveProcess.Frozen.Section3.SpecialTwoDExactFormula

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Lemma `l.one.step.upper` (one-step upper bound).

Correspondence with the live paper statement: `C(d)` is fixed before the model `M`; `m, h ∈ ℕ`
(`0 < m`, `0 < h`), `h ≤ δ⁻¹`, and `m - h ≥ 16 ⌈|log_3 δ|⌉` (integer subtraction, so `h ≤ m` follows);
`ahom_m ≤ ahom_{m-h} (1 - 2τ²h/d + C δ⁴ h² + C δ² |log δ|)`.

For `d ≥ 3` the statement is the frozen-vocabulary provider
`SubdiffusiveProcess.Providers.Section5.sharpOneStepUpperConclusion_of_concrete` (lower endpoint `n = m - h`); for `d = 2` it is
proved here from the planar exact formula `ahom_m = exp (-(m+1) τ²)` and `τ² ≤ (log 2 / 2) δ²`, using
`exp (-x) ≤ 1 - x + x²` for `x ≥ 0`. -/
theorem l_one_step_upper {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m h : ℕ), 0 < m → 0 < h →
        (h : ℝ) ≤ M.delta⁻¹ →
        ((16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ : ℕ) : ℤ) ≤ (m : ℤ) - (h : ℤ) →
        ahom M m ≤ ahom M (m - h) *
          (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / d +
            C * M.delta ^ 4 * (h : ℝ) ^ 2 +
            C * M.delta ^ 2 * |Real.log M.delta|) := by
  by_cases hd3 : 3 ≤ d
  · let : NeZero d := ⟨by omega⟩
    obtain ⟨C, hC, hbound⟩ := SubdiffusiveProcess.Providers.Section5.sharpOneStepUpperConclusion_of_concrete hd3
    refine ⟨C, hC, ?_⟩
    intro M m h _hm _hh hhδ hsub
    have hle : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ m - h := by omega
    have hhm : h ≤ m := by omega
    have := hbound M (m - h) h hhδ hle
    rwa [Nat.sub_add_cancel hhm] at this
  · by_cases hd2 : d = 2
    · subst hd2
      refine ⟨1, one_pos, ?_⟩
      intro M m h _hm hh hhδ hsub
      have hhm : h ≤ m := by omega
      have hδpos := M.shellPrefix.delta_pos
      have hτ0 : 0 ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P := M.G4.tauSq_pos.le
      have hτ := tauSq_le_delta_sq M
      have hmh : (m : ℝ) = ((m - h : ℕ) : ℝ) + h := by
        rw [Nat.cast_sub hhm]; ring
      rw [SubdiffusiveProcess.Frozen.Section3.special_two_d_exact_formula M m,
        SubdiffusiveProcess.Frozen.Section3.special_two_d_exact_formula M (m - h)]
      set T := _root_.SubdiffusiveProcess.Model.tauSq M.P with hT
      have hx0 : 0 ≤ T * h := mul_nonneg hτ0 (Nat.cast_nonneg h)
      -- exp(-x) ≤ 1 - x + x² for x ≥ 0
      have hexp : Real.exp (-(T * h)) ≤ 1 - T * h + (T * h) ^ 2 := by
        have h1 : 1 + T * h ≤ Real.exp (T * h) := by linarith [Real.add_one_le_exp (T * h)]
        have h2 : Real.exp (-(T * h)) * (1 + T * h) ≤ 1 := by
          rw [Real.exp_neg]
          calc (Real.exp (T * h))⁻¹ * (1 + T * h) ≤ (Real.exp (T * h))⁻¹ * Real.exp (T * h) :=
                mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (Real.exp_pos _).le)
            _ = 1 := inv_mul_cancel₀ (Real.exp_pos _).ne'
        nlinarith [Real.exp_pos (-(T * h)), sq_nonneg (T * h), mul_nonneg hx0 hx0,
          mul_nonneg hx0 (sq_nonneg (T * h))]
      have hsq : (T * h) ^ 2 ≤ M.delta ^ 4 * (h : ℝ) ^ 2 := by
        have hlog2 : Real.log 2 / 2 ≤ 1 := by
          have := Real.log_two_lt_d9; linarith
        have hTle : T ≤ M.delta ^ 2 := hτ.trans (by nlinarith [sq_nonneg M.delta])
        have : T * h ≤ M.delta ^ 2 * h := mul_le_mul_of_nonneg_right hTle (Nat.cast_nonneg h)
        calc (T * h) ^ 2 ≤ (M.delta ^ 2 * h) ^ 2 := pow_le_pow_left₀ hx0 this 2
          _ = M.delta ^ 4 * (h : ℝ) ^ 2 := by ring
      have hlogd : 0 ≤ |Real.log M.delta| := abs_nonneg _
      have hextra : 0 ≤ M.delta ^ 2 * |Real.log M.delta| := by positivity
      have hexpeq : Real.exp (-(((m - h : ℕ) : ℝ) + 1) * T) * Real.exp (-(T * h)) =
          Real.exp (-((m : ℝ) + 1) * T) := by
        rw [← Real.exp_add]; congr 1; rw [hmh]; ring
      rw [← hexpeq]
      have hpos : 0 < Real.exp (-(((m - h : ℕ) : ℝ) + 1) * T) := Real.exp_pos _
      have : Real.exp (-(T * h)) ≤
          1 - 2 * T * h / ((2 : ℕ) : ℝ) + 1 * M.delta ^ 4 * (h : ℝ) ^ 2 +
            1 * M.delta ^ 2 * |Real.log M.delta| := by
        push_cast
        nlinarith [hexp, hsq, hextra]
      calc Real.exp (-(((m - h : ℕ) : ℝ) + 1) * T) * Real.exp (-(T * h))
          ≤ Real.exp (-(((m - h : ℕ) : ℝ) + 1) * T) *
            (1 - 2 * T * h / ((2 : ℕ) : ℝ) + 1 * M.delta ^ 4 * (h : ℝ) ^ 2 +
              1 * M.delta ^ 2 * |Real.log M.delta|) :=
            mul_le_mul_of_nonneg_left this hpos.le
        _ = _ := by push_cast; ring_nf
    · refine ⟨1, one_pos, fun M => ?_⟩
      exact absurd M.shellPrefix.dimension (by omega)

end SubdiffusiveProcess.Paper
