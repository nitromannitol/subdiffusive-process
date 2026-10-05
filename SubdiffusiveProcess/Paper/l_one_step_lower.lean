module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.Assembly
public import SubdiffusiveProcess.Section3.SpecialTwoDExactFormula

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Lemma `l.one.step.lower` (one-step lower bound).

Correspondence with the live paper statement: `C(d)` is fixed before the model `M`; `m, h ∈ ℕ`
(`0 < m`, `0 < h`), `h ≤ δ⁻¹`, and `m - h ≥ 16 ⌈|log_3 δ|⌉` (integer subtraction, so `h ≤ m` follows);
`ahom_m⁻¹ ≤ ahom_{m-h}⁻¹ (1 + 2τ²h/d + C δ⁴ h² + C δ² |log δ|)`.

For `d ≥ 3` the statement is the provider
`SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.sharpOneStepLowerConclusion_of_dualCellMajorants` (lower endpoint
`n = m - h`) with its inputs supplied by `Section5DualCompetitor.dualCellMajorantInputs_of_three_le`; for `d = 2` it
is proved here from the planar exact formula `ahom_m = exp (-(m+1) τ²)` and `τ² ≤ (log 2 / 2) δ²`, using
`exp x ≤ 1 + x + 2 x²` for `0 ≤ x ≤ 1/2`. -/
theorem l_one_step_lower {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m h : ℕ), 0 < m → 0 < h →
        (h : ℝ) ≤ M.delta⁻¹ →
        ((16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ : ℕ) : ℤ) ≤ (m : ℤ) - (h : ℤ) →
        (ahom M m)⁻¹ ≤ (ahom M (m - h))⁻¹ *
          (1 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / d +
            C * M.delta ^ 4 * (h : ℝ) ^ 2 +
            C * M.delta ^ 2 * |Real.log M.delta|) := by
  by_cases hd3 : 3 ≤ d
  · let : NeZero d := ⟨by omega⟩
    obtain ⟨C, hC, hbound⟩ :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.sharpOneStepLowerConclusion_of_dualCellMajorants
        hd3 (SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.dualCellMajorantInputs_of_three_le d hd3)
    refine ⟨C, hC, ?_⟩
    intro M m h _hm _hh hhδ hsub
    have hle : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ m - h := by omega
    have hhm : h ≤ m := by omega
    have := hbound M (m - h) h hhδ hle
    rwa [Nat.sub_add_cancel hhm] at this
  · by_cases hd2 : d = 2
    · subst hd2
      refine ⟨2, two_pos, ?_⟩
      intro M m h _hm hh hhδ hsub
      have hhm : h ≤ m := by omega
      have hδpos := M.shellPrefix.delta_pos
      have hδhalf := M.shellPrefix.delta_le_half
      have hτ0 : 0 ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P := M.G4.tauSq_pos.le
      have hτ := tauSq_le_delta_sq M
      have hmh : (m : ℝ) = ((m - h : ℕ) : ℝ) + h := by
        rw [Nat.cast_sub hhm]; ring
      rw [_root_.SubdiffusiveProcess.Section3.special_two_d_exact_formula M m,
        _root_.SubdiffusiveProcess.Section3.special_two_d_exact_formula M (m - h), ← Real.exp_neg, ← Real.exp_neg]
      simp only [neg_mul, neg_neg]
      set T := _root_.SubdiffusiveProcess.Model.tauSq M.P with hT
      have hx0 : 0 ≤ T * h := mul_nonneg hτ0 (Nat.cast_nonneg h)
      have hlog2 : Real.log 2 / 2 ≤ 1 / 2 := by
        have := Real.log_two_lt_d9; linarith
      have hhδ1 : (h : ℝ) * M.delta ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hhδ hδpos.le
        rwa [inv_mul_cancel₀ hδpos.ne'] at this
      have hTle : T ≤ (1 / 2) * M.delta ^ 2 := hτ.trans (mul_le_mul_of_nonneg_right hlog2 (sq_nonneg _))
      have hxhalf : T * h ≤ 1 / 2 := by
        calc T * h ≤ ((1 / 2) * M.delta ^ 2) * h := mul_le_mul_of_nonneg_right hTle (Nat.cast_nonneg h)
          _ = (1 / 2) * M.delta * ((h : ℝ) * M.delta) := by ring
          _ ≤ (1 / 2) * (1 / 2) * 1 := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hδhalf (by norm_num)
            · exact hhδ1
            · exact mul_nonneg (Nat.cast_nonneg h) hδpos.le
            · norm_num
          _ ≤ 1 / 2 := by norm_num
      -- exp x ≤ 1 + x + 2 x² for 0 ≤ x ≤ 1/2
      have hexp : Real.exp (T * h) ≤ 1 + T * h + 2 * (T * h) ^ 2 := by
        have h1 : 1 - T * h ≤ Real.exp (-(T * h)) := by linarith [Real.add_one_le_exp (-(T * h))]
        have h2 : Real.exp (T * h) * (1 - T * h) ≤ 1 := by
          calc Real.exp (T * h) * (1 - T * h) ≤ Real.exp (T * h) * Real.exp (-(T * h)) :=
                mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
            _ = 1 := by rw [← Real.exp_add]; simp
        have h3 : 1 ≤ (1 + T * h + 2 * (T * h) ^ 2) * (1 - T * h) := by
          nlinarith [mul_nonneg (sq_nonneg (T * h)) (by linarith : 0 ≤ 1 - 2 * (T * h))]
        have hpos : 0 < 1 - T * h := by linarith
        exact le_of_mul_le_mul_right (h2.trans h3) hpos
      have hsq : (T * h) ^ 2 ≤ M.delta ^ 4 * (h : ℝ) ^ 2 := by
        have hTle' : T ≤ M.delta ^ 2 := hTle.trans (by nlinarith [sq_nonneg M.delta])
        have : T * h ≤ M.delta ^ 2 * h := mul_le_mul_of_nonneg_right hTle' (Nat.cast_nonneg h)
        calc (T * h) ^ 2 ≤ (M.delta ^ 2 * h) ^ 2 := pow_le_pow_left₀ hx0 this 2
          _ = M.delta ^ 4 * (h : ℝ) ^ 2 := by ring
      have hextra : 0 ≤ M.delta ^ 2 * |Real.log M.delta| := by positivity
      have hexpeq : Real.exp ((((m - h : ℕ) : ℝ) + 1) * T) * Real.exp (T * h) =
          Real.exp (((m : ℝ) + 1) * T) := by
        rw [← Real.exp_add]; congr 1; rw [hmh]; ring
      rw [← hexpeq]
      have hpos : 0 < Real.exp ((((m - h : ℕ) : ℝ) + 1) * T) := Real.exp_pos _
      have : Real.exp (T * h) ≤
          1 + 2 * T * h / ((2 : ℕ) : ℝ) + 2 * M.delta ^ 4 * (h : ℝ) ^ 2 +
            2 * M.delta ^ 2 * |Real.log M.delta| := by
        push_cast
        nlinarith [hexp, hsq, hextra]
      calc Real.exp ((((m - h : ℕ) : ℝ) + 1) * T) * Real.exp (T * h)
          ≤ Real.exp ((((m - h : ℕ) : ℝ) + 1) * T) *
            (1 + 2 * T * h / ((2 : ℕ) : ℝ) + 2 * M.delta ^ 4 * (h : ℝ) ^ 2 +
              2 * M.delta ^ 2 * |Real.log M.delta|) :=
            mul_le_mul_of_nonneg_left this hpos.le
        _ = _ := by push_cast; ring_nf
    · refine ⟨1, one_pos, fun M => ?_⟩
      exact absurd M.shellPrefix.dimension (by omega)

end SubdiffusiveProcess.Paper
