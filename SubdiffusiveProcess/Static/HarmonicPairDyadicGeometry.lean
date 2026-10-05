module

public import SubdiffusiveProcess.Static.HarmonicCutoffMajorant

@[expose] public section

/-! # Literal nested dyadic sides used by the cutoff clause -/
noncomputable section
namespace SubdiffusiveProcess.Static

/-- The exact consecutive dyadic pair has positive inner side, lies in the
outer window, and has the prescribed dyadic gap. -/
theorem pair_dyadic_sides {s0 s1 : ℝ} (h0 : 0 < s0) (h01 : s0 < s1)
    (n k : ℕ) (hk : k < 2 ^ n) :
    let R1 := ((1 - (k : ℝ) / 2 ^ n) * s0 + ((k : ℝ) / 2 ^ n) * s1) / 2
    let R2 := ((1 - ((k + 1 : ℕ) : ℝ) / 2 ^ n) * s0 +
      (((k + 1 : ℕ) : ℝ) / 2 ^ n) * s1) / 2
    0 < R1 ∧ R1 < R2 ∧ R2 ≤ s1 / 2 ∧
      R2 - R1 = (s1 - s0) / 2 ^ n / 2 := by
  have hn : 0 < (2 : ℝ) ^ n := by positivity
  have hk0 : 0 ≤ (k : ℝ) / 2 ^ n := by positivity
  have hk1 : ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ 1 := by
    rw [div_le_one hn]
    exact_mod_cast Nat.succ_le_of_lt hk
  have hdiff :
      (((1 - ((k + 1 : ℕ) : ℝ) / 2 ^ n) * s0 +
        (((k + 1 : ℕ) : ℝ) / 2 ^ n) * s1) / 2) -
        (((1 - (k : ℝ) / 2 ^ n) * s0 + ((k : ℝ) / 2 ^ n) * s1) / 2) =
          (s1 - s0) / 2 ^ n / 2 := by
    push_cast
    ring
  have hR1 : 0 < ((1 - (k : ℝ) / 2 ^ n) * s0 + ((k : ℝ) / 2 ^ n) * s1) / 2 := by
    have hprod := mul_nonneg hk0 (sub_pos.mpr h01).le
    nlinarith only [hprod, h0]
  have hs : 0 < s1 - s0 := sub_pos.mpr h01
  have hgap : 0 < (s1 - s0) / 2 ^ n / 2 := by positivity
  have hR2 : ((1 - ((k + 1 : ℕ) : ℝ) / 2 ^ n) * s0 +
      (((k + 1 : ℕ) : ℝ) / 2 ^ n) * s1) / 2 ≤ s1 / 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hk1) (sub_pos.mpr h01).le
    nlinarith only [hp]
  exact ⟨hR1, by linarith, hR2, hdiff⟩

end SubdiffusiveProcess.Static
