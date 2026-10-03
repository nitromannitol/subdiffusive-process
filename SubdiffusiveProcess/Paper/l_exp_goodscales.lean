module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.FieldTwoDensity

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper

theorem aux_l_exp_goodscales_translatedCube_zero (d : ℕ) (n : ℤ) :
    translatedCube d n (0 : Vec d) = cube d n := by
  rw [translatedCube]
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    simpa using hy
  · intro x hx
    exact ⟨x, hx, by simp⟩

/-- The discounted product test at discount `3^{-s j}` fails iff the frozen `GoodFieldTwo` fails at `8 s`. -/
theorem aux_l_exp_goodscales_iff {d : ℕ} (m : ℕ) (s : ℝ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    (∃ j : ℕ, 6 < (3 : ℝ) ^ (-(s * (j : ℝ))) *
        supNormOn (cube d ((m : ℤ) + 1 + (j : ℤ))) (fun x =>
          (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |ω i x|) +
            ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i x - ω i 0|) else 1)) ↔
      ω ∈ {ω' : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | GoodFieldTwo m 0 (8 * s) ω'}ᶜ := by
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, GoodFieldTwo, not_forall, not_le]
  refine exists_congr fun j => ?_
  rw [aux_l_exp_goodscales_translatedCube_zero]
  have hB : (0 : ℝ) < (3 : ℝ) ^ (-(s * (j : ℝ))) := by positivity
  have hA : (0 : ℝ) < (3 : ℝ) ^ ((8 * s * (j : ℝ)) / 8) := by positivity
  have hAB : (3 : ℝ) ^ ((8 * s * (j : ℝ)) / 8) * (3 : ℝ) ^ (-(s * (j : ℝ))) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have : (8 * s * (j : ℝ)) / 8 + -(s * (j : ℝ)) = 0 := by ring
    rw [this, Real.rpow_zero]
  generalize (3 : ℝ) ^ ((8 * s * (j : ℝ)) / 8) = A at hA hAB ⊢
  generalize (3 : ℝ) ^ (-(s * (j : ℝ))) = B at hB hAB ⊢
  generalize (supNormOn (cube d ((m : ℤ) + 1 + (j : ℤ))) (fun x =>
    (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |ω i x|) +
      ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i x - ω i 0|) else 1)) = S
  constructor
  · intro h
    have h1 := mul_lt_mul_of_pos_left h hA
    calc 6 * A = A * 6 := mul_comm _ _
      _ < A * (B * S) := h1
      _ = (A * B) * S := by ring
      _ = S := by rw [hAB, one_mul]
  · intro h
    have h1 := mul_lt_mul_of_pos_right h hB
    calc (6 : ℝ) = 6 * (A * B) := by rw [hAB, mul_one]
      _ = 6 * A * B := by ring
      _ < S * B := h1
      _ = B * S := mul_comm _ _

/-- `GoodFieldTwo` is monotone in the parameter `s` (larger `s` relaxes the discount). -/
theorem aux_l_exp_goodscales_mono {d : ℕ} (m : ℕ) (y : Vec d) {s₁ s₂ : ℝ} (h : s₁ ≤ s₂)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (h1 : GoodFieldTwo m y s₁ ω) :
    GoodFieldTwo m y s₂ ω := by
  intro j
  refine (h1 j).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith



theorem l_exp_goodscales
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ m0 K : ℕ, ∀ s theta : ℝ,
      s ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 →
      C * s ^ (-2 : ℤ) * M.delta ^ 2 ≤ theta →
        M.P.toMeasure {ω | theta ≤ (∑ m ∈ Finset.Icc m0 (m0 + K),
            if ∃ j : ℕ, 6 < (3 : ℝ) ^ (-(s * (j : ℝ))) *
                supNormOn (cube d ((m : ℤ) + 1 + (j : ℤ))) (fun x =>
                  (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |ω i x|) +
                    ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i x - ω i 0|) else 1)
              then (1 : ℝ) else 0) / (K + 1)} ≤
          ENNReal.ofReal (Real.exp (-(s ^ 2 * theta / (C * M.delta ^ 2)) * (K + 1))) := by
  refine ⟨1 + SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.fieldTwoDensityConst d ^ 2 +
    2 * |SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.fieldTwoRateDenom d|, by positivity, ?_⟩
  intro M m0 K s theta hs htheta hsmall
  have hdelta := M.shellPrefix.delta_pos
  have hc : 0 < SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.fieldTwoDensityConst d :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.fieldTwoDensityConst_pos M
  have hR : 0 < SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.fieldTwoRateDenom d :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.fieldTwoRateDenom_pos M
  set c := SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.fieldTwoDensityConst d with hcdef
  set R := SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.fieldTwoRateDenom d with hRdef
  have hCR : 2 * R ≤ 1 + c ^ 2 + 2 * |R| := by
    have := le_abs_self R
    nlinarith [sq_nonneg c]
  have hCc : c ^ 2 ≤ 1 + c ^ 2 + 2 * |R| := by
    nlinarith [abs_nonneg R]
  have hCpos : 0 < 1 + c ^ 2 + 2 * |R| := by positivity
  set C := 1 + c ^ 2 + 2 * |R| with hCdef
  have hs0 : 0 < s := hs.1
  have hθ0 : 0 < theta := htheta.1
  -- the Lean parameter `sL = min 1 (8 s)` lies in `(0,1]`, dominates `s`, and is at most `8 s`
  have hsL0 : 0 < min 1 (8 * s) := lt_min one_pos (by linarith)
  have hsL1 : min 1 (8 * s) ≤ 1 := min_le_left _ _
  have hsLs : s ≤ min 1 (8 * s) := le_min hs.2 (by linarith)
  have hsL8 : min 1 (8 * s) ≤ 8 * s := min_le_right _ _
  generalize hsLdef : min 1 (8 * s) = sL at hsL0 hsL1 hsLs hsL8
  -- smallness hypothesis of the Lean theorem
  have h1 : C * M.delta ^ 2 ≤ theta * s ^ 2 := by
    have hs2 : 0 < s ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hsmall hs2.le
    calc C * M.delta ^ 2 = C * s ^ (-2 : ℤ) * M.delta ^ 2 * s ^ 2 := by
          rw [zpow_neg]; field_simp
      _ ≤ theta * s ^ 2 := this
  have hcd : (c * M.delta) ^ 2 ≤ (sL * Real.sqrt theta) ^ 2 := by
    have hsq : (Real.sqrt theta) ^ 2 = theta := Real.sq_sqrt hθ0.le
    calc (c * M.delta) ^ 2 = c ^ 2 * M.delta ^ 2 := by ring
      _ ≤ C * M.delta ^ 2 := mul_le_mul_of_nonneg_right hCc (sq_nonneg _)
      _ ≤ theta * s ^ 2 := h1
      _ ≤ theta * sL ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hθ0.le
          exact pow_le_pow_left₀ hs0.le hsLs 2
      _ = (sL * Real.sqrt theta) ^ 2 := by rw [mul_pow, hsq]; ring
  have hcd' : c * M.delta ≤ sL * Real.sqrt theta := by
    by_contra hlt
    push_neg at hlt
    have hpos : 0 ≤ sL * Real.sqrt theta := by positivity
    have := mul_self_lt_mul_self hpos hlt
    nlinarith
  have hsmallL : M.delta ≤ c⁻¹ * sL * Real.sqrt theta := by
    rw [mul_assoc, le_inv_mul_iff₀ hc]
    exact hcd'
  have hmain : M.P.toMeasure {ω | theta ≤ SubdiffusiveProcess.CoarseGrainingVocab.intervalEventDensity
        (fun k => {ω' : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d | GoodFieldTwo k 0 sL ω'}ᶜ)
        m0 K ω} ≤
      ENNReal.ofReal (Real.exp (-(sL ^ 2 * theta / (2 * R * M.delta ^ 2)) * ((K : ℝ) + 1))) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.measure_goodFieldTwo_badDensity_le M
      hsL0 hsL1 htheta.1 htheta.2 hsmallL m0 K
  refine (MeasureTheory.measure_mono ?_).trans (hmain.trans ?_)
  · intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    refine hω.trans ?_
    simp only [SubdiffusiveProcess.CoarseGrainingVocab.intervalEventDensity,
      SubdiffusiveProcess.CoarseGrainingVocab.eventIndicator]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro m _
    by_cases h : ∃ j : ℕ, 6 < (3 : ℝ) ^ (-(s * (j : ℝ))) *
        supNormOn (cube d ((m : ℤ) + 1 + (j : ℤ))) (fun x =>
          (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |ω i x|) +
            ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i x - ω i 0|) else 1)
    · have hbad := (aux_l_exp_goodscales_iff m s ω).mp h
      have hbadL : ω ∈ {ω' : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d |
          GoodFieldTwo m 0 sL ω'}ᶜ := fun hg =>
        hbad (aux_l_exp_goodscales_mono m 0 hsL8 ω hg)
      rw [if_pos h, if_pos hbadL]
    · rw [if_neg h]
      split_ifs <;> norm_num
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    have hK : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
    have hk : s ^ 2 * theta / (C * M.delta ^ 2) ≤ sL ^ 2 * theta / (2 * R * M.delta ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hd2 : 0 ≤ M.delta ^ 2 := sq_nonneg _
      have hs2 : s ^ 2 ≤ sL ^ 2 := pow_le_pow_left₀ hs0.le hsLs 2
      calc s ^ 2 * theta * (2 * R * M.delta ^ 2)
          = (s ^ 2 * theta * M.delta ^ 2) * (2 * R) := by ring
        _ ≤ (s ^ 2 * theta * M.delta ^ 2) * C :=
            mul_le_mul_of_nonneg_left hCR (by positivity)
        _ ≤ (sL ^ 2 * theta * M.delta ^ 2) * C :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs2 hθ0.le) hd2) hCpos.le
        _ = sL ^ 2 * theta * (C * M.delta ^ 2) := by ring
    have := mul_le_mul_of_nonneg_right hk hK
    linarith

end Paper
