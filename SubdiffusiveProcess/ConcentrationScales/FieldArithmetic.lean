module

public import Mathlib

@[expose] public section

/-!
# Constant arithmetic for `p.concentration.for.scales.exp.field`

Real-variable inequality turning the single-exceedance bound
`3^{d(h+2j)} 2^{2j+1} exp(-t²/((2j+1)δ²))`, `t = (1+sj) log 3`, into `exp(-(c₁ s²/δ²)(j+1))` under the smallness
`δ² h (2 d log 3 + 2 log 2) ≤ c₁ s²`, `c₁ = (log 3)²/4`.
-/

namespace SubdiffusiveProcess.ConcentrationScales

/-- The constant `c₁ = (log 3)² / 4` of the exceedance rate. -/
noncomputable def fieldRate : ℝ := Real.log 3 ^ 2 / 4

/-- The entropy constant `2 d log 3 + 2 log 2`. -/
noncomputable def fieldEntropy (d : ℕ) : ℝ := 2 * d * Real.log 3 + 2 * Real.log 2

theorem fieldRate_pos : 0 < fieldRate := by
  unfold fieldRate
  have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  positivity

theorem fieldEntropy_pos (d : ℕ) : 0 < fieldEntropy d := by
  unfold fieldEntropy
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  positivity

theorem field_exponent_le (d h j : ℕ) (hh : 1 ≤ h) {s δ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hδ : 0 < δ)
    (hsmall : δ ^ 2 * h * fieldEntropy d ≤ fieldRate * s ^ 2) :
    d * (h + 2 * j) * Real.log 3 + (2 * j + 1) * Real.log 2 -
        ((1 + s * j) * Real.log 3) ^ 2 / ((2 * j + 1) * δ ^ 2) ≤
      -(fieldRate * s ^ 2 / δ ^ 2 * ((j : ℝ) + 1)) := by
  have hl3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hj1 : (0 : ℝ) < 2 * j + 1 := by positivity
  -- entropy
  have hent : (d : ℝ) * (h + 2 * j) * Real.log 3 + (2 * j + 1) * Real.log 2 ≤
      fieldEntropy d * h * (j + 1) := by
    unfold fieldEntropy
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have e1 : (h : ℝ) + 2 * j ≤ 2 * h * (j + 1) := by nlinarith
    have e2 : (2 : ℝ) * j + 1 ≤ 2 * h * (j + 1) := by nlinarith
    calc (d : ℝ) * (h + 2 * j) * Real.log 3 + (2 * j + 1) * Real.log 2
        ≤ d * (2 * h * (j + 1)) * Real.log 3 + (2 * h * (j + 1)) * Real.log 2 := by
          gcongr
      _ = (2 * d * Real.log 3 + 2 * Real.log 2) * h * (j + 1) := by ring
  -- Gaussian term
  have hsj : s * ((j : ℝ) + 1) ≤ 1 + s * j := by nlinarith
  have ht : ((j : ℝ) + 1) * s * Real.log 3 ≤ (1 + s * j) * Real.log 3 := by nlinarith
  have ht0 : 0 ≤ ((j : ℝ) + 1) * s * Real.log 3 := by positivity
  have ht2 : (((j : ℝ) + 1) * s * Real.log 3) ^ 2 ≤ ((1 + s * j) * Real.log 3) ^ 2 :=
    pow_le_pow_left₀ ht0 ht 2
  have hgauss : Real.log 3 ^ 2 * s ^ 2 * ((j : ℝ) + 1) / (2 * δ ^ 2) ≤
      ((1 + s * j) * Real.log 3) ^ 2 / ((2 * j + 1) * δ ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : Real.log 3 ^ 2 * s ^ 2 * ((j : ℝ) + 1) * ((2 * j + 1) * δ ^ 2) ≤
        ((j + 1) * s * Real.log 3) ^ 2 * (2 * δ ^ 2) := by
      have h3 : ((j : ℝ) + 1) * (2 * j + 1) ≤ ((j + 1) ^ 2) * 2 := by nlinarith
      have hA : 0 ≤ Real.log 3 ^ 2 * s ^ 2 * δ ^ 2 := by positivity
      calc Real.log 3 ^ 2 * s ^ 2 * ((j : ℝ) + 1) * ((2 * j + 1) * δ ^ 2)
          = (Real.log 3 ^ 2 * s ^ 2 * δ ^ 2) * (((j : ℝ) + 1) * (2 * j + 1)) := by ring
        _ ≤ (Real.log 3 ^ 2 * s ^ 2 * δ ^ 2) * (((j + 1) ^ 2) * 2) := by gcongr
        _ = ((j + 1) * s * Real.log 3) ^ 2 * (2 * δ ^ 2) := by ring
    calc Real.log 3 ^ 2 * s ^ 2 * ((j : ℝ) + 1) * ((2 * j + 1) * δ ^ 2)
        ≤ ((j + 1) * s * Real.log 3) ^ 2 * (2 * δ ^ 2) := this
      _ ≤ ((1 + s * j) * Real.log 3) ^ 2 * (2 * δ ^ 2) := by gcongr
  -- assemble
  have hres : fieldEntropy d * h * ((j : ℝ) + 1) ≤ fieldRate * s ^ 2 / δ ^ 2 * ((j : ℝ) + 1) := by
    have : fieldEntropy d * h ≤ fieldRate * s ^ 2 / δ ^ 2 := by
      rw [le_div_iff₀ hδ2]
      nlinarith [hsmall]
    gcongr
  have hgeq : Real.log 3 ^ 2 * s ^ 2 * ((j : ℝ) + 1) / (2 * δ ^ 2) =
      2 * (fieldRate * s ^ 2 / δ ^ 2 * ((j : ℝ) + 1)) := by
    unfold fieldRate
    field_simp
    ring
  linarith

/-- The threshold `3 · 3^{s j}` of the exceedance events written as an exponential. -/
theorem three_mul_rpow_eq_exp (s : ℝ) (j : ℕ) :
    (3 : ℝ) * (3 : ℝ) ^ (s * j) = Real.exp ((1 + s * j) * Real.log 3) := by
  rw [show (1 + s * j) * Real.log 3 = Real.log 3 + Real.log 3 * (s * j) by ring, Real.exp_add,
    Real.exp_log (by norm_num), ← Real.rpow_def_of_pos (by norm_num)]

/-- Choice of the universal constant: `C` dominating the three thresholds of the assembly. -/
theorem exists_field_constant (d : ℕ) {cr Cr : ℝ} (hcr : 0 < cr) (hCr : 0 < Cr) :
    ∃ C : ℝ, 0 < C ∧ fieldEntropy d / fieldRate ≤ C ^ 2 ∧ Cr / fieldRate ≤ C ^ 2 ∧
      1 / (cr * fieldRate) ≤ C := by
  have hc1 := fieldRate_pos
  have hEd := fieldEntropy_pos d
  have hs1 : 0 ≤ Real.sqrt (fieldEntropy d / fieldRate) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt (Cr / fieldRate) := Real.sqrt_nonneg _
  have hs3 : 0 ≤ 1 / (cr * fieldRate) := by positivity
  refine ⟨1 + Real.sqrt (fieldEntropy d / fieldRate) + Real.sqrt (Cr / fieldRate) +
    1 / (cr * fieldRate), by positivity, ?_, ?_, by linarith⟩
  · calc fieldEntropy d / fieldRate = Real.sqrt (fieldEntropy d / fieldRate) ^ 2 :=
          (Real.sq_sqrt (by positivity)).symm
      _ ≤ _ := pow_le_pow_left₀ hs1 (by linarith) 2
  · calc Cr / fieldRate = Real.sqrt (Cr / fieldRate) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ ≤ _ := pow_le_pow_left₀ hs2 (by linarith) 2

/-- The three consequences of the smallness hypothesis `δ ≤ C⁻¹ s (θ ∧ h⁻¹)^{1/2}` used in the assembly:
the entropy absorption, the hypothesis `C_rare ≤ λθ` of the rare-interval lemma, and the final rate comparison. -/
theorem field_smallness (d h : ℕ) (hh : 1 ≤ h) {C Cr cr δ s θ : ℝ} (hC : 0 < C) (hcr : 0 < cr)
    (hδ : 0 < δ) (hs : 0 < s) (hθ : 0 < θ) (hC1 : fieldEntropy d / fieldRate ≤ C ^ 2)
    (hC2 : Cr / fieldRate ≤ C ^ 2) (hC3 : 1 / (cr * fieldRate) ≤ C)
    (hsmall : δ ≤ C⁻¹ * s * Real.sqrt (min θ ((h : ℝ)⁻¹))) :
    δ ^ 2 * h * fieldEntropy d ≤ fieldRate * s ^ 2 ∧ Cr ≤ fieldRate * s ^ 2 / δ ^ 2 * θ ∧
      s ^ 2 * θ / (C * δ ^ 2) ≤ cr * (fieldRate * s ^ 2 / δ ^ 2) * θ := by
  have hc1pos := fieldRate_pos
  have hEdpos := fieldEntropy_pos d
  have hm0 : 0 ≤ min θ ((h : ℝ)⁻¹) := le_min hθ.le (by positivity)
  have hδsq : δ ^ 2 ≤ C⁻¹ ^ 2 * s ^ 2 * min θ ((h : ℝ)⁻¹) := by
    calc δ ^ 2 ≤ (C⁻¹ * s * Real.sqrt (min θ ((h : ℝ)⁻¹))) ^ 2 := pow_le_pow_left₀ hδ.le hsmall 2
      _ = C⁻¹ ^ 2 * s ^ 2 * min θ ((h : ℝ)⁻¹) := by rw [mul_pow, mul_pow, Real.sq_sqrt hm0]
  have hδθ : δ ^ 2 ≤ C⁻¹ ^ 2 * s ^ 2 * θ := hδsq.trans (by gcongr; exact min_le_left _ _)
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hδh : δ ^ 2 * h ≤ C⁻¹ ^ 2 * s ^ 2 := by
    calc δ ^ 2 * h ≤ (C⁻¹ ^ 2 * s ^ 2 * (h : ℝ)⁻¹) * h := by
          gcongr
          exact hδsq.trans (by gcongr; exact min_le_right _ _)
      _ = C⁻¹ ^ 2 * s ^ 2 := by field_simp
  have hδ2pos : 0 < δ ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have hEC : C⁻¹ ^ 2 * fieldEntropy d ≤ fieldRate := by
      have : fieldEntropy d ≤ fieldRate * C ^ 2 := by rwa [div_le_iff₀ hc1pos, mul_comm] at hC1
      rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
      linarith
    calc δ ^ 2 * h * fieldEntropy d ≤ C⁻¹ ^ 2 * s ^ 2 * fieldEntropy d := by gcongr
      _ = (C⁻¹ ^ 2 * fieldEntropy d) * s ^ 2 := by ring
      _ ≤ fieldRate * s ^ 2 := by gcongr
  · have h1' : C ^ 2 ≤ s ^ 2 * θ / δ ^ 2 := by
      rw [le_div_iff₀ hδ2pos]
      calc C ^ 2 * δ ^ 2 ≤ C ^ 2 * (C⁻¹ ^ 2 * s ^ 2 * θ) := by gcongr
        _ = s ^ 2 * θ := by field_simp
    calc Cr = fieldRate * (Cr / fieldRate) := by field_simp
      _ ≤ fieldRate * C ^ 2 := by gcongr
      _ ≤ fieldRate * (s ^ 2 * θ / δ ^ 2) := by gcongr
      _ = fieldRate * s ^ 2 / δ ^ 2 * θ := by ring
  · have hone : 1 ≤ C * (cr * fieldRate) := by
      have := hC3
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    rw [div_le_iff₀ (by positivity)]
    calc s ^ 2 * θ ≤ s ^ 2 * θ * (C * (cr * fieldRate)) :=
          le_mul_of_one_le_right (by positivity) hone
      _ = cr * (fieldRate * s ^ 2 / δ ^ 2) * θ * (C * δ ^ 2) := by field_simp

end SubdiffusiveProcess.ConcentrationScales
