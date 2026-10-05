module

public import Mathlib
public import SubdiffusiveProcess.Model.OGammaLE

@[expose] public section

/-!
# Ingredients of `p.concentration.for.scales.exp.sequence`

* the deterministic witness step: if `X_{k+j} ≤ (log 3 / 3)(1 + s j)` for all `j`, no forward sum
  `∑_{i≥0} 3^{-i} X_{k+i+j}` exceeds `(1+sj) log 3`;
* the tail bound `P[Y > u] ≤ 2 exp(-(u/δ)²)` from `Y = O_{Γ₂}(δ)` in the expectation convention;
* the exponent inequality and the choice of the universal constant.
-/

namespace SubdiffusiveProcess.ConcentrationScales

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- `∑_{i ≥ 0} 3^{-i} (1 + i) = 9/4`. -/
theorem hasSum_third_pow_mul_succ : HasSum (fun i : ℕ => ((1 : ℝ) / 3) ^ i * (1 + i)) (9 / 4) := by
  have h1 : HasSum (fun i : ℕ => ((1 : ℝ) / 3) ^ i) (3 / 2) := by
    have := hasSum_geometric_of_lt_one (r := (1 : ℝ) / 3) (by norm_num) (by norm_num)
    convert this using 1
    norm_num
  have h2 : HasSum (fun i : ℕ => (i : ℝ) * ((1 : ℝ) / 3) ^ i) (3 / 4) := by
    have := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := (1 : ℝ) / 3) (by norm_num)
    convert this using 1
    norm_num
  have h3 := h1.add h2
  convert h3 using 1
  · funext i
    ring
  · norm_num

theorem rpow_neg_natCast_eq (i : ℕ) : (3 : ℝ) ^ (-(i : ℝ)) = ((1 : ℝ) / 3) ^ i := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]

/-- Deterministic step: a sequence below the linear barrier `(log 3 / 3)(1 + s j)` has all forward sums
below `(3/4)(1 + s j) log 3`. -/
theorem tsum_ofReal_le_of_forall_le (x : ℤ → ℝ) {s : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) (k : ℤ) (h : ∀ j : ℕ, x (k + j) ≤ Real.log 3 / 3 * (1 + s * j)) (j : ℕ) :
    ∑' i : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(i : ℝ)) * x (k + i + j)) ≤
      ENNReal.ofReal (3 / 4 * (1 + s * j) * Real.log 3) := by
  have hl3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  set c : ℝ := Real.log 3 / 3 * (1 + s * j) with hc
  have hcnn : 0 ≤ c := by positivity
  have hterm : ∀ i : ℕ, (3 : ℝ) ^ (-(i : ℝ)) * x (k + i + j) ≤ c * (((1 : ℝ) / 3) ^ i * (1 + i)) := by
    intro i
    have h1 := h (i + j)
    have h2 : x (k + i + j) = x (k + ((i + j : ℕ) : ℤ)) := by
      congr 1
      push_cast
      ring
    rw [rpow_neg_natCast_eq, h2]
    have h3 : Real.log 3 / 3 * (1 + s * ((i + j : ℕ) : ℝ)) ≤ c * (1 + i) := by
      rw [hc]
      push_cast
      have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have : 1 + s * ((i : ℝ) + j) ≤ (1 + s * j) * (1 + i) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hi, mul_nonneg (mul_nonneg hs.le hj) hi]
      nlinarith [this, hl3]
    have hp : (0 : ℝ) ≤ ((1 : ℝ) / 3) ^ i := by positivity
    calc ((1 : ℝ) / 3) ^ i * x (k + ((i + j : ℕ) : ℤ)) ≤ ((1 : ℝ) / 3) ^ i * (c * (1 + i)) :=
          mul_le_mul_of_nonneg_left (h1.trans h3) hp
      _ = c * (((1 : ℝ) / 3) ^ i * (1 + i)) := by ring
  have hsum := hasSum_third_pow_mul_succ.mul_left c
  calc ∑' i : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(i : ℝ)) * x (k + i + j))
      ≤ ∑' i : ℕ, ENNReal.ofReal (c * (((1 : ℝ) / 3) ^ i * (1 + i))) :=
        ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (hterm i)
    _ = ENNReal.ofReal (∑' i : ℕ, c * (((1 : ℝ) / 3) ^ i * (1 + i))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum.summable).symm
    _ = ENNReal.ofReal (3 / 4 * (1 + s * j) * Real.log 3) := by
        rw [hsum.tsum_eq, hc]
        congr 1
        ring

/-- The tail bound `P[Y > u] ≤ 2 exp(-(u/δ)²)` from `E exp((Y⁺/δ)²) ≤ 2`. -/
theorem measure_lt_le_of_OGammaLE {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} {δ : ℝ} (hδ : 0 < δ) (hO : SubdiffusiveProcess.OGammaLE μ 2 δ Y)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | u < Y ω} ≤ ENNReal.ofReal (2 * Real.exp (-(u / δ) ^ 2)) := by
  obtain ⟨hint, hle⟩ := hO
  set e : ℝ := Real.exp ((δ⁻¹ * u) ^ (2 : ℝ)) with he
  have hepos : 0 < e := Real.exp_pos _
  have hsub : {ω | u < Y ω} ⊆
      {ω | e ≤ Real.exp ((δ⁻¹ * max (Y ω) 0) ^ (2 : ℝ))} := by
    intro ω hω
    have hω' : u < Y ω := hω
    have hmax : max (Y ω) 0 = Y ω := max_eq_left (by linarith)
    show e ≤ Real.exp ((δ⁻¹ * max (Y ω) 0) ^ (2 : ℝ))
    rw [he, hmax, Real.rpow_two, Real.rpow_two]
    refine Real.exp_le_exp.mpr ?_
    have hδi : 0 < δ⁻¹ := inv_pos.mpr hδ
    have : δ⁻¹ * u ≤ δ⁻¹ * Y ω := by nlinarith
    have h0 : 0 ≤ δ⁻¹ * u := by positivity
    nlinarith
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun ω => Real.exp ((δ⁻¹ * max (Y ω) 0) ^ (2 : ℝ)))
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hint e
  have hreal : μ.real {ω | e ≤ Real.exp ((δ⁻¹ * max (Y ω) 0) ^ (2 : ℝ))} ≤ 2 / e := by
    rw [le_div_iff₀ hepos, mul_comm]
    exact hmark.trans hle
  calc μ {ω | u < Y ω} ≤ μ {ω | e ≤ Real.exp ((δ⁻¹ * max (Y ω) 0) ^ (2 : ℝ))} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | e ≤ Real.exp ((δ⁻¹ * max (Y ω) 0) ^ (2 : ℝ))}) :=
        (ofReal_measureReal (measure_ne_top μ _)).symm
    _ ≤ ENNReal.ofReal (2 / e) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (2 * Real.exp (-(u / δ) ^ 2)) := by
        congr 1
        rw [he, Real.rpow_two, div_eq_mul_inv, ← Real.exp_neg]
        congr 2
        rw [inv_mul_eq_div]

/-- The constant `c₂ = (log 3 / 3)² / 2` of the rate of `p.concentration.for.scales.exp.sequence`. -/
def seqRate : ℝ := (Real.log 3 / 3) ^ 2 / 2

theorem seqRate_pos : 0 < seqRate := by
  unfold seqRate
  have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  positivity

/-- Single-event exponent: `2 exp(-(c₀(1+sj)/δ)²) ≤ exp(-(c₂ s/δ²)(j+1))` for `δ² log 2 ≤ c₂ s`. -/
theorem seq_single_le (j : ℕ) {s δ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hδ : 0 < δ)
    (hsmall : δ ^ 2 * Real.log 2 ≤ seqRate * s) :
    2 * Real.exp (-(Real.log 3 / 3 * (1 + s * j) / δ) ^ 2) ≤
      Real.exp (-(seqRate * s / δ ^ 2 * ((j : ℝ) + 1))) := by
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h2 : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  rw [h2, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  -- (1 + s j)² ≥ s (j + 1)
  have hsq : s * ((j : ℝ) + 1) ≤ (1 + s * j) ^ 2 := by
    nlinarith [mul_nonneg hs.le hj, sq_nonneg (s * j)]
  have hA : seqRate * s * ((j : ℝ) + 1) * 2 / δ ^ 2 ≤ (Real.log 3 / 3 * (1 + s * j) / δ) ^ 2 := by
    rw [div_pow, mul_pow, div_le_div_iff_of_pos_right hδ2]
    unfold seqRate
    nlinarith [sq_nonneg (Real.log 3 / 3)]
  have hB : Real.log 2 ≤ seqRate * s / δ ^ 2 * ((j : ℝ) + 1) := by
    have h1 : Real.log 2 ≤ seqRate * s / δ ^ 2 := by
      rw [le_div_iff₀ hδ2]
      linarith
    have h2 : seqRate * s / δ ^ 2 ≤ seqRate * s / δ ^ 2 * ((j : ℝ) + 1) := by
      have : 0 ≤ seqRate * s / δ ^ 2 := by have := seqRate_pos; positivity
      nlinarith
    linarith
  have hC : seqRate * s / δ ^ 2 * ((j : ℝ) + 1) * 2 =
      seqRate * s * ((j : ℝ) + 1) * 2 / δ ^ 2 := by ring
  nlinarith [hA, hB, hC]

/-- Choice of the universal constant. -/
theorem exists_seq_constant {cr Cr : ℝ} (hcr : 0 < cr) (hCr : 0 < Cr) :
    ∃ C : ℝ, 0 < C ∧ Real.log 2 / seqRate ≤ C ^ 2 ∧ Cr / seqRate ≤ C ^ 2 ∧
      1 / (cr * seqRate) ≤ C := by
  have hc2 := seqRate_pos
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hs1 : 0 ≤ Real.sqrt (Real.log 2 / seqRate) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt (Cr / seqRate) := Real.sqrt_nonneg _
  have hs3 : 0 ≤ 1 / (cr * seqRate) := by positivity
  refine ⟨1 + Real.sqrt (Real.log 2 / seqRate) + Real.sqrt (Cr / seqRate) +
    1 / (cr * seqRate), by positivity, ?_, ?_, by linarith⟩
  · calc Real.log 2 / seqRate = Real.sqrt (Real.log 2 / seqRate) ^ 2 :=
          (Real.sq_sqrt (by positivity)).symm
      _ ≤ _ := pow_le_pow_left₀ hs1 (by linarith) 2
  · calc Cr / seqRate = Real.sqrt (Cr / seqRate) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ ≤ _ := pow_le_pow_left₀ hs2 (by linarith) 2

/-- The consequences of `δ ≤ C⁻¹ √(s θ)`: single-event absorption, `C_rare ≤ λθ`, and the rate comparison. -/
theorem seq_smallness {C Cr cr δ s θ : ℝ} (hC : 0 < C) (hcr : 0 < cr) (hδ : 0 < δ) (hs : 0 < s)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC1 : Real.log 2 / seqRate ≤ C ^ 2) (hC2 : Cr / seqRate ≤ C ^ 2)
    (hC3 : 1 / (cr * seqRate) ≤ C) (hsmall : δ ≤ C⁻¹ * Real.sqrt (s * θ)) :
    δ ^ 2 * Real.log 2 ≤ seqRate * s ∧ Cr ≤ seqRate * s / δ ^ 2 * θ ∧
      s * θ / (C * δ ^ 2) ≤ cr * (seqRate * s / δ ^ 2) * θ := by
  have hc2 := seqRate_pos
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hδsq : δ ^ 2 ≤ C⁻¹ ^ 2 * (s * θ) := by
    calc δ ^ 2 ≤ (C⁻¹ * Real.sqrt (s * θ)) ^ 2 := pow_le_pow_left₀ hδ.le hsmall 2
      _ = C⁻¹ ^ 2 * (s * θ) := by rw [mul_pow, Real.sq_sqrt (by positivity)]
  refine ⟨?_, ?_, ?_⟩
  · have hsθ : s * θ ≤ s := by nlinarith
    have hEC : C⁻¹ ^ 2 * Real.log 2 ≤ seqRate := by
      have : Real.log 2 ≤ seqRate * C ^ 2 := by rwa [div_le_iff₀ hc2, mul_comm] at hC1
      rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
      linarith
    calc δ ^ 2 * Real.log 2 ≤ C⁻¹ ^ 2 * (s * θ) * Real.log 2 := by gcongr
      _ ≤ C⁻¹ ^ 2 * s * Real.log 2 := by gcongr
      _ = (C⁻¹ ^ 2 * Real.log 2) * s := by ring
      _ ≤ seqRate * s := by gcongr
  · have h1' : C ^ 2 ≤ s * θ / δ ^ 2 := by
      rw [le_div_iff₀ hδ2]
      calc C ^ 2 * δ ^ 2 ≤ C ^ 2 * (C⁻¹ ^ 2 * (s * θ)) := by gcongr
        _ = s * θ := by field_simp
    calc Cr = seqRate * (Cr / seqRate) := by field_simp
      _ ≤ seqRate * C ^ 2 := by gcongr
      _ ≤ seqRate * (s * θ / δ ^ 2) := by gcongr
      _ = seqRate * s / δ ^ 2 * θ := by ring
  · have hone : 1 ≤ C * (cr * seqRate) := by
      have := hC3
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    rw [div_le_iff₀ (by positivity)]
    calc s * θ ≤ s * θ * (C * (cr * seqRate)) := le_mul_of_one_le_right (by positivity) hone
      _ = cr * (seqRate * s / δ ^ 2) * θ * (C * δ ^ 2) := by field_simp

end

end SubdiffusiveProcess.ConcentrationScales
