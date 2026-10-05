module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeLargeBox

@[expose] public section

/-!
# The layer-zero cover gauge and its Gaussian-type tail

The layer events `B_j(U)`  see a
*single* shell `n + j`, and their tail is
`Section9GoodCubeLargeBox.measure_layerEvent_le_cover`.  The **layer-zero**
event  sees the coefficient `a_n` itself, hence all of the
shells `0, …, n` at once, and its native box `U` has side `3^n` — many
wavelengths of every shell `k < n`.

This file records the two ingredients the layer-zero tail needs and that the
layer machinery did not:

* `coverEntropyScale`, the `Γ₂` scale of the covering gauge `coverShellG2` at a
  cover depth `r`, which grows like `(3 d (r+1) log 3)^{1/2}·δ` — this is the
  entropy of the `3^{d(r+1)}` unit cells the box of side `3^{k+r}` is cut into;
* `measure_upperTail_coverShellG2_le`, the resulting tail at an arbitrary
  deviation `t ≥ 1`, in the `ENNReal` form the frozen clause uses.

Both are stated at an arbitrary centre `y` and depth `r`, because the layer-zero
sum uses a *different* depth at every shell: shell `k ≤ n` sees the box of side
`3^n = 3^k · 3^{n-k}` and therefore needs depth `n - k + 1`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Homogenization Set
open Homogenization.IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open _root_.SubdiffusiveProcess.Model

variable {d : ℕ}

/-! ## The `Γ₂` scale of the covering gauge -/

/-- The `Γ₂` scale of `coverShellG2 k y r`: the maximum-of-`N` scale
`(3 log N)^{1/2}` of `Homogenization.IndependentSums.isBigOWith_gammaSigma_finset_sup'`
applied to the `N = card (shellCoverShifts d r)` translated own-scale `(g2)`
gauges, each of which has scale `(1 + log 2)^{1/2} δ`. -/
def coverEntropyScale (M : GMCModel d) (r : ℤ) : ℝ :=
  ((3 * Real.log (((shellCoverShifts d r).card : ℕ) : ℝ)) ^ (2 : ℝ)⁻¹) *
    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)

theorem coverEntropyScale_nonneg (M : GMCModel d) (r : ℤ) :
    0 ≤ coverEntropyScale M r := by
  have hcard : (1 : ℝ) ≤ ((shellCoverShifts d r).card : ℝ) := by
    exact_mod_cast (shellCoverShifts_nonempty d r).card_pos
  have hlog : 0 ≤ 3 * Real.log (((shellCoverShifts d r).card : ℕ) : ℝ) := by
    have := Real.log_nonneg hcard
    linarith
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have h1 : (0 : ℝ) ≤ (3 * Real.log (((shellCoverShifts d r).card : ℕ) : ℝ)) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_nonneg hlog _
  have h2 : (0 : ℝ) ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) hdelta.le
  exact mul_nonneg h1 h2

/-- **The covering gauge is `Γ₂`-subgaussian at scale `coverEntropyScale`.**  The
finite-maximum lemma of the concentration chapter, applied to the cover of the
translated triadic cube `y + cu_r`. -/
theorem isBigOWith_gammaTwo_coverShellG2 (M : GMCModel d) (k : ℕ) (y : Vec d)
    (r : ℤ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2) (coverShellG2 k y r)
      (coverEntropyScale M r) :=
  isBigOWith_gammaSigma_finset_sup'
    (μ := M.P.toMeasure) (shellCoverShifts d r) (shellCoverShifts_nonempty d r)
    (by norm_num) (shellCoverShifts_card_ge_two M r)
    (fun p _ => isBigOWith_gammaTwo_translatedShellG2 M k (y + shellCoverCenter p))

/-- **The layer-zero per-shell tail.**  At any deviation `t ≥ 1` the covering
gauge exceeds `coverEntropyScale M r · t` with probability at most `e^{-t²}`. -/
theorem measure_upperTail_coverShellG2_le (M : GMCModel d) (k : ℕ) (y : Vec d)
    (r : ℤ) {t : ℝ} (ht : 1 ≤ t) :
    M.P.toMeasure (upperTailEvent (coverShellG2 k y r) (coverEntropyScale M r * t)) ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2))) := by
  have htail := isBigOWith_gammaTwo_coverShellG2 M k y r ht
  have hg : (gammaSigma 2 t)⁻¹ = Real.exp (-(t ^ 2)) := by
    rw [gammaSigma_apply, ← Real.exp_neg]
    congr 1
    rw [← Real.rpow_natCast t 2]
    norm_num
  rw [hg] at htail
  have hne : M.P.toMeasure
      (upperTailEvent (coverShellG2 k y r) (coverEntropyScale M r * t)) ≠ ⊤ :=
    measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal htail

/-! ## The disorder-only deviation index -/

/-- The deviation index `δ^{-1}|log δ|^{-1}` at which the layer-zero tail is
read.  It is a function of the model alone — the frozen clause's `c` is not
available when the bad predicate is chosen — and its square is the printed
exponent `δ^{-2}|log δ|^{-2}`. -/
def tailIndex (M : GMCModel d) : ℝ := (M.delta * (-Real.log M.delta))⁻¹

theorem neg_log_delta_pos (M : GMCModel d) : 0 < -Real.log M.delta := by
  have h1 : M.delta ≤ (1 : ℝ) / 2 := M.shellPrefix.delta_le_half
  have h2 : 0 < M.delta := M.shellPrefix.delta_pos
  have : Real.log M.delta ≤ Real.log ((1 : ℝ) / 2) := Real.log_le_log h2 h1
  have hhalf : Real.log ((1 : ℝ) / 2) < 0 := by
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub, neg_lt, neg_zero]
    exact Real.log_pos (by norm_num)
  linarith

theorem delta_mul_neg_log_lt_one (M : GMCModel d) :
    M.delta * (-Real.log M.delta) < 1 := by
  have h2 : 0 < M.delta := M.shellPrefix.delta_pos
  have hinv : Real.log M.delta⁻¹ ≤ M.delta⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at hinv
  have hmul := mul_le_mul_of_nonneg_left hinv h2.le
  have hrw : M.delta * (M.delta⁻¹ - 1) = 1 - M.delta := by
    field_simp
  rw [hrw] at hmul
  linarith

theorem one_le_tailIndex (M : GMCModel d) : 1 ≤ tailIndex M := by
  have hpos : 0 < M.delta * (-Real.log M.delta) :=
    mul_pos M.shellPrefix.delta_pos (neg_log_delta_pos M)
  have hlt := delta_mul_neg_log_lt_one M
  rw [tailIndex, le_inv_comm₀ one_pos hpos]
  simpa using hlt.le

theorem tailIndex_pos (M : GMCModel d) : 0 < tailIndex M :=
  lt_of_lt_of_le one_pos (one_le_tailIndex M)

/-- The square of the deviation index is the printed exponent. -/
theorem tailIndex_sq (M : GMCModel d) :
    tailIndex M ^ 2 = 1 / (M.delta ^ 2 * Real.log M.delta ^ 2) := by
  have hd : M.delta ≠ 0 := ne_of_gt M.shellPrefix.delta_pos
  have hl : Real.log M.delta ≠ 0 := by
    have := neg_log_delta_pos M
    intro h
    rw [h] at this
    simp at this
  rw [tailIndex, inv_pow, mul_pow, neg_pow_two]
  field_simp

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
