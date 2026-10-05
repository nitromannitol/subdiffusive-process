module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTailThreshold

@[expose] public section

/-!
# The layer-zero tail

`mfd:in-deterministic` and `s.tightness` requires the layer-zero failure
probability to be at most `C e^{-c q}` with `q = c δ^{-2}|log δ|^{-2}`,
**uniformly in the scale `n`**.  The concrete layer-zero predicate of
`Section9GoodCubeTailThreshold` meets that requirement: its deterministic
reduction spends, at shell `k ≤ n`, the deviation
`√(tailIndex M ² + (n - k))`, whose Gaussian-type cost `e^{-(n-k)}` beats the
`n + 1` terms of the union bound with a geometric series, so the total is
`2 e^{-tailIndex M ²}` at every `n`.

The price is that the *threshold itself*, `logLipschitzThreshold M n`, grows
with `n` — exactly as the manuscript's threshold `B(1 + n)`
does.  The consequences of that growth are recorded in
`Section9GoodCubeTailResidual.lean`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Homogenization Set
open Homogenization.IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open _root_.SubdiffusiveProcess.Model

variable {d : ℕ}

/-! ## The geometric series of the union bound -/

theorem exp_neg_one_pow (m : ℕ) : Real.exp (-1 : ℝ) ^ m = Real.exp (-(m : ℝ)) := by
  induction m with
  | zero => simp
  | succ i ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

theorem exp_neg_one_le_half : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2
  rw [Real.exp_neg, inv_eq_one_div]
  exact h

theorem geom_sum_exp_neg_one_le (N : ℕ) :
    ∑ m ∈ Finset.range N, Real.exp (-1 : ℝ) ^ m ≤ 2 := by
  set x : ℝ := Real.exp (-1 : ℝ) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hxh : x ≤ 1 / 2 := exp_neg_one_le_half
  set S : ℝ := ∑ m ∈ Finset.range N, x ^ m with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ => pow_nonneg hx0.le m
  have hstep : S * (x - 1) = x ^ N - 1 := geom_sum_mul x N
  have hxn : 0 ≤ x ^ N := pow_nonneg hx0.le N
  nlinarith [mul_le_mul_of_nonneg_left hxh hS0]

/-- **The per-shell costs sum, uniformly in the scale.** -/
theorem sum_exp_neg_shellDeviation_sq_le (M : GMCModel d) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Real.exp (-(shellDeviation M n k ^ 2)) ≤
      2 * Real.exp (-(tailIndex M ^ 2)) := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      Real.exp (-(shellDeviation M n k ^ 2)) =
        Real.exp (-(tailIndex M ^ 2)) * Real.exp (-1 : ℝ) ^ (n - k) := by
    intro k _
    rw [shellDeviation_sq, exp_neg_one_pow, ← Real.exp_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hrefl : ∑ k ∈ Finset.range (n + 1), Real.exp (-1 : ℝ) ^ (n - k) =
      ∑ m ∈ Finset.range (n + 1), Real.exp (-1 : ℝ) ^ m := by
    simpa using Finset.sum_range_reflect (fun m => Real.exp (-1 : ℝ) ^ m) (n + 1)
  rw [hrefl]
  have hpos : 0 < Real.exp (-(tailIndex M ^ 2)) := Real.exp_pos _
  calc Real.exp (-(tailIndex M ^ 2)) * ∑ m ∈ Finset.range (n + 1), Real.exp (-1 : ℝ) ^ m
      ≤ Real.exp (-(tailIndex M ^ 2)) * 2 :=
        mul_le_mul_of_nonneg_left (geom_sum_exp_neg_one_le (n + 1)) hpos.le
    _ = 2 * Real.exp (-(tailIndex M ^ 2)) := by ring

/-! ## The layer-zero tail -/

/-- **The layer-zero tail at the origin.** -/
theorem measure_observation_goodCubeBad_le (M : GMCModel d) (n : ℕ) :
    M.P.toMeasure
        (restrictedCoefficientObservation (aCutoff M n) (nativeBox n 1 (0 : Lattice d)) ⁻¹'
          goodCubeBad M n) ≤
      ENNReal.ofReal (2 * Real.exp (-(tailIndex M ^ 2))) := by
  refine (measure_mono (observation_goodCubeBad_subset M n)).trans ?_
  refine (measure_biUnion_finset_le (Finset.range (n + 1)) _).trans ?_
  have hshell : ∀ k ∈ Finset.range (n + 1),
      M.P.toMeasure (upperTailEvent (coverShellG2 k (0 : Vec d) (shellCoverDepth n k))
          (coverEntropyScale M (shellCoverDepth n k) * shellDeviation M n k)) ≤
        ENNReal.ofReal (Real.exp (-(shellDeviation M n k ^ 2))) := fun k _ =>
    measure_upperTail_coverShellG2_le M k (0 : Vec d) (shellCoverDepth n k)
      (one_le_shellDeviation M n k)
  refine (Finset.sum_le_sum hshell).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal (sum_exp_neg_shellDeviation_sq_le M n)

/-- **The layer-zero tail at every site.** -/
theorem measure_coefficientLocalBadEvent_goodCubeBad_le (M : GMCModel d) (n : ℕ)
    (z : Lattice d) :
    M.P.toMeasure (coefficientLocalBadEvent M n 1 (goodCubeBad M n) z) ≤
      ENNReal.ofReal (2 * Real.exp (-(tailIndex M ^ 2))) := by
  have hrw : M.P.toMeasure (coefficientLocalBadEvent M n 1 (goodCubeBad M n) z) =
      M.P.toMeasure
        (restrictedCoefficientObservation (aCutoff M n) (nativeBox n 1 (0 : Lattice d)) ⁻¹'
          goodCubeBad M n) := by
    rw [coefficientLocalBadEvent, measure_preimage_translatePotentialSequence]
  rw [hrw]
  exact measure_observation_goodCubeBad_le M n

/-- **The `.tail` display of `GoodCubeAnalyticDisplays`, for the concrete
layer-zero predicate.**  The exponent is the printed
`c·(c δ^{-2}|log δ|^{-2})` of `mfd:in-deterministic` and `s.tightness`, and the
bound is uniform in the scale `n` and the site `z`. -/
theorem goodCubeBad_tail (M : GMCModel d) {c C : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hC : 2 ≤ C)
    (n : ℕ) (z : Lattice d) :
    M.P.toMeasure (coefficientLocalBadEvent M n 1 (goodCubeBad M n) z) ≤
      ENNReal.ofReal
        (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2))))) := by
  refine (measure_coefficientLocalBadEvent_goodCubeBad_le M n z).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) = c ^ 2 * tailIndex M ^ 2 := by
    rw [tailIndex_sq]
    ring
  have ht0 : 0 ≤ tailIndex M ^ 2 := sq_nonneg _
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have hle : c ^ 2 * tailIndex M ^ 2 ≤ tailIndex M ^ 2 := by nlinarith
  have hexp : Real.exp (-(tailIndex M ^ 2)) ≤
      Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)))) := by
    rw [hsq]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpos : 0 < Real.exp (-(tailIndex M ^ 2)) := Real.exp_pos _
  calc 2 * Real.exp (-(tailIndex M ^ 2))
      ≤ C * Real.exp (-(tailIndex M ^ 2)) := mul_le_mul_of_nonneg_right hC hpos.le
    _ ≤ C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)))) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
