module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.EntropyGeometric
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.SharpErrorWindowFluctuation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedAccumulatedErrorWindow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseGamma

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open Homogenization hiding Vec
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## An unshifted geometric tail -/

/-- Reverse-indexed geometric sum, in the unshifted `q` convention. -/
theorem sum_geom_reverse_le {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho ≤ 1 / 2)
    {q m : ℕ} (hqm : q ≤ m) :
    ∑ n ∈ Finset.range (m - q + 1), rho ^ (m - n) ≤ 2 * rho ^ q := by
  rw [sum_pow_sub_eq_pow_mul (rho := rho) hqm]
  have hgeom := geom_partial_sum_le_two h0 h1 (m - q + 1)
  have hpow : (0 : ℝ) ≤ rho ^ q := pow_nonneg h0 q
  calc rho ^ q * ∑ j ∈ Finset.range (m - q + 1), rho ^ j
      ≤ rho ^ q * 2 := mul_le_mul_of_nonneg_left hgeom hpow
    _ = 2 * rho ^ q := by ring

/-- The starting-scale union, summed in the unshifted `q` convention. -/
theorem sum_exp_neg_sq_gap_le {u : ℝ} (hu : 1 ≤ u) {q m : ℕ} (hqm : q ≤ m) :
    (∑ n ∈ Finset.range (m - q + 1),
      Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ))))) ≤
      2 * Real.exp (-(u ^ 2 * (q : ℝ))) := by
  have hu2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith
  set rho : ℝ := Real.exp (-(u ^ 2)) with hrhodef
  have hrho0 : 0 ≤ rho := (Real.exp_pos _).le
  have hrhohalf : rho ≤ 1 / 2 := by
    rw [hrhodef]
    have hle : Real.exp (-(u ^ 2)) ≤ Real.exp (-1) :=
      Real.exp_le_exp.2 (by linarith)
    refine hle.trans ?_
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
    linarith [Real.exp_one_gt_d9]
  have hterms : ∀ n ∈ Finset.range (m - q + 1),
      Real.exp (-(u ^ 2 * ((m : ℝ) - (n : ℝ)))) = rho ^ (m - n) := by
    intro n hn
    have hnle : n ≤ m := by
      have := Finset.mem_range.1 hn
      omega
    rw [hrhodef, ← Real.exp_nat_mul]
    congr 1
    rw [Nat.cast_sub hnle]
    ring
  rw [Finset.sum_congr rfl hterms]
  refine (sum_geom_reverse_le hrho0 hrhohalf hqm).trans (le_of_eq ?_)
  rw [hrhodef, ← Real.exp_nat_mul]
  congr 2
  ring

/-! ## The window-scale input -/

/-- The printed arbitrary-`s` error window coefficient
`C s^{-7/2} δ |log δ|^{1/2}` of `e.cutoff.regularity.error.average`. -/
noncomputable def errorWindowScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Cw s : ℝ) : ℝ :=
  Cw * s ^ (-7 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta|

theorem errorWindowScale_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {Cw s : ℝ}
    (hCw : 0 < Cw) (hs : 0 < s) : 0 < errorWindowScale M Cw s := by
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  have hroot : 0 < Real.sqrt |Real.log M.delta| :=
    Real.sqrt_pos.mpr (abs_pos.mpr hlogNeg.ne)
  unfold errorWindowScale
  exact mul_pos (mul_pos (mul_pos hCw (Real.rpow_pos_of_pos hs _))
    M.shellPrefix.delta_pos) hroot

/-- **The one missing input.**  The arbitrary-`s` analogue of the landed
fixed-scale `Section6Stopping.accumulatedErrorWindow_bounds`: both the
retained mean and the Gamma-two fluctuation scale of the parameterized
accumulated-error window are controlled by the printed coefficient
`C s^{-7/2} δ |log δ|^{1/2}`, once `s` is above the cutoff-ladder budget.

This is stated exactly as the landed fixed-scale lemma is stated — for an
arbitrary positive row constant, with the window evaluated at the
corresponding response Gamma scale — so discharging it is a direct
re-derivation of `accumulatedErrorWindow_bounds` at general `s`.  It is the
only step of conjunct (3) not proved in this directory. -/
def CutoffParameterizedErrorWindowInput (d : ℕ) [NeZero d] : Prop :=
  ∀ Crow : ℝ, 0 < Crow →
    ∃ Kw Cw : ℝ, 0 < Kw ∧ 0 < Cw ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ), 0 < s → s ≤ 1 →
        Kw * M.delta ^ 2 * |Real.log M.delta| ≤ s →
        ∀ n m : ℕ, n ≤ m →
          cutoffParameterizedAccumulatedErrorWindowMeanBound M s
              (Real.exp 1 *
                cutoffParameterizedResponseGammaScale M Crow s) n m ≤
            ((m + 1 - n : ℕ) : ℝ) * errorWindowScale M Cw s ∧
          cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s
              (Real.exp 1 *
                cutoffParameterizedResponseGammaScale M Crow s) n m
              (sharpFieldLowWindowScale M s) ≤
            errorWindowScale M Cw s * Real.sqrt ((m + 1 - n : ℕ) : ℝ)

/-! ## The one-centre tail -/

/-- Arbitrary-`s` finite-cutoff one-centre sub-Gaussian tail, before any
numerical absorption.  Mirrors
`Section6Cutoff.measureReal_cutoffAccumulatedError_oneCenter_le_exp`. -/
theorem measureReal_cutoffParameterizedAccumulatedError_oneCenter_le_exp
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {A threshold t : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A)
    (ht : 1 ≤ t)
    (hthreshold : cutoffParameterizedAccumulatedErrorWindowMeanBound M s A n m +
      cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s A n m
          (sharpFieldLowWindowScale M s) * t ≤
        threshold) :
    M.P.toMeasure.real {omega | threshold <
        ∑ k ∈ Finset.Icc n m,
          accumulatedError M (some L) k z s omega} ≤
      Real.exp (-(t ^ (2 : ℝ))) := by
  have hbig := isBigO_cutoffParameterizedAccumulatedErrorWindowFluctuation_sharp
    M L hs hs1 z hnm hA hrow
  have htail := (IndependentSums.isBigO_gammaSigma_iff.mp hbig) ht
  have hae : {omega | threshold <
      ∑ k ∈ Finset.Icc n m,
        accumulatedError M (some L) k z s omega} ≤ᵐ[M.P.toMeasure]
      IndependentSums.absTailEvent
        (cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m)
        (cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s A n m
          (sharpFieldLowWindowScale M s) *
          t) := by
    filter_upwards
      [ae_sum_cutoffParameterizedAccumulatedError_le_mean_add_fluctuation
        M L hs hs1 z hnm hA hrow] with omega hupper
    intro homega
    change threshold < ∑ k ∈ Finset.Icc n m,
      accumulatedError M (some L) k z s omega at homega
    unfold IndependentSums.absTailEvent IndependentSums.upperTailEvent
    dsimp only [Set.mem_setOf_eq]
    have hfluct :
        cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen M s A n m
          (sharpFieldLowWindowScale M s) *
            t <
          cutoffParameterizedAccumulatedErrorWindowFluctuation M L s z n m
            omega := by
      linarith
    exact hfluct.trans_le (le_abs_self _)
  have hmeasure := MeasureTheory.measure_mono_ae hae
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hmeasure
  exact hreal.trans htail

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
