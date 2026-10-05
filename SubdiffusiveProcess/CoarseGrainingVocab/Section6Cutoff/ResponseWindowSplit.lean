module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseWindow

@[expose] public section

/-!
# Finite-cutoff response-window split

This file interchanges the scale triangle in the cutoff response convolution,
separates rows born before the active window, and proves the Gamma-two bound
for that geometrically decaying low part.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- The `j`th finite-cutoff row after interchanging the `k/j` triangle. -/
noncomputable def cutoffAccumulatedResponseColumn {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m j : ℕ) : Sample d → ℝ :=
  fun omega => ∑ k ∈ (Finset.Icc n m).filter (fun k => j ≤ k),
    (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
      cutoffHolderResponseRow M L j omega

theorem cutoffAccumulatedResponseColumn_eq_weight_mul
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m j : ℕ)
    (omega : Sample d) :
    cutoffAccumulatedResponseColumn M L n m j omega =
      accumulatedResponseColumnWeight n m j *
        cutoffHolderResponseRow M L j omega := by
  unfold cutoffAccumulatedResponseColumn accumulatedResponseColumnWeight
  rw [Finset.sum_mul]

noncomputable def cutoffAccumulatedResponseLowWindow {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ) : Sample d → ℝ :=
  fun omega => ∑ j ∈ Finset.range n,
    cutoffAccumulatedResponseColumn M L n m j omega

noncomputable def cutoffAccumulatedResponseActiveWindow
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ) : Sample d → ℝ :=
  fun omega => ∑ j ∈ Finset.Icc n m,
    cutoffAccumulatedResponseColumn M L n m j omega

theorem cutoffAccumulatedResponseActiveWindow_le_rows
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ)
    (omega : Sample d) :
    cutoffAccumulatedResponseActiveWindow M L n m omega ≤
      (8 / holderStoppingS) *
        ∑ j ∈ Finset.Icc n m, cutoffHolderResponseRow M L j omega := by
  unfold cutoffAccumulatedResponseActiveWindow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _hj
  rw [cutoffAccumulatedResponseColumn_eq_weight_mul]
  exact mul_le_mul_of_nonneg_right
    (accumulatedResponseColumnWeight_le n m j)
    (cutoffHolderResponseRow_nonneg M L j omega)

theorem cutoffAccumulatedResponseLowWindow_le_decay_rows
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n m : ℕ)
    (omega : Sample d) :
    cutoffAccumulatedResponseLowWindow M L n m omega ≤
      (8 / holderStoppingS) * ∑ j ∈ Finset.range n,
        (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) *
          cutoffHolderResponseRow M L j omega := by
  unfold cutoffAccumulatedResponseLowWindow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [cutoffAccumulatedResponseColumn_eq_weight_mul,
    accumulatedResponseColumnWeight_eq_low_decay
      (Finset.mem_range.mp hj).le]
  have hw := accumulatedResponseColumnWeight_le n m n
  have hdecay : 0 ≤
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hrow := cutoffHolderResponseRow_nonneg M L j omega
  calc
    _ ≤ ((3 : ℝ) ^
          (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) *
          (8 / holderStoppingS)) * cutoffHolderResponseRow M L j omega := by
      gcongr
    _ = (8 / holderStoppingS) *
        ((3 : ℝ) ^
          (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) *
          cutoffHolderResponseRow M L j omega) := by ring

/-- The low finite-cutoff rows with their retained geometric decay. -/
noncomputable def cutoffAccumulatedResponseLowRows
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) : Sample d → ℝ :=
  fun omega => ∑ j ∈ Finset.range n,
    (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) *
      cutoffHolderResponseRow M L j omega

theorem measurable_cutoffAccumulatedResponseLowRows
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) :
    Measurable (cutoffAccumulatedResponseLowRows M L n) := by
  unfold cutoffAccumulatedResponseLowRows
  apply Finset.measurable_sum
  intro j _hj
  exact measurable_const.mul (measurable_cutoffHolderResponseRow M L j)

theorem isBigO_cutoffAccumulatedResponseLowRows
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffHolderResponseRow M L j) A) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (cutoffAccumulatedResponseLowRows M L n)
      (Ch04.gammaTriangleConst 2 * ((8 / holderStoppingS) * A)) := by
  by_cases hn : n = 0
  · subst n
    have hzero := (hrow 0).const_mul (c := 0) (by norm_num)
    have hzero' : IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2)
        (fun _ : Sample d => (0 : ℝ)) 0 := by
      simpa [IndependentSums.IsBigO] using! hzero
    have hfun : cutoffAccumulatedResponseLowRows M L 0 =
        (fun _ : Sample d => (0 : ℝ)) := by
      funext omega
      simp [cutoffAccumulatedResponseLowRows]
    rw [hfun]
    exact hzero'.mono_scale (by
      have htri := IndependentSums.gammaTriangleConst_pos (σ := 2)
      have hs : 0 < holderStoppingS := holderStoppingS_pos
      positivity)
  · let X : ℕ → Sample d → ℝ := fun j omega =>
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) *
        cutoffHolderResponseRow M L j omega
    let a : ℕ → ℝ := fun j =>
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) * A
    have hsum := Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := M.P.toMeasure) (Finset.range n) (X := X) (a := a) (σ := 2)
      (by norm_num) (Finset.nonempty_range_iff.mpr hn)
      (fun j _ => mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hA)
      (fun j _ => by
        let w : ℝ := (3 : ℝ) ^
          (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ)))
        have hw : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
        have hscaled := (hrow j).const_mul (c := w) hw
        simpa only [X, a, w, IndependentSums.IsBigO,
          abs_of_nonneg
            (mul_nonneg hw (cutoffHolderResponseRow_nonneg M L j _))]
          using! hscaled)
      (fun j _ =>
        measurable_const.mul (measurable_cutoffHolderResponseRow M L j))
    have hsum' : IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2)
        (cutoffAccumulatedResponseLowRows M L n)
        (Ch04.gammaTriangleConst 2 * ∑ j ∈ Finset.range n, a j) := by
      simpa only [cutoffAccumulatedResponseLowRows, X] using! hsum
    refine hsum'.mono_scale ?_
    have hweights := sum_responseQuarterWeight_range_le n
    have hnonneg : 0 ≤ Ch04.gammaTriangleConst 2 :=
      (IndependentSums.gammaTriangleConst_pos (σ := 2)).le
    unfold a
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hweights hA.le) hnonneg

/-- Exact `j<n`/`n≤j≤m` split of the finite-cutoff response convolution. -/
theorem cutoffAccumulatedResponseWindowConvolution_eq_low_add_active
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {n m : ℕ} (hnm : n ≤ m) (omega : Sample d) :
    cutoffAccumulatedResponseWindowConvolution M L n m omega =
      cutoffAccumulatedResponseLowWindow M L n m omega +
        cutoffAccumulatedResponseActiveWindow M L n m omega := by
  unfold cutoffAccumulatedResponseWindowConvolution
    cutoffAccumulatedResponseLowWindow cutoffAccumulatedResponseActiveWindow
    cutoffAccumulatedResponseColumn
  rw [sum_Icc_sum_range_eq_sum_range_sum_filter]
  rw [show Finset.Icc n m = Finset.Ico n (m + 1) by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega]
  exact (Finset.sum_range_add_sum_Ico (f := fun j =>
    ∑ k ∈ (Finset.Icc n m).filter (fun k => j ≤ k),
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
        cutoffHolderResponseRow M L j omega) (by omega : n ≤ m + 1)).symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
