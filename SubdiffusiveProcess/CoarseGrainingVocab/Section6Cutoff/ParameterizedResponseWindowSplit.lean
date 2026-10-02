import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseGamma
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseWindow

/-!
# Split of the parameterized cutoff response window

This interchanges the finite `k/j` triangle, separates rows born below the
active window, and retains their geometric decay.  All constants keep the
general exponent `s` visible.
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
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

noncomputable def cutoffParameterizedAccumulatedResponseColumn
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (n m j : ℕ) : Sample d → ℝ :=
  fun omega => ∑ k ∈ (Finset.Icc n m).filter (fun k => j ≤ k),
    (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
      cutoffParameterizedResponseRow M L s j omega

noncomputable def cutoffParameterizedAccumulatedResponseColumnWeight
    (s : ℝ) (n m j : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc n m).filter (fun k => j ≤ k),
    (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ)))

theorem cutoffParameterizedAccumulatedResponseColumn_eq_weight_mul
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (n m j : ℕ) (omega : Sample d) :
    cutoffParameterizedAccumulatedResponseColumn M L s n m j omega =
      cutoffParameterizedAccumulatedResponseColumnWeight s n m j *
        cutoffParameterizedResponseRow M L s j omega := by
  unfold cutoffParameterizedAccumulatedResponseColumn
    cutoffParameterizedAccumulatedResponseColumnWeight
  rw [Finset.sum_mul]

theorem cutoffParameterizedAccumulatedResponseColumnWeight_le
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (n m j : ℕ) :
    cutoffParameterizedAccumulatedResponseColumnWeight s n m j ≤ 8 / s := by
  let S : Finset ℕ := (Finset.Icc n m).filter (fun k => j ≤ k)
  have hquarter : s / 2 / 2 = s / 4 := by ring
  have hsHalf : 0 < s / 2 := by positivity
  have hsHalfOne : s / 2 ≤ 1 := by linarith
  have hsummable : Summable (fun q : ℤ =>
      SubdiffusiveProcess.Concentration.wt (s / 4) (j : ℤ) q) := by
    simpa only [hquarter] using SubdiffusiveProcess.Concentration.summable_wt_half
      hsHalf hsHalfOne (j : ℤ)
  have hfinite : (∑ q ∈ S.map ⟨Int.ofNat, Int.ofNat_injective⟩,
      SubdiffusiveProcess.Concentration.wt (s / 4) (j : ℤ) q) ≤
      ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (s / 4) (j : ℤ) q :=
    hsummable.sum_le_tsum
      (s := S.map ⟨Int.ofNat, Int.ofNat_injective⟩)
      (fun q _ => SubdiffusiveProcess.Concentration.wt_nonneg (s / 4) (j : ℤ) q)
  have hsum : cutoffParameterizedAccumulatedResponseColumnWeight s n m j ≤
      ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (s / 4) (j : ℤ) q := by
    unfold cutoffParameterizedAccumulatedResponseColumnWeight
    rw [Finset.sum_map] at hfinite
    apply (Finset.sum_le_sum fun k hk => ?_).trans hfinite
    obtain ⟨_hk, hjk⟩ := Finset.mem_filter.mp hk
    simp only [Function.Embedding.coeFn_mk, SubdiffusiveProcess.Concentration.wt,
      SubdiffusiveProcess.Concentration.idist_eq]
    have habs : ((j : ℤ) - Int.ofNat k).natAbs = k - j := by
      rw [show (j : ℤ) - Int.ofNat k = -(Int.ofNat k - (j : ℤ)) by ring,
        Int.natAbs_neg]
      simpa only [Int.ofNat_eq_natCast] using
        Int.natAbs_natCast_sub_natCast_of_ge hjk
    rw [habs, Nat.cast_sub hjk]
    apply le_of_eq
    congr 2
    ring
  calc
    _ ≤ ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (s / 4) (j : ℤ) q := hsum
    _ ≤ 4 / (s / 2) := by
      simpa only [hquarter] using SubdiffusiveProcess.Concentration.sum_wt_half_le
        hsHalf hsHalfOne (j : ℤ)
    _ = 8 / s := by ring

theorem cutoffParameterizedAccumulatedResponseColumnWeight_eq_low_decay
    {s : ℝ} {n m j : ℕ} (hj : j ≤ n) :
    cutoffParameterizedAccumulatedResponseColumnWeight s n m j =
      (3 : ℝ) ^ (-(s / 4) * ((n : ℝ) - (j : ℝ))) *
        cutoffParameterizedAccumulatedResponseColumnWeight s n m n := by
  unfold cutoffParameterizedAccumulatedResponseColumnWeight
  have hfilter : (Finset.Icc n m).filter (fun k => j ≤ k) =
      (Finset.Icc n m).filter (fun k => n ≤ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

theorem sum_cutoffParameterizedResponseQuarterWeight_range_le
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (n : ℕ) :
    (∑ j ∈ Finset.range n,
      (3 : ℝ) ^ (-(s / 4) * ((n : ℝ) - (j : ℝ)))) ≤ 8 / s := by
  have hquarter : s / 2 / 2 = s / 4 := by ring
  have hsHalf : 0 < s / 2 := by positivity
  have hsHalfOne : s / 2 ≤ 1 := by linarith
  have hsummable : Summable (fun q : ℤ =>
      SubdiffusiveProcess.Concentration.wt (s / 4) (n : ℤ) q) := by
    simpa only [hquarter] using SubdiffusiveProcess.Concentration.summable_wt_half
      hsHalf hsHalfOne (n : ℤ)
  have hfinite := hsummable.sum_le_tsum
    (s := (Finset.range n).map ⟨Int.ofNat, Int.ofNat_injective⟩)
    (fun q _ => SubdiffusiveProcess.Concentration.wt_nonneg (s / 4) (n : ℤ) q)
  have hsum : (∑ j ∈ Finset.range n,
      (3 : ℝ) ^ (-(s / 4) * ((n : ℝ) - (j : ℝ)))) ≤
      ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (s / 4) (n : ℤ) q := by
    rw [Finset.sum_map] at hfinite
    apply (Finset.sum_le_sum fun j hj => ?_).trans hfinite
    have hjn := (Finset.mem_range.mp hj).le
    simp only [Function.Embedding.coeFn_mk, SubdiffusiveProcess.Concentration.wt,
      SubdiffusiveProcess.Concentration.idist_eq]
    have habs : ((n : ℤ) - Int.ofNat j).natAbs = n - j := by
      simpa only [Int.ofNat_eq_natCast] using
        Int.natAbs_natCast_sub_natCast_of_ge hjn
    rw [habs, Nat.cast_sub hjn]
    apply le_of_eq
    congr 2
    ring
  calc
    _ ≤ ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (s / 4) (n : ℤ) q := hsum
    _ ≤ 4 / (s / 2) := by
      simpa only [hquarter] using SubdiffusiveProcess.Concentration.sum_wt_half_le
        hsHalf hsHalfOne (n : ℤ)
    _ = 8 / s := by ring

noncomputable def cutoffParameterizedAccumulatedResponseLowWindow
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (n m : ℕ) : Sample d → ℝ :=
  fun omega => ∑ j ∈ Finset.range n,
    cutoffParameterizedAccumulatedResponseColumn M L s n m j omega

noncomputable def cutoffParameterizedAccumulatedResponseActiveWindow
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (n m : ℕ) : Sample d → ℝ :=
  fun omega => ∑ j ∈ Finset.Icc n m,
    cutoffParameterizedAccumulatedResponseColumn M L s n m j omega

noncomputable def cutoffParameterizedAccumulatedResponseLowRows
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    (n : ℕ) : Sample d → ℝ :=
  fun omega => ∑ j ∈ Finset.range n,
    (3 : ℝ) ^ (-(s / 4) * ((n : ℝ) - (j : ℝ))) *
      cutoffParameterizedResponseRow M L s j omega

theorem cutoffParameterizedAccumulatedResponseActiveWindow_le_rows
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (n m : ℕ) (omega : Sample d) :
    cutoffParameterizedAccumulatedResponseActiveWindow M L s n m omega ≤
      (8 / s) * ∑ j ∈ Finset.Icc n m,
        cutoffParameterizedResponseRow M L s j omega := by
  unfold cutoffParameterizedAccumulatedResponseActiveWindow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _hj
  rw [cutoffParameterizedAccumulatedResponseColumn_eq_weight_mul]
  exact mul_le_mul_of_nonneg_right
    (cutoffParameterizedAccumulatedResponseColumnWeight_le hs hs1 n m j)
    (cutoffParameterizedResponseRow_nonneg M L s j omega)

theorem cutoffParameterizedAccumulatedResponseLowWindow_le_decay_rows
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (n m : ℕ) (omega : Sample d) :
    cutoffParameterizedAccumulatedResponseLowWindow M L s n m omega ≤
      (8 / s) * cutoffParameterizedAccumulatedResponseLowRows M L s n omega := by
  unfold cutoffParameterizedAccumulatedResponseLowWindow
    cutoffParameterizedAccumulatedResponseLowRows
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [cutoffParameterizedAccumulatedResponseColumn_eq_weight_mul,
    cutoffParameterizedAccumulatedResponseColumnWeight_eq_low_decay
      (Finset.mem_range.mp hj).le]
  have hw := cutoffParameterizedAccumulatedResponseColumnWeight_le hs hs1 n m n
  have hdecay : 0 ≤
      (3 : ℝ) ^ (-(s / 4) * ((n : ℝ) - (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hrow := cutoffParameterizedResponseRow_nonneg M L s j omega
  calc
    _ ≤ ((3 : ℝ) ^ (-(s / 4) * ((n : ℝ) - (j : ℝ))) *
          (8 / s)) * cutoffParameterizedResponseRow M L s j omega := by gcongr
    _ = (8 / s) * ((3 : ℝ) ^
          (-(s / 4) * ((n : ℝ) - (j : ℝ))) *
        cutoffParameterizedResponseRow M L s j omega) := by ring

theorem cutoffParameterizedAccumulatedResponseWindowConvolution_eq_low_add_active
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ)
    {n m : ℕ} (hnm : n ≤ m) (omega : Sample d) :
    cutoffParameterizedAccumulatedResponseWindowConvolution M L s n m omega =
      cutoffParameterizedAccumulatedResponseLowWindow M L s n m omega +
        cutoffParameterizedAccumulatedResponseActiveWindow M L s n m omega := by
  unfold cutoffParameterizedAccumulatedResponseWindowConvolution
    cutoffParameterizedAccumulatedResponseLowWindow
    cutoffParameterizedAccumulatedResponseActiveWindow
    cutoffParameterizedAccumulatedResponseColumn
  rw [sum_Icc_sum_range_eq_sum_range_sum_filter]
  rw [show Finset.Icc n m = Finset.Ico n (m + 1) by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega]
  exact (Finset.sum_range_add_sum_Ico (f := fun j =>
    ∑ k ∈ (Finset.Icc n m).filter (fun k => j ≤ k),
      (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
        cutoffParameterizedResponseRow M L s j omega)
    (by omega : n ≤ m + 1)).symm

theorem measurable_cutoffParameterizedAccumulatedResponseLowRows
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ) (n : ℕ) :
    Measurable (cutoffParameterizedAccumulatedResponseLowRows M L s n) := by
  unfold cutoffParameterizedAccumulatedResponseLowRows
  apply Finset.measurable_sum
  intro j _hj
  exact measurable_const.mul
    (measurable_cutoffParameterizedResponseRow M L s j)

theorem isBigO_cutoffParameterizedAccumulatedResponseLowRows
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s A : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (n : ℕ) (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j) A) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (cutoffParameterizedAccumulatedResponseLowRows M L s n)
      (Ch04.gammaTriangleConst 2 * ((8 / s) * A)) := by
  by_cases hn : n = 0
  · subst n
    have hzero := (hrow 0).const_mul (c := 0) (by norm_num)
    have hzero' : IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2) (fun _ : Sample d => (0 : ℝ)) 0 := by
      simpa [IndependentSums.IsBigO] using hzero
    have hfun : cutoffParameterizedAccumulatedResponseLowRows M L s 0 =
        (fun _ : Sample d => (0 : ℝ)) := by
      funext omega
      simp [cutoffParameterizedAccumulatedResponseLowRows]
    rw [hfun]
    exact hzero'.mono_scale (by
      have htri := IndependentSums.gammaTriangleConst_pos (σ := 2)
      positivity)
  · let X : ℕ → Sample d → ℝ := fun j omega =>
      (3 : ℝ) ^ (-(s / 4) * ((n : ℝ) - (j : ℝ))) *
        cutoffParameterizedResponseRow M L s j omega
    let a : ℕ → ℝ := fun j =>
      (3 : ℝ) ^ (-(s / 4) * ((n : ℝ) - (j : ℝ))) * A
    have hsum := Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := M.P.toMeasure) (Finset.range n) (X := X) (a := a) (σ := 2)
      (by norm_num) (Finset.nonempty_range_iff.mpr hn)
      (fun j _ => mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hA)
      (fun j _ => by
        let w : ℝ := (3 : ℝ) ^ (-(s / 4) * ((n : ℝ) - (j : ℝ)))
        have hw : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
        have hscaled := (hrow j).const_mul (c := w) hw
        simpa only [X, a, w, IndependentSums.IsBigO,
          abs_of_nonneg (mul_nonneg hw
            (cutoffParameterizedResponseRow_nonneg M L s j _))] using hscaled)
      (fun j _ => measurable_const.mul
        (measurable_cutoffParameterizedResponseRow M L s j))
    have hsum' : IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2)
        (cutoffParameterizedAccumulatedResponseLowRows M L s n)
        (Ch04.gammaTriangleConst 2 * ∑ j ∈ Finset.range n, a j) := by
      simpa only [cutoffParameterizedAccumulatedResponseLowRows, X] using hsum
    refine hsum'.mono_scale ?_
    have hweights := sum_cutoffParameterizedResponseQuarterWeight_range_le
      hs hs1 n
    have hnonneg : 0 ≤ Ch04.gammaTriangleConst 2 :=
      (IndependentSums.gammaTriangleConst_pos (σ := 2)).le
    unfold a
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hweights hA.le) hnonneg

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
