module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ResponseRow

@[expose] public section

/-!
# Parameterized finite-cutoff response row

The fixed Holder stopping row is not sufficient for the general-`s` clauses
of `p.cutoff.regularity.good.scales`.  This module records the corresponding
row at an arbitrary positive `s`.  Its deterministic cap is `4 / s`, the
geometric mass of the response weights, and every literal response atom in
`accumulatedError M (some L) ... s` is dominated by this row.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- The finite-cutoff annular score with decay exponent `s / 2`. -/
noncomputable def cutoffParameterizedResponseScore {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ) (j : ℕ) :
    Sample d → ℝ :=
  fun omega ↦
    (cutoffLocalResponseScore M L (s / 2) 1 1 j omega).toReal

/-- The capped square-root response row used at a general stopping exponent. -/
noncomputable def cutoffParameterizedResponseRow {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ) (j : ℕ) :
    Sample d → ℝ :=
  fun omega ↦ Real.sqrt
    (min (cutoffParameterizedResponseScore M L s j omega) (4 / s))

theorem cutoffParameterizedResponseRow_nonneg {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ) (j : ℕ)
    (omega : Sample d) :
    0 ≤ cutoffParameterizedResponseRow M L s j omega :=
  Real.sqrt_nonneg _

theorem cutoffParameterizedResponseRow_le_sqrt_cap {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ)
    (j : ℕ) (omega : Sample d) :
    cutoffParameterizedResponseRow M L s j omega ≤ Real.sqrt (4 / s) := by
  unfold cutoffParameterizedResponseRow
  exact Real.sqrt_le_sqrt (min_le_right _ _)

theorem measurable_cutoffParameterizedResponseScore {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ) (j : ℕ) :
    Measurable (cutoffParameterizedResponseScore M L s j) := by
  unfold cutoffParameterizedResponseScore
  exact ENNReal.measurable_toReal.comp
    ((measurable_cutoffLocalResponseScore M L (s / 2) 1 1 j).mono
      (aCutoffPotentialLocalSigma_le_borel _) le_rfl)

theorem measurable_cutoffParameterizedResponseRow {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ) (j : ℕ) :
    Measurable (cutoffParameterizedResponseRow M L s j) := by
  unfold cutoffParameterizedResponseRow
  exact Real.continuous_sqrt.measurable.comp
    ((measurable_cutoffParameterizedResponseScore M L s j).min measurable_const)

/-- Truncated weighted annular mass at the general response exponent. -/
noncomputable def cutoffParameterizedResponseTruncatedMass
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ) (j : ℕ) :
    Sample d → ℝ≥0∞ :=
  fun omega ↦ ∑ n ∈ Finset.range (j - 1),
    ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) *
      min (cutoffLocalResponseScaleAtom M L j n omega) 1

theorem measurable_cutoffParameterizedResponseTruncatedMass
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ) (j : ℕ) :
    Measurable (cutoffParameterizedResponseTruncatedMass M L s j) := by
  unfold cutoffParameterizedResponseTruncatedMass
  apply Finset.measurable_sum
  intro n _hn
  exact measurable_const.mul
    (((measurable_cutoffLocalResponseScaleAtom M L j n).mono
      (aCutoffPotentialLocalSigma_le_borel _) le_rfl).min measurable_const)

theorem cutoffParameterizedResponseTruncatedMass_ne_top
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ) (j : ℕ)
    (omega : Sample d) :
    cutoffParameterizedResponseTruncatedMass M L s j omega ≠ ∞ := by
  unfold cutoffParameterizedResponseTruncatedMass
  rw [ENNReal.sum_ne_top]
  intro n _hn
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_of_lt ((min_le_right _ _).trans_lt ENNReal.one_lt_top))

theorem cutoffParameterizedResponseTruncatedMass_le_localScore
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (j : ℕ) (omega : Sample d) :
    cutoffParameterizedResponseTruncatedMass M L s j omega ≤
      cutoffLocalResponseScore M L (s / 2) 1 1 j omega := by
  let S : ℝ≥0∞ := ∑ n ∈ Finset.range (j - 1),
    ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) *
      cutoffLocalResponseScaleAtom M L j n omega
  have hmass : cutoffParameterizedResponseTruncatedMass M L s j omega ≤ S := by
    unfold cutoffParameterizedResponseTruncatedMass S
    apply Finset.sum_le_sum
    intro n _hn
    exact mul_le_mul_right (min_le_left _ _) _
  have hsHalf : 0 < s / 2 := by positivity
  have hsHalfTwo : s / 2 ≤ 2 := by linarith
  have hcoefReal : 1 ≤ 2 * (s / 2)⁻¹ := by
    have hinv0 : 0 ≤ (s / 2)⁻¹ := inv_nonneg.mpr hsHalf.le
    have hmul := mul_le_mul_of_nonneg_right hsHalfTwo hinv0
    rw [mul_inv_cancel₀ hsHalf.ne'] at hmul
    exact hmul
  have hcoef : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * (s / 2)⁻¹) := by
    rw [ENNReal.one_le_ofReal]
    exact hcoefReal
  calc
    cutoffParameterizedResponseTruncatedMass M L s j omega ≤ S := hmass
    _ = 1 * S := by rw [one_mul]
    _ ≤ ENNReal.ofReal (2 * (s / 2)⁻¹) * S := by gcongr
    _ = cutoffLocalResponseScore M L (s / 2) 1 1 j omega := by
      unfold cutoffLocalResponseScore S
      norm_num

theorem cutoffParameterizedResponseTruncatedMass_toReal_le_score
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (j : ℕ) (omega : Sample d) :
    (cutoffParameterizedResponseTruncatedMass M L s j omega).toReal ≤
      cutoffParameterizedResponseScore M L s j omega := by
  unfold cutoffParameterizedResponseScore
  exact ENNReal.toReal_mono
    (cutoffLocalResponseScore_ne_top M L (s / 2) 1 1 j omega)
    (cutoffParameterizedResponseTruncatedMass_le_localScore
      M L hs hs1 j omega)

theorem sum_cutoffParameterizedResponseWeight_le
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (j : ℕ) :
    ∑ n ∈ Finset.range (j - 1),
        (3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ))) ≤ 4 / s := by
  have hsummable := SubdiffusiveProcess.Concentration.summable_wt_half hs hs1 (j : ℤ)
  have hfinite := hsummable.sum_le_tsum
    (s := (Finset.range (j - 1)).map ⟨Int.ofNat, Int.ofNat_injective⟩)
    (fun q _ ↦ SubdiffusiveProcess.Concentration.wt_nonneg (s / 2) (j : ℤ) q)
  have hsum :
      (∑ n ∈ Finset.range (j - 1),
        (3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) ≤
        ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (s / 2) (j : ℤ) q := by
    rw [Finset.sum_map] at hfinite
    apply (Finset.sum_le_sum fun n hn ↦ ?_).trans hfinite
    have hnj : n ≤ j := by
      have : n < j - 1 := Finset.mem_range.mp hn
      omega
    simp only [Function.Embedding.coeFn_mk, SubdiffusiveProcess.Concentration.wt,
      SubdiffusiveProcess.Concentration.idist_eq]
    have habs : ((j : ℤ) - Int.ofNat n).natAbs = j - n := by
      simpa only [Int.ofNat_eq_natCast] using
        Int.natAbs_natCast_sub_natCast_of_ge hnj
    rw [habs, Nat.cast_sub hnj]
    apply le_of_eq
    congr 2
    ring
  exact hsum.trans (SubdiffusiveProcess.Concentration.sum_wt_half_le hs hs1 (j : ℤ))

theorem cutoffParameterizedResponseTruncatedMass_toReal_le_cap
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (j : ℕ) (omega : Sample d) :
    (cutoffParameterizedResponseTruncatedMass M L s j omega).toReal ≤ 4 / s := by
  have hmass : cutoffParameterizedResponseTruncatedMass M L s j omega ≤
      ENNReal.ofReal (4 / s) := by
    unfold cutoffParameterizedResponseTruncatedMass
    calc
      ∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) *
            min (cutoffLocalResponseScaleAtom M L j n omega) 1 ≤
          ∑ n ∈ Finset.range (j - 1),
            ENNReal.ofReal
              ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) := by
        apply Finset.sum_le_sum
        intro n _hn
        simpa only [mul_one] using mul_le_mul_right
          (min_le_right (cutoffLocalResponseScaleAtom M L j n omega) 1)
          (ENNReal.ofReal
            ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))))
      _ = ENNReal.ofReal
          (∑ n ∈ Finset.range (j - 1),
            (3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro n _hn
        positivity
      _ ≤ ENNReal.ofReal (4 / s) := ENNReal.ofReal_le_ofReal
        (sum_cutoffParameterizedResponseWeight_le hs hs1 j)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  have hcap0 : 0 ≤ 4 / s := div_nonneg (by norm_num) hs.le
  rw [ENNReal.toReal_ofReal hcap0] at hreal
  exact hreal

theorem sqrt_cutoffParameterizedResponseTruncatedMass_le_row
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (j : ℕ) (omega : Sample d) :
    Real.sqrt (cutoffParameterizedResponseTruncatedMass M L s j omega).toReal ≤
      cutoffParameterizedResponseRow M L s j omega := by
  unfold cutoffParameterizedResponseRow
  apply Real.sqrt_le_sqrt
  exact le_min
    (cutoffParameterizedResponseTruncatedMass_toReal_le_score
      M L hs hs1 j omega)
    (cutoffParameterizedResponseTruncatedMass_toReal_le_cap
      M L hs hs1 j omega)

/-- Every response atom in the general-`s` accumulated error is a summand of
the parameterized capped row. -/
theorem cutoffParameterizedResponseAtom_le_row
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) {j l : ℕ} (hlj : l + 2 ≤ j)
    (omega : Sample d) :
    (3 : ℝ) ^ (-(s / 4) * ((j : ℝ) - (l : ℝ))) *
        Real.sqrt (min (cutoffLocalResponseScaleAtom M L j l omega).toReal 1) ≤
      cutoffParameterizedResponseRow M L s j omega := by
  let T : ℝ≥0∞ :=
    ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (l : ℝ)))) *
      min (cutoffLocalResponseScaleAtom M L j l omega) 1
  have hlmem : l ∈ Finset.range (j - 1) := by
    rw [Finset.mem_range]
    omega
  have hT : T ≤ cutoffParameterizedResponseTruncatedMass M L s j omega := by
    unfold T cutoffParameterizedResponseTruncatedMass
    exact Finset.single_le_sum
      (f := fun n : ℕ => ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) *
        min (cutoffLocalResponseScaleAtom M L j n omega) 1)
      (fun _ _ => zero_le) hlmem
  have hreal : T.toReal ≤
      (cutoffParameterizedResponseTruncatedMass M L s j omega).toReal :=
    ENNReal.toReal_mono
      (cutoffParameterizedResponseTruncatedMass_ne_top M L s j omega) hT
  have hsqrt := Real.sqrt_le_sqrt hreal
  have hatomTop : cutoffLocalResponseScaleAtom M L j l omega ≠ ∞ :=
    cutoffLocalResponseScaleAtom_ne_top M L j l omega
  have hweight : 0 ≤
      (3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (l : ℝ))) := by positivity
  have hsqrtWeight : Real.sqrt
        ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (l : ℝ)))) =
      (3 : ℝ) ^ (-(s / 4) * ((j : ℝ) - (l : ℝ))) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hTreal : Real.sqrt T.toReal =
      (3 : ℝ) ^ (-(s / 4) * ((j : ℝ) - (l : ℝ))) *
        Real.sqrt (min (cutoffLocalResponseScaleAtom M L j l omega).toReal 1) := by
    change Real.sqrt
      ((ENNReal.ofReal
          ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (l : ℝ)))) *
        min (cutoffLocalResponseScaleAtom M L j l omega) 1).toReal) = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hweight,
      ENNReal.toReal_min hatomTop (by norm_num), ENNReal.toReal_one,
      Real.sqrt_mul hweight, hsqrtWeight]
  rw [← hTreal]
  exact hsqrt.trans
    (sqrt_cutoffParameterizedResponseTruncatedMass_le_row
      M L hs hs1 j omega)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
