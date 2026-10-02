import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoTopLeg
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowOneInstantiation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.StoppedRatio

/-!
# The stopped tail-average ratios at an arbitrary pair of scales

`RowTwoRatioRow` exports the two ratio directions at the scales row 1 uses, and
`RowTwoTopLeg.tail_pairing_at_top` pairs them at `n + 2` against `top + 4`.
Row 2's Step-6 budget is read at the **selected** gate scale, not at `n + 2`, so
the pairing is needed at a free scale `q`.

Everything here is the same one-line consequence of
`stopped_tailAverage_ratio_bounds_exp_cut`: the stopped controls at
the base scale `n` at a scale-`n` grid centre bound *both* the local-over-domain
and the domain-over-local tail-average ratios by
`exp (ratioRate_cut d * lambda * (m - n))`, uniformly in the read-out scale
`q ∈ [n, m]`.  The pairing of two such bounds at two (possibly different)
centres is then `RowTwoRatioRow.sqrt_tailAverage_pairing`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The exponential rate carried by every stopped ratio of the row-2 chain. -/
def rowTwoRatioBound_cut (d : ℕ) (C1 alpha : ℝ) (m n : ℕ) : ℝ :=
  Real.exp (ratioRate_cut d * Section6Stopping.holderStoppingLambda C1 alpha *
    ((m : ℝ) - (n : ℝ)))

theorem rowTwoRatioBound_nonneg_cut (d : ℕ) (C1 alpha : ℝ) (m n : ℕ) :
    0 ≤ rowTwoRatioBound_cut d C1 alpha m n := (Real.exp_nonneg _)

theorem one_le_rowTwoRatioBound_cut (d : ℕ) {C1 alpha : ℝ} {m n : ℕ}
    (hlam0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hnm : n ≤ m) : 1 ≤ rowTwoRatioBound_cut d C1 alpha m n := by
  rw [rowTwoRatioBound_cut]
  refine Real.one_le_exp ?_
  have hgap : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith
  have := ratioRate_nonneg_cut d
  positivity

/-- **Both stopped ratio directions at a free read-out scale `q`.** -/
theorem stoppedRatio_bounds_at_cut (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (C1 C2 alpha : ℝ) (step m n q L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m)
    (hstop : (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hnm : n < m) (hnq : n ≤ q) (hqm : q ≤ m)     (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha) :
    tailAverage M L q omega (translatedCube d (q : ℕ) z) /
          tailCoefficientCubeAverage M L m omega ≤
        rowTwoRatioBound_cut d C1 alpha m n ∧
      tailCoefficientCubeAverage M L m omega /
          tailAverage M L q omega (translatedCube d (q : ℕ) z) ≤
        rowTwoRatioBound_cut d C1 alpha m n := by
  obtain ⟨hcY, hc0⟩ := stoppedControls_pair_cut M C1 C2 alpha step m n omega hstop
    z hzgrid hz
  have hs2 : Section6Stopping.holderStoppingS ≤ 1 / 2 := by
    rw [Section6Stopping.holderStoppingS]; norm_num
  have hraw := stopped_tailAverage_ratio_bounds_exp_cut
    (M := M) (L := L) (n := n) (q := q) (m := m)
    hnm hnq hqm
    (Section6Stopping.holderStoppingEpsilon C2 alpha)
    Section6Stopping.holderStoppingS
    (Section6Stopping.holderStoppingLambda C1 alpha)
    hepsilon hs2 hlambda0 hlambda1 hdelta omega z hz hcY.1 hc0.1 hcY.2 hc0.2
  dsimp only at hraw
  exact hraw

/-- Strict positivity of the local tail average at a translated window. -/
theorem tailAverage_translatedCube_pos_cut (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L q : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d) :
    0 < tailAverage M L q omega (translatedCube d (q : ℕ) z) := by
  rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
  exact tailCoefficientCubeAverage_pos M L q (translatePotentialSample z omega)

/-- **The pairing at two free scales and two grid centres.**  Both centres carry
the stopped controls at the base scale `n`, so the quotient of the two square
roots is bounded by the single exponential rate. -/
theorem sqrt_tailAverage_pairing_at_cut (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (C1 C2 alpha : ℝ) (step m n p r L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z z' : Vec d)
    (hzgrid : OnTriadicGrid n z) (hz : z ∈ cube d m)
    (hz'grid : OnTriadicGrid n z') (hz' : z' ∈ cube d m)
    (hstop : (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (n : ℤ))
    (hnm : n < m) (hnp : n ≤ p) (hpm : p ≤ m) (hnr : n ≤ r) (hrm : r ≤ m)
        (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha) :
    Real.sqrt (tailAverage M L p omega (translatedCube d (p : ℕ) z)) *
        (Real.sqrt (tailAverage M L r omega
          (translatedCube d (r : ℕ) z')))⁻¹ ≤
      rowTwoRatioBound_cut d C1 alpha m n := by
  have hlow := stoppedRatio_bounds_at_cut M C1 C2 alpha step m n p L omega z hzgrid hz
    hstop hnm hnp hpm hlambda0 hlambda1 hepsilon hdelta
  have hhigh := stoppedRatio_bounds_at_cut M C1 C2 alpha step m n r L omega z' hz'grid
    hz' hstop hnm hnr hrm hlambda0 hlambda1 hepsilon hdelta
  exact sqrt_tailAverage_pairing
    (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _)
    (tailAverage_translatedCube_pos_cut M L r omega z')
    (tailCoefficientCubeAverage_pos M L m omega)
    (rowTwoRatioBound_nonneg_cut d C1 alpha m n) hlow.1 hhigh.2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
