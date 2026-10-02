import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.StoppedRatio
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.CampanatoFullGate
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.CampanatoFullGate
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneJoint
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.StoppedRatio




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section

variable {L : ℕ}
attribute [local instance] Classical.propDecidable

/-- The coefficient-ratio rate of `stopped_tailAverage_ratio_bounds_exp_cut`
at the manuscript's scale `s = holderStoppingS`. -/
def ratioRate_cut (d : ℕ) : ℝ :=
  4 * (d : ℝ) + ((3 : ℝ) ^ (-(Section6Stopping.holderStoppingS / 8)))⁻¹ + 1

theorem ratioRate_nonneg_cut (d : ℕ) : 0 ≤ ratioRate_cut d := by
  unfold ratioRate_cut
  positivity

/-- The two stopped controls at a grid centre and at the origin, packaged for
`stopped_tailAverage_ratio_bounds_exp_cut`. -/
theorem stoppedControls_pair_cut {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C1 C2 alpha : ℝ) (step m ell : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hstop : (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (ell : ℤ))
    (y : Vec d) (hygrid : OnTriadicGrid ell y) (hy : y ∈ cube d m) :
    ((∑ j ∈ Finset.Icc ell m,
        accumulatedError M (some L) j y Section6Stopping.holderStoppingS omega) ≤
      Section6Stopping.holderStoppingLambda C1 alpha * ((m : ℝ) - (ell : ℝ)) ∧
      (∑ j ∈ Finset.Icc ell m,
        (1 - if omega ∈ goodEvent M (some L) j y
          (Section6Stopping.holderStoppingEpsilon C2 alpha)
          Section6Stopping.holderStoppingS then (1 : ℝ) else 0)) <
        1 + Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (ell : ℝ))) ∧
    ((∑ j ∈ Finset.Icc ell m,
        accumulatedError M (some L) j 0 Section6Stopping.holderStoppingS omega) ≤
      Section6Stopping.holderStoppingLambda C1 alpha * ((m : ℝ) - (ell : ℝ)) ∧
      (∑ j ∈ Finset.Icc ell m,
        (1 - if omega ∈ goodEvent M (some L) j 0
          (Section6Stopping.holderStoppingEpsilon C2 alpha)
          Section6Stopping.holderStoppingS then (1 : ℝ) else 0)) <
        1 + Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (ell : ℝ))) := by
  have hzero : (0 : Vec d) ∈ cube d m := Section6ExcessDecay.zero_mem_cube d (m : ℤ)
  have hzeroGrid : OnTriadicGrid ell (0 : Vec d) := fun i => ⟨0, by simp⟩
  exact ⟨Section6Stopping.measurableCutoffHolder_stopped_controls_at_parameters
      M L C1 C2 alpha step m ell omega hstop y hygrid hy,
    Section6Stopping.measurableCutoffHolder_stopped_controls_at_parameters
      M L C1 C2 alpha step m ell omega hstop 0 hzeroGrid hzero⟩

/-- The coefficient-ratio row consumed by the gated Campanato estimate, at the
stopping scale.  This is the second conjunct of
`stopped_tailAverage_ratio_bounds_exp_cut`, with the exponential of
the ratio rate as the uniform bound. -/
theorem stoppedRatio_row_cut {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C1 C2 alpha : ℝ)
    (step m ell top L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hellm : ell < m) (htop : top + 5 ≤ m)
    (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (y : Vec d) (hy : y ∈ cube d m)
    (hstop : (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (ell : ℤ))
    (hygrid : OnTriadicGrid ell y) :
    ∀ j ∈ Finset.Icc ell top,
      tailCoefficientCubeAverage M L m omega /
          tailAverage M L (j + 2) omega (translatedCube d (j + 2 : ℕ) y) ≤
        Real.exp (ratioRate_cut d *
          Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (ell : ℝ))) := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hcY, hc0⟩ := stoppedControls_pair_cut M C1 C2 alpha step m ell omega hstop
    y hygrid hy
  have hraw := stopped_tailAverage_ratio_bounds_exp_cut
    (M := M) (L := L) (n := ell) (q := j + 2) (m := m)
    hellm (by omega) (by omega)
    (Section6Stopping.holderStoppingEpsilon C2 alpha)
    Section6Stopping.holderStoppingS
    (Section6Stopping.holderStoppingLambda C1 alpha)
    hepsilon (by rw [Section6Stopping.holderStoppingS]; norm_num)
    hlambda0 hlambda1 hdelta omega y hy hcY.1 hc0.1 hcY.2 hc0.2
  dsimp only at hraw
  exact hraw.2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
