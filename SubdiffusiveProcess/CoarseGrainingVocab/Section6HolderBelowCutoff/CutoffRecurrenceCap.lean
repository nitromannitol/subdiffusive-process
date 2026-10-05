module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.AccumulatedErrorCovariance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffErrorCap

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- Cutoff companion of
`Section6Holder.exists_holderSection6Error_le_recurrenceMin`, with the binder
`m ≤ L` deleted. -/
theorem exists_holderSection6Error_le_recurrenceMin_cutoff (d : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ L m : ℕ, ∀ omega z,
        ∀ epsilon ∈ Set.Icc
            (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1,
          omega ∈ goodEvent M (some L) m z epsilon
              Section6Stopping.holderStoppingS →
            section6HomogenizationError M Section6Stopping.holderStoppingS
                L m omega z ≤
              K * min epsilon (M.delta ^ 2 + epsilon ^ 8 +
                accumulatedError M (some L) m z
                  Section6Stopping.holderStoppingS omega) := by
  obtain ⟨C, hC, hcut⟩ := _root_.SubdiffusiveProcess.Section6.cutoff_regularity_good_scales d
  refine ⟨32 * C, by positivity, ?_⟩
  intro M hsmall L m omega z epsilon hepsilon hgood
  have hs : Section6Stopping.holderStoppingS ∈
      Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ) := by
    refine ⟨hsmall, ?_⟩
    rw [Section6Stopping.holderStoppingS]
    norm_num
  have hraw := ((hcut M L).2.2.2.2 Section6Stopping.holderStoppingS hs
    epsilon hepsilon m z omega).1
  rw [Section6ExcessDecay.indicatorValue_of_mem hgood] at hraw
  refine hraw.trans ?_
  set E : ℝ := accumulatedError M (some L) m z
    Section6Stopping.holderStoppingS omega with hEdef
  have hE0 : 0 ≤ E :=
    Section6Holder.accumulatedError_nonneg M (some L)
      Section6Stopping.holderStoppingS m z omega
  have heps0 : 0 ≤ epsilon := by
    have h0 : 0 ≤ Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2 := by
      have : (0 : ℝ) < Section6Stopping.holderStoppingS :=
        Section6Stopping.holderStoppingS_pos
      positivity
    exact le_trans h0 hepsilon.1
  have hinv : Section6Stopping.holderStoppingS⁻¹ = (32 : ℝ) := by
    rw [Section6Stopping.holderStoppingS]; norm_num
  have hmin : min epsilon (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2 +
        epsilon ^ 8 + E) ≤
      32 * min epsilon (M.delta ^ 2 + epsilon ^ 8 + E) := by
    have hleft : min epsilon (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2 +
        epsilon ^ 8 + E) ≤ 32 * epsilon := by
      refine le_trans (min_le_left _ _) ?_
      linarith
    have hright : min epsilon (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2 +
        epsilon ^ 8 + E) ≤ 32 * (M.delta ^ 2 + epsilon ^ 8 + E) := by
      refine le_trans (min_le_right _ _) ?_
      rw [hinv]
      have h8 : 0 ≤ epsilon ^ 8 := by positivity
      linarith
    have h32 : 32 * min epsilon (M.delta ^ 2 + epsilon ^ 8 + E) =
        min (32 * epsilon) (32 * (M.delta ^ 2 + epsilon ^ 8 + E)) := by
      rcases le_total epsilon (M.delta ^ 2 + epsilon ^ 8 + E) with h | h
      · rw [min_eq_left h, min_eq_left (by linarith : (32 : ℝ) * epsilon ≤
          32 * (M.delta ^ 2 + epsilon ^ 8 + E))]
      · rw [min_eq_right h, min_eq_right (by linarith : (32 : ℝ) *
          (M.delta ^ 2 + epsilon ^ 8 + E) ≤ 32 * epsilon)]
    rw [h32]
    exact le_min hleft hright
  calc
    C * min epsilon (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2 +
          epsilon ^ 8 + E) ≤ C * (32 * min epsilon
            (M.delta ^ 2 + epsilon ^ 8 + E)) :=
      mul_le_mul_of_nonneg_left hmin hC.le
    _ = 32 * C * min epsilon (M.delta ^ 2 + epsilon ^ 8 + E) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
