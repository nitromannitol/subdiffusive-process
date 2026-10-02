import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.ContractionParameters
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ParameterAbsorption

/-! # Raising the cutoff ladder's contraction budget to the v4 power -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.BelowCutoff

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- Doubling the recurrence constant pays the D-073 change
`(1/4)^(-3/2) = 8` to `(1/4)^(-2) = 16`. -/
theorem holderContraction_v4_of_doubled_v3
    {C base amp epsilon theta : ℝ}
    (hC : 0 ≤ C) (hbase : 0 ≤ base)
    (h : (2 * C) *
      (base + amp * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * epsilon) ≤ theta) :
    C * (base + amp * (1 / 4 : ℝ) ^ (-2 : ℝ) * epsilon) ≤ theta := by
  have hp32 : (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) = 8 := by norm_num
  have hp2 : (1 / 4 : ℝ) ^ (-2 : ℝ) = 16 := by norm_num
  rw [hp32] at h
  rw [hp2]
  apply le_trans ?_ h
  nlinarith

/-- Boundary-owned parameter selector for the v4 cutoff recurrence.  The
underlying v3 selector is invoked at `2 * Cstep`; the preceding arithmetic
adapter is the only place where the D-073 exponent change is paid. -/
theorem exists_boundaryHolderContractionParameters_cut (d : ℕ) (Cstep : ℝ)
    (hCstep : 0 < Cstep) :
    ∃ k : ℕ, ∃ C₂ : ℝ, 0 < k ∧ 1 ≤ C₂ ∧
      let theta := (3 : ℝ) ^ (-(1 / 4 : ℝ))
      theta ∈ Set.Ioo (0 : ℝ) 1 ∧ theta ^ k ∈ Set.Ioo (0 : ℝ) (3 / 5) ∧
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ C₂⁻¹ →
        Cstep * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
            (1 / 4 : ℝ) ^ (-2 : ℝ) * epsilon) ≤ theta ^ k := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.exists_holderContractionParameters_cut (d := d) (Cstep := Cstep) (hCstep := hCstep)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.BelowCutoff
