import SubdiffusiveProcess.Frozen.Section3.AnnealedMatrixBounds
import SubdiffusiveProcess.Frozen.Section3.SpecialTwoDExactFormula
import SubdiffusiveProcess.Frozen.Section5.HomogenizedCoefficientReciprocalLower
import SubdiffusiveProcess.Frozen.Section5.HomogenizedCoefficientStrictDecay




open SubdiffusiveProcess.CoarseGrainingVocab

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Renormalized

noncomputable section

/-- The conclusion of the frozen `p.sharp.asymptotic`, stated byte-for-byte as
in `SubdiffusiveProcess/Frozen/Section5/SharpAsymptotic.lean`.  Used only to name the
hypothesis; the draft anchor itself is never imported. -/
def SharpAsymptoticStatement (d : ℕ) : Prop :=
  ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
    ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      M.delta ≤ delta0 → ∀ m : ℕ,
        |Real.log (ahom M m) +
            2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (m + 1 : ℝ) / d| ≤
          C * M.delta ^ 2 * |Real.log M.delta| *
            (1 + (m : ℝ) * M.delta)

/-- **`t.renormalized.diffusivities` from the sharp asymptotic.**  The
conclusion is byte-identical to the frozen
`SubdiffusiveProcess.Frozen.Section5.renormalized_diffusivities` statement.

Residual hypotheses: exactly one, the sharp asymptotic itself.  Everything
else is discharged from PROVED anchors — `l.annealed.matrix.bounds`,
`p.special.two.d.exact.formula`,
`p.homogenized.coefficient.strict.decay`,
`p.homogenized.coefficient.reciprocal.lower` — and the vocabulary lemma
`ahom_le_one`. -/
theorem renormalized_diffusivities_of_sharp_asymptotic {d : ℕ}
    (hsharp : ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta)) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        ∃ eta : ℝ, 0 < eta ∧
          (∀ n m : ℕ, n ≤ m →
            Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤
                ahom M m ∧
            ahom M m ≤ ahom M n ∧
            ahom M n ≤ min 1
              (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
                ((m - n : ℕ) : ℝ)) * ahom M m) ∧
            ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ))) ∧
          (d = 2 → ∀ m : ℕ,
            ahom M m =
              Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) ∧
          (M.delta ≤ delta0 → ∀ m : ℕ,
            |Real.log (ahom M m) +
                2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (m + 1 : ℝ) / d| ≤
              C * M.delta ^ 2 * |Real.log M.delta| *
                (1 + (m : ℝ) * M.delta)) := by
  obtain ⟨delta0, C, hdelta0, hC, hsharpM⟩ := hsharp
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M
  obtain ⟨eta, heta, _hetaTwo, _hetaHigh, hdecay⟩ :=
    SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_strict_decay M
  refine ⟨eta, heta, ?_, ?_, hsharpM M⟩
  · -- the four-term chain at every pair of scales
    intro n m hnm
    rcases hnm.eq_or_lt with rfl | hlt
    · refine ⟨SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M n,
        le_rfl, le_min (ahom_le_one M n) ?_, hdecay n⟩
      simp
    · obtain ⟨hmono, hcomp⟩ :=
        (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds (d := d)).2 M m n hlt
      exact ⟨SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M m,
        hmono, le_min (ahom_le_one M n) hcomp, hdecay m⟩
  · -- the exact two-dimensional formula
    intro hd2
    subst hd2
    exact fun m ↦ SubdiffusiveProcess.Frozen.Section3.special_two_d_exact_formula M m

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Renormalized
