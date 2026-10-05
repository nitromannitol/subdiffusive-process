module

public import SubdiffusiveProcess.Section3.AnnealedMatrixBounds
public import SubdiffusiveProcess.Section3.SpecialTwoDExactFormula
public import SubdiffusiveProcess.Section5.HomogenizedCoefficientReciprocalLower
public import SubdiffusiveProcess.Section5.HomogenizedCoefficientStrictDecay

@[expose] public section

/-!
# `t.renormalized.diffusivities` from `p.sharp.asymptotic`

The printed  is four citations:

> The ordering and adjacent-scale comparison are `e.annealed.ordering`; the
> affine competitor gives `ahom_0 ≤ 1`.  The remaining assertions are
> Propositions `p.special.two.d.exact.formula`, `p.sharp.asymptotic`,
> `p.homogenized.coefficient.strict.decay`, and
> `p.homogenized.coefficient.reciprocal.lower`.

This module formalizes exactly that.  The sharp asymptotic is taken as an
explicit hypothesis whose statement is byte-identical to the frozen
`SubdiffusiveProcess.Section5.sharp_asymptotic` body, so nothing here imports the
draft anchor; the other three inputs are estimates, consumed at their
frozen statements, plus the vocabulary bound `ahom_le_one`.

Once `p.sharp.asymptotic` seals, its provider term instantiates the hypothesis
and `renormalized_diffusivities_of_sharp_asymptotic` becomes the provider for
`t.renormalized.diffusivities` with no further mathematical content.
-/

open SubdiffusiveProcess.CoarseGrainingVocab

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Renormalized

noncomputable section

/-- The conclusion of the frozen `p.sharp.asymptotic`, stated byte-for-byte as
in `SubdiffusiveProcess/Section5/SharpAsymptotic.lean`.  Used only to name the
hypothesis; the draft anchor itself is never imported. -/
def SharpAsymptoticStatement (d : ℕ) : Prop :=
  ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
    ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      M.delta ≤ delta0 → ∀ m : ℕ,
        |Real.log (ahom M m) +
            2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
          C * M.delta ^ 2 * |Real.log M.delta| *
            (1 + (m : ℝ) * M.delta)

/-- **`t.renormalized.diffusivities` from the sharp asymptotic.**  The
conclusion is byte-identical to the frozen
`SubdiffusiveProcess.Section5.renormalized_diffusivities` statement.

Residual hypotheses: exactly one, the sharp asymptotic itself.  Everything
else is discharged from estimates — `l.annealed.matrix.bounds`,
`p.special.two.d.exact.formula`,
`p.homogenized.coefficient.strict.decay`,
`p.homogenized.coefficient.reciprocal.lower` — and the vocabulary lemma
`ahom_le_one`. -/
theorem renormalized_diffusivities_of_sharp_asymptotic {d : ℕ}
    (hsharp : ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta)) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        ∃ eta : ℝ, 0 < eta ∧
          (∀ n m : ℕ, n ≤ m →
            Real.exp (-(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≤
                ahom M m ∧
            ahom M m ≤ ahom M n ∧
            ahom M n ≤ min 1
              (Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
                ((m - n : ℕ) : ℝ)) * ahom M m) ∧
            ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ))) ∧
          (d = 2 → ∀ m : ℕ,
            ahom M m =
              Real.exp (-(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) ∧
          (M.delta ≤ delta0 → ∀ m : ℕ,
            |Real.log (ahom M m) +
                2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
              C * M.delta ^ 2 * |Real.log M.delta| *
                (1 + (m : ℝ) * M.delta)) := by
  obtain ⟨delta0, C, hdelta0, hC, hsharpM⟩ := hsharp
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M
  obtain ⟨eta, heta, _hetaTwo, _hetaHigh, hdecay⟩ :=
    _root_.SubdiffusiveProcess.Section5.homogenized_coefficient_strict_decay M
  refine ⟨eta, heta, ?_, ?_, hsharpM M⟩
  · -- the four-term chain at every pair of scales
    intro n m hnm
    rcases hnm.eq_or_lt with rfl | hlt
    · refine ⟨_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M n,
        le_rfl, le_min (ahom_le_one M n) ?_, hdecay n⟩
      simp
    · obtain ⟨hmono, hcomp⟩ :=
        (_root_.SubdiffusiveProcess.Section3.annealed_matrix_bounds (d := d)).2 M m n hlt
      exact ⟨_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M m,
        hmono, le_min (ahom_le_one M n) hcomp, hdecay m⟩
  · -- the exact two-dimensional formula
    intro hd2
    subst hd2
    exact fun m ↦ _root_.SubdiffusiveProcess.Section3.special_two_d_exact_formula M m

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Renormalized
