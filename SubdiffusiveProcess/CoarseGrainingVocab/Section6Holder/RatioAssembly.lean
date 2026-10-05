module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.CubeAverageRatio

@[expose] public section

/-!
# Hölder Step 3: assembly of the local/top coefficient ratio

This composes the parent suffix comparison, the finite shell block, and the
annealed-normalizer error in the exact `combinedCoefficientRatio` carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

noncomputable section

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- The forward combined ratio is bounded by the product of the parent ratio
and the exponential shell/normalizer budget. -/
theorem combinedCoefficientRatio_le_of_budgets {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m q : ℕ)
    (omega : Sample d) (z x : Vec d) {P B R : ℝ} (hP : 0 ≤ P)
    (hparent : tailCoefficient M L m (translatePotentialSample z omega) x /
      tailCoefficientCubeAverage M L m omega ≤ P)
    (hshell : |shellBlock m q (translatePotentialSample z omega) x| ≤ B)
    (hrho : |normalizerLogError M m q| ≤ R) :
    combinedCoefficientRatio M L m q omega z x ≤ P * Real.exp (B + R) := by
  have hexp : Real.exp (shellBlock m q (translatePotentialSample z omega) x +
      normalizerLogError M m q) ≤ Real.exp (B + R) := by
    apply Real.exp_le_exp.mpr
    calc
      shellBlock m q (translatePotentialSample z omega) x + normalizerLogError M m q
          ≤ |shellBlock m q (translatePotentialSample z omega) x| +
              |normalizerLogError M m q| := add_le_add (le_abs_self _) (le_abs_self _)
      _ ≤ B + R := add_le_add hshell hrho
  unfold combinedCoefficientRatio
  exact mul_le_mul hparent hexp (Real.exp_pos _).le hP

/-- The reciprocal combined ratio obeys the same budget. -/
theorem combinedCoefficientRatioInv_le_of_budgets {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m q : ℕ)
    (omega : Sample d) (z x : Vec d) {P B R : ℝ} (hP : 0 ≤ P)
    (hparent : tailCoefficientCubeAverage M L m omega /
      tailCoefficient M L m (translatePotentialSample z omega) x ≤ P)
    (hshell : |shellBlock m q (translatePotentialSample z omega) x| ≤ B)
    (hrho : |normalizerLogError M m q| ≤ R) :
    combinedCoefficientRatioInv M L m q omega z x ≤ P * Real.exp (B + R) := by
  have hexp : Real.exp (-(shellBlock m q (translatePotentialSample z omega) x +
      normalizerLogError M m q)) ≤ Real.exp (B + R) := by
    apply Real.exp_le_exp.mpr
    calc
      -(shellBlock m q (translatePotentialSample z omega) x +
          normalizerLogError M m q)
          ≤ |shellBlock m q (translatePotentialSample z omega) x| +
              |normalizerLogError M m q| := by
            linarith [neg_le_abs (shellBlock m q (translatePotentialSample z omega) x),
              neg_le_abs (normalizerLogError M m q)]
      _ ≤ B + R := add_le_add hshell hrho
  unfold combinedCoefficientRatioInv
  calc
    Real.exp (-(shellBlock m q (translatePotentialSample z omega) x +
        normalizerLogError M m q)) *
        (tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m (translatePotentialSample z omega) x)
        ≤ Real.exp (-(shellBlock m q (translatePotentialSample z omega) x +
            normalizerLogError M m q)) * P :=
          mul_le_mul_of_nonneg_left hparent (Real.exp_pos _).le
    _ ≤ Real.exp (B + R) * P := mul_le_mul_of_nonneg_right hexp hP
    _ = P * Real.exp (B + R) := by ring

/-- The literal lower local average and the top cube average obey the same
two-sided bound once the three pointwise budgets are uniform on the lower
cube. -/
theorem tailAverage_ratio_bounds_of_budgets {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m q : ℕ}
    (hqm : q ≤ m) (hmL : m ≤ L) (omega : Sample d) (z : Vec d)
    {P B R : ℝ} (hP : 0 ≤ P)
    (hparent : ∀ x ∈ cube d (q : ℤ),
      tailCoefficient M L m (translatePotentialSample z omega) x /
          tailCoefficientCubeAverage M L m omega ≤ P ∧
        tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m (translatePotentialSample z omega) x ≤ P)
    (hshell : ∀ x ∈ cube d (q : ℤ),
      |shellBlock m q (translatePotentialSample z omega) x| ≤ B)
    (hrho : |normalizerLogError M m q| ≤ R) :
    tailAverage M L q omega (translatedCube d (q : ℤ) z) /
        tailCoefficientCubeAverage M L m omega ≤ P * Real.exp (B + R) ∧
      tailCoefficientCubeAverage M L m omega /
        tailAverage M L q omega (translatedCube d (q : ℤ) z) ≤
          P * Real.exp (B + R) := by
  apply tailAverage_ratio_bounds_of_combined M hqm hmL omega z
  · intro x hx
    exact combinedCoefficientRatio_le_of_budgets M L m q omega z x hP
      (hparent x hx).1 (hshell x hx) hrho
  · intro x hx
    exact combinedCoefficientRatioInv_le_of_budgets M L m q omega z x hP
      (hparent x hx).2 (hshell x hx) hrho

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
