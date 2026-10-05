module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpSuffixRepresentative

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open SubdiffusiveProcess.CoarseGrainingVocab

/-!
# Algebra behind the combine estimate

The proof is decomposed as in Algsuperdiff's `CombineGoodEvent.lean` and
`FiniteRecurrence.lean`: expansion, energy absorption, then the final merge of
the defect, variance/mean, and bad-event blocks.
-/

/-- The seven nonconstant terms obtained by expanding a three-factor ratio.
This is the algebra used before Hölder is applied to the three stochastic
factors. -/
theorem combineStep1_defect_algebra (X Y Z : ℝ) :
    |X * Y * Z - 1| ≤
      |X - 1| + |Y - 1| + |Z - 1| +
        |X - 1| * |Y - 1| + |X - 1| * |Z - 1| +
        |Y - 1| * |Z - 1| + |X - 1| * |Y - 1| * |Z - 1| := by
  have h := abs_mul_three_sub_one_le_product_envelope
    (X := X) (Y := Y) (Z := Z)
    (DX := |X - 1|) (DY := |Y - 1|) (DZ := |Z - 1|)
    (abs_nonneg _) (abs_nonneg _) le_rfl le_rfl le_rfl
  calc
    |X * Y * Z - 1| ≤
        (1 + |X - 1|) * (1 + |Y - 1|) * (1 + |Z - 1|) - 1 := h
    _ = _ := by ring

/-- Absorb the energy remainder in the good-event estimate. -/
theorem combineStep1_absorb_energy {J main energy : ℝ}
    (hJ : J ≤ main + energy) (henergy : energy ≤ (1 / 2 : ℝ) * J) :
    J ≤ 2 * main := by
  linarith

/-- Merge the three quantitative blocks at the end of the combine proof.
`defect` is the weighted response-difference sum; `matrix` combines the mean
and variance estimates; `bad` is the exceptional-event contribution. -/
theorem combineStep5_close {J defect responseSum matrix bad C δ r : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hJ : J ≤ defect + matrix + bad)
    (hdefect : defect ≤ C * responseSum)
    (hmatrix : matrix ≤ C * δ * (δ + r))
    (hbad : bad ≤ C * δ ^ 2) :
    J ≤ C * responseSum + 2 * C * δ * (δ + r) := by
  have hsquare : C * δ ^ 2 ≤ C * δ * (δ + r) := by
    nlinarith [mul_nonneg hC (mul_nonneg hδ hr)]
  linarith

/-- A version of the final merge in which the response-difference term is
already normalized, avoiding the self-referential term used by the
preceding low-level lemma. -/
theorem combineStep5_close_normalized {J defect matrix bad C δ r : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hJ : J ≤ C * defect + matrix + bad)
    (hmatrix : matrix ≤ C * δ * (δ + r))
    (hbad : bad ≤ C * δ ^ 2) :
    J ≤ C * defect + 2 * C * δ * (δ + r) := by
  have hsquare : C * δ ^ 2 ≤ C * δ * (δ + r) := by
    nlinarith [mul_nonneg hC (mul_nonneg hδ hr)]
  linarith

/-- Remove a recurrence term proportional to the current value. -/
theorem recurrence_absorb_current {F forcing history θ : ℝ}
    (hF0 : 0 ≤ F) (hθ : θ ≤ 1 / 2)
    (hF : F ≤ forcing + history + θ * F) :
    F ≤ 2 * (forcing + history) := by
  nlinarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
