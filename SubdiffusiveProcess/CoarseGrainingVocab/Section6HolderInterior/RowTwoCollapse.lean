module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoLegArith

@[expose] public section

/-!
# The three abstract collapses of row 2's oscillation leg

Pure real arithmetic, stated so that the geometric assembly never has to retype
the ladder's constants:

* `rowTwo_defect_arith` — the defect budget, once its datum has been paired
  against the one;
* `rowTwo_Ksum_arith` — the two coefficients of the leg against a single
  exponential;
* `rowTwo_collapse_arith` — the final product, with the two exponents added.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

noncomputable section

/-- The defect budget against the datum. -/
theorem rowTwo_defect_arith {S Kf t E TF Da : ℝ} (hKf : 0 ≤ Kf) (hE : 0 ≤ E)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hDa : 0 ≤ Da)
    (hStf : S * TF ≤ E * Da) :
    S * (5 / 2 * Kf * t * E * TF) ≤ 5 / 2 * Kf * E * E * Da := by
  have hA0 : (0 : ℝ) ≤ 5 / 2 * Kf * t * E := by positivity
  have hQ0 : (0 : ℝ) ≤ 5 / 2 * Kf * E * E * Da := by positivity
  calc S * (5 / 2 * Kf * t * E * TF)
      = (5 / 2 * Kf * t * E) * (S * TF) := by ring
    _ ≤ (5 / 2 * Kf * t * E) * (E * Da) := mul_le_mul_of_nonneg_left hStf hA0
    _ = t * (5 / 2 * Kf * E * E * Da) := by ring
    _ ≤ 1 * (5 / 2 * Kf * E * E * Da) := mul_le_mul_of_nonneg_right ht1 hQ0
    _ = 5 / 2 * Kf * E * E * Da := by ring

/-- The two coefficients of the leg against a single exponential. -/
theorem rowTwo_Ksum_arith {E TP Kosc Kf X : ℝ} (hKosc : 0 ≤ Kosc) (hKf : 0 ≤ Kf)
    (h1 : E * TP ≤ X) (h2 : E * E ≤ X) :
    E * (Kosc * TP) + 5 / 2 * Kf * E * E ≤ (Kosc + 5 / 2 * Kf) * X := by
  have hKf' : (0 : ℝ) ≤ 5 / 2 * Kf := by linarith
  have hA : E * (Kosc * TP) ≤ Kosc * X := by
    calc E * (Kosc * TP) = Kosc * (E * TP) := by ring
      _ ≤ Kosc * X := mul_le_mul_of_nonneg_left h1 hKosc
  have hB : 5 / 2 * Kf * E * E ≤ 5 / 2 * Kf * X := by
    calc 5 / 2 * Kf * E * E = (5 / 2 * Kf) * (E * E) := by ring
      _ ≤ (5 / 2 * Kf) * X := mul_le_mul_of_nonneg_left h2 hKf'
  calc E * (Kosc * TP) + 5 / 2 * Kf * E * E ≤ Kosc * X + 5 / 2 * Kf * X :=
        add_le_add hA hB
    _ = (Kosc + 5 / 2 * Kf) * X := by ring

/-- The final product of row 2's oscillation leg. -/
theorem rowTwo_collapse_arith {price E1 Ksum T Kfac a1 a2 a3 : ℝ}
    (hprice : 0 ≤ price) (hT : 0 ≤ T) (hKsum : 0 ≤ Ksum)
    (hE1 : E1 ≤ Real.exp a1) (hK : Ksum ≤ Kfac * Real.exp a2)
    (hexp : a1 + a2 = a3) :
    price * E1 * (Ksum * T) ≤ price * Kfac * Real.exp a3 * T := by
  have hprod : E1 * Ksum ≤ Kfac * Real.exp a3 := by
    calc E1 * Ksum ≤ Real.exp a1 * (Kfac * Real.exp a2) :=
          mul_le_mul hE1 hK hKsum (Real.exp_nonneg _)
      _ = Kfac * (Real.exp a1 * Real.exp a2) := by ring
      _ = Kfac * Real.exp (a1 + a2) := by rw [← Real.exp_add]
      _ = Kfac * Real.exp a3 := by rw [hexp]
  calc price * E1 * (Ksum * T) = price * (E1 * Ksum) * T := by ring
    _ ≤ price * (Kfac * Real.exp a3) * T := by
        refine mul_le_mul_of_nonneg_right ?_ hT
        exact mul_le_mul_of_nonneg_left hprod hprice
    _ = price * Kfac * Real.exp a3 * T := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
