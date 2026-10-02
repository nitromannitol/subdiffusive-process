import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ParameterAbsorption
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowTwoCollapse

/-!
# The final absorption of row 2's prefactor

Two pieces.

* `holderExponentialAbsorption_mono` — the absorption of
  `Section6Holder.exists_holderExponentialAbsorption` survives *enlarging* `C₁`:
  the exponent is decreasing in `C₁` and the right-hand side does not depend on
  it.  Row 2 needs `C₁ ≥ 2`, because the good-scale window it opens above the
  base scale must still fit below the domain, which forces
  `lambda = C₁⁻¹(1-alpha) ≤ 1/4`.

* `rowTwo_absorb_arith` — the arithmetic that turns the Step-6 conversion's
  output into the frozen row-2 shape once the two legs and the window price are
  in exponential form.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- The exponential absorption is monotone in `C₁`. -/
theorem holderExponentialAbsorption_mono {A0 P C1 C1' C : ℝ} (hP : 0 ≤ P)
    (hC1 : 0 < C1) (hle : C1 ≤ C1')
    (h : ∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
      Real.exp (A0 + P * (C1⁻¹ * (1 - alpha)) * (gap + 1)) ≤
        C * (3 : ℝ) ^ ((1 - alpha) * gap / 4)) :
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gap : ℝ, 0 ≤ gap →
      Real.exp (A0 + P * (C1'⁻¹ * (1 - alpha)) * (gap + 1)) ≤
        C * (3 : ℝ) ^ ((1 - alpha) * gap / 4) := by
  intro alpha halpha gap hgap
  refine le_trans (Real.exp_le_exp.mpr ?_) (h alpha halpha gap hgap)
  have ha0 : (0 : ℝ) ≤ 1 - alpha := by linarith [halpha.2]
  have hinv : C1'⁻¹ ≤ C1⁻¹ := inv_anti₀ hC1 hle
  have hstep : C1'⁻¹ * (1 - alpha) ≤ C1⁻¹ * (1 - alpha) :=
    mul_le_mul_of_nonneg_right hinv ha0
  have hgap1 : (0 : ℝ) ≤ gap + 1 := by linarith
  have h1 : P * (C1'⁻¹ * (1 - alpha)) ≤ P * (C1⁻¹ * (1 - alpha)) :=
    mul_le_mul_of_nonneg_left hstep hP
  have h2 := mul_le_mul_of_nonneg_right h1 hgap1
  linarith only [h2]

/-- **The final absorption of row 2's prefactor.** -/
theorem rowTwo_absorb_arith {price Ksq A B Ka Kb Cabs a b gapfac Elocal T : ℝ}
    (hKsq : 0 ≤ Ksq) (hT : 0 ≤ T) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hE : Elocal ≤ price * Ksq * ((A + B) * T))
    (hpriceb : price ≤ Real.exp b)
    (hA : A ≤ Ka * Real.exp a) (hB : B ≤ Kb * Real.exp a)
    (hexp : Real.exp (a + b) ≤ Cabs * gapfac) :
    Elocal ≤ Ksq * (Ka + Kb) * Cabs * gapfac * T := by
  have hAB : A + B ≤ (Ka + Kb) * Real.exp a := by
    calc A + B ≤ Ka * Real.exp a + Kb * Real.exp a := add_le_add hA hB
      _ = (Ka + Kb) * Real.exp a := by ring
  have hAB0 : 0 ≤ A + B := by linarith
  have hkey : price * (A + B) ≤ (Ka + Kb) * (Cabs * gapfac) := by
    calc price * (A + B) ≤ Real.exp b * ((Ka + Kb) * Real.exp a) :=
          mul_le_mul hpriceb hAB hAB0 (Real.exp_nonneg b)
      _ = (Ka + Kb) * Real.exp (a + b) := by rw [Real.exp_add]; ring
      _ ≤ (Ka + Kb) * (Cabs * gapfac) := by
          refine mul_le_mul_of_nonneg_left hexp ?_
          nlinarith only [hAB, hAB0, Real.exp_pos a, Real.exp_nonneg a]
  calc Elocal ≤ price * Ksq * ((A + B) * T) := hE
    _ = Ksq * (price * (A + B)) * T := by ring
    _ ≤ Ksq * ((Ka + Kb) * (Cabs * gapfac)) * T := by
        refine mul_le_mul_of_nonneg_right ?_ hT
        exact mul_le_mul_of_nonneg_left hkey hKsq
    _ = Ksq * (Ka + Kb) * Cabs * gapfac * T := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
