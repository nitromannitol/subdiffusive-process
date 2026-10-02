import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary.BoundaryNorm
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneAbsorption




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

noncomputable section

/-- Joint ladder/ratio absorption with the boundary recurrence's linear gap
factor. -/
theorem expAbar_mul_linearRatio_le
    {Citer Keps Cratio alpha gap k C1 Cabs : ℝ}
    (hCiter : 0 ≤ Citer) (hCratio : 0 ≤ Cratio)
    (hgap : 0 ≤ gap) (hk : 0 ≤ k)
    (halpha : alpha ∈ Set.Icc (1 / 2 : ℝ) 1) (hC1 : 0 < C1)
    (habsorb : ∀ a ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ gp : ℝ, 0 ≤ gp →
      (1 + C1⁻¹ * (1 - a) * gp) *
          Real.exp (Citer * (k + 1) * (k + 2) +
            (Citer * (k + 1) + 3 * Citer * Keps + Cratio) *
              (C1⁻¹ * (1 - a)) * (gp + 1)) ≤
        Cabs * (3 : ℝ) ^ ((1 - a) * gp / 4)) :
    Real.exp (Citer * (k + 1) * (k + 2 + (C1⁻¹ * (1 - alpha)) * gap) +
        Citer * (3 * Keps * (C1⁻¹ * (1 - alpha)) * (gap + 1))) *
      ((1 + C1⁻¹ * (1 - alpha) * gap) *
        Real.exp (Cratio * (C1⁻¹ * (1 - alpha)) * gap)) ≤
      Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4) := by
  have hlambda : 0 ≤ C1⁻¹ * (1 - alpha) :=
    mul_nonneg (inv_nonneg.mpr hC1.le) (by linarith [halpha.2])
  have hlinear : 0 ≤ 1 + C1⁻¹ * (1 - alpha) * gap := by positivity
  have hsum := ladderExponent_le_affine (Citer := Citer) (Keps := Keps)
    (Cratio := Cratio) (lambda := C1⁻¹ * (1 - alpha)) (gap := gap) (k := k)
    hCiter hCratio hlambda hk
  have hexponential :
      Real.exp (Citer * (k + 1) *
            (k + 2 + (C1⁻¹ * (1 - alpha)) * gap) +
          Citer * (3 * Keps * (C1⁻¹ * (1 - alpha)) * (gap + 1))) *
        Real.exp (Cratio * (C1⁻¹ * (1 - alpha)) * gap) ≤
      Real.exp (Citer * (k + 1) * (k + 2) +
        (Citer * (k + 1) + 3 * Citer * Keps + Cratio) *
          (C1⁻¹ * (1 - alpha)) * (gap + 1)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hsum
  have hscaled := mul_le_mul_of_nonneg_left hexponential hlinear
  calc
    Real.exp (Citer * (k + 1) *
          (k + 2 + (C1⁻¹ * (1 - alpha)) * gap) +
        Citer * (3 * Keps * (C1⁻¹ * (1 - alpha)) * (gap + 1))) *
        ((1 + C1⁻¹ * (1 - alpha) * gap) *
          Real.exp (Cratio * (C1⁻¹ * (1 - alpha)) * gap))
        = (1 + C1⁻¹ * (1 - alpha) * gap) *
          (Real.exp (Citer * (k + 1) *
              (k + 2 + (C1⁻¹ * (1 - alpha)) * gap) +
            Citer * (3 * Keps * (C1⁻¹ * (1 - alpha)) * (gap + 1))) *
            Real.exp (Cratio * (C1⁻¹ * (1 - alpha)) * gap)) := by ring
    _ ≤ (1 + C1⁻¹ * (1 - alpha) * gap) *
        Real.exp (Citer * (k + 1) * (k + 2) +
          (Citer * (k + 1) + 3 * Citer * Keps + Cratio) *
            (C1⁻¹ * (1 - alpha)) * (gap + 1)) := hscaled
    _ ≤ Cabs * (3 : ℝ) ^ ((1 - alpha) * gap / 4) :=
      habsorb alpha halpha gap hgap

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundary
