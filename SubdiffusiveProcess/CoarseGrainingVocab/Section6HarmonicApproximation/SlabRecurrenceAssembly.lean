module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.BudgetedRadiusIteration
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.SlabMeanSplit

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization

noncomputable section

/-- A slab thickness `delta ≤ eta * (R-rho)` converts the `delta²` Poincare
gain into an `eta²` gain after multiplication by the cutoff price
`(R-rho)⁻²`.  This is the scalar normalization used for a triadic thickness
`delta = 3^k'`. -/
theorem slabSq_mul_gapRpowNegTwo_le
    {slabSq outerEnergy Cslab delta eta rho R : ℝ}
    (houter : 0 ≤ outerEnergy)
    (hCslab : 0 ≤ Cslab) (hdelta0 : 0 ≤ delta) (heta : 0 ≤ eta)
    (hgap : rho < R) (hdelta : delta ≤ eta * (R - rho))
    (hslab : slabSq ≤ Cslab * delta ^ 2 * outerEnergy) :
    slabSq * Real.rpow (R - rho) (-2 : ℝ) ≤
      Cslab * eta ^ 2 * outerEnergy := by
  have hgap0 : 0 < R - rho := sub_pos.mpr hgap
  have hetaGap : 0 ≤ eta * (R - rho) := mul_nonneg heta hgap0.le
  have hdeltaSq : delta ^ 2 ≤ eta ^ 2 * (R - rho) ^ 2 := by
    nlinarith [sq_nonneg (eta * (R - rho) - delta)]
  have hrpow : Real.rpow (R - rho) (-2 : ℝ) = ((R - rho) ^ 2)⁻¹ := by
    calc
      Real.rpow (R - rho) (-2 : ℝ) =
          (Real.rpow (R - rho) (2 : ℝ))⁻¹ :=
        Real.rpow_neg hgap0.le (2 : ℝ)
      _ = ((R - rho) ^ 2)⁻¹ := by
        congr 1
        exact Real.rpow_natCast (R - rho) 2
  have hscaled : delta ^ 2 * Real.rpow (R - rho) (-2 : ℝ) ≤ eta ^ 2 := by
    rw [hrpow, ← div_eq_mul_inv]
    rw [div_le_iff₀ (sq_pos_of_pos hgap0)]
    nlinarith only [hdeltaSq]
  calc
    slabSq * Real.rpow (R - rho) (-2 : ℝ) ≤
        (Cslab * delta ^ 2 * outerEnergy) *
          Real.rpow (R - rho) (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right hslab (Real.rpow_nonneg hgap0.le _)
    _ = Cslab * outerEnergy *
          (delta ^ 2 * Real.rpow (R - rho) (-2 : ℝ)) := by ring
    _ ≤ Cslab * outerEnergy * eta ^ 2 :=
      mul_le_mul_of_nonneg_left hscaled (mul_nonneg hCslab houter)
    _ = Cslab * eta ^ 2 * outerEnergy := by ring

/-- Algebraic assembly of the corrected boundary row.

`hASD` is the separate-datum Caccioppoli row after isolating its parent mean;
`hmean` is the committed slab/oscillation split; `hslab` is the sole concrete
face-tile Poincare input.  The conclusion has exactly P-118's public
`BudgetedRadiusRecurrence` carrier, with the radius-priced oscillation budget
in `A` and the remaining four-budget terms in `B`. -/
theorem budgetedRadiusRecurrence_of_slabMeanRows
    (F : ℝ → ℝ) (meanSq slabSq : ℝ → ℝ → ℝ)
    {Cmean Cosc Cbase Cslab eta budgets : ℝ}
    (hCmean : 0 ≤ Cmean) (hCslab : 0 ≤ Cslab)
    (heta : 0 ≤ eta)
    (hF : ∀ R, (1 / 3 : ℝ) < R → R ≤ 1 → 0 ≤ F R)
    (hASD : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      F rho ≤ Cmean * meanSq rho R * Real.rpow (R - rho) (-2 : ℝ) +
        Cbase * budgets)
    (hmean : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      meanSq rho R ≤ 2 * slabSq rho R + Cosc * budgets)
    (hslab : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      ∃ delta : ℝ, 0 ≤ delta ∧ delta ≤ eta * (R - rho) ∧
        slabSq rho R ≤ Cslab * delta ^ 2 * F R) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.BudgetedRadiusRecurrence F
      (2 * Cmean * Cslab * eta ^ 2)
      (Cmean * Cosc * budgets) (Cbase * budgets) 2 := by
  intro rho R hrho hgap hR
  obtain ⟨delta, hdelta0, hdelta, hslabBound⟩ :=
    hslab rho R hrho hgap hR
  have hgapRpow : 0 ≤ Real.rpow (R - rho) (-2 : ℝ) :=
    Real.rpow_nonneg (sub_pos.mpr hgap).le _
  have hmeanScaled :
      meanSq rho R * Real.rpow (R - rho) (-2 : ℝ) ≤
        2 * (slabSq rho R * Real.rpow (R - rho) (-2 : ℝ)) +
          Cosc * budgets * Real.rpow (R - rho) (-2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (hmean rho R hrho hgap hR) hgapRpow
    nlinarith only [h]
  have hslabScaled :
      slabSq rho R * Real.rpow (R - rho) (-2 : ℝ) ≤
        Cslab * eta ^ 2 * F R :=
    slabSq_mul_gapRpowNegTwo_le
      (hF R (hrho.trans_lt hgap) hR)
      hCslab hdelta0 heta hgap hdelta hslabBound
  have hmeanFinal :
      Cmean * (meanSq rho R * Real.rpow (R - rho) (-2 : ℝ)) ≤
        (2 * Cmean * Cslab * eta ^ 2) * F R +
          (Cmean * Cosc * budgets) * Real.rpow (R - rho) (-2 : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hmeanScaled hCmean
    have h2 := mul_le_mul_of_nonneg_left hslabScaled
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCmean)
    nlinarith only [h1, h2]
  have hasd := hASD rho R hrho hgap hR
  rw [show Cmean * meanSq rho R * Real.rpow (R - rho) (-2 : ℝ) =
    Cmean * (meanSq rho R * Real.rpow (R - rho) (-2 : ℝ)) by ring] at hasd
  exact hasd.trans (by
    calc
      Cmean * (meanSq rho R * Real.rpow (R - rho) (-2 : ℝ)) +
          Cbase * budgets ≤
        ((2 * Cmean * Cslab * eta ^ 2) * F R +
          (Cmean * Cosc * budgets) * Real.rpow (R - rho) (-2 : ℝ)) +
            Cbase * budgets := by linarith only [hmeanFinal]
      _ = (2 * Cmean * Cslab * eta ^ 2) * F R +
          (Cmean * Cosc * budgets) * Real.rpow (R - rho) (-2 : ℝ) +
            Cbase * budgets := by ring)

/-- Additive-datum version of `budgetedRadiusRecurrence_of_slabMeanRows`.

For the physical boundary application the slab function is the zero extension
of `u - h`; hence its gradient energy is bounded by the solution energy plus
the datum energy.  The latter remains an unpriced additive budget after the
slab's `delta²` gain cancels the cutoff gap. -/
theorem budgetedRadiusRecurrence_of_slabMeanRows_additive
    (F : ℝ → ℝ) (meanSq slabSq : ℝ → ℝ → ℝ)
    {Cmean Cosc Cbase Cslab eta budgets : ℝ}
    (hCmean : 0 ≤ Cmean) (hCslab : 0 ≤ Cslab)
    (heta : 0 ≤ eta) (hbudgets : 0 ≤ budgets)
    (hF : ∀ R, (1 / 3 : ℝ) < R → R ≤ 1 → 0 ≤ F R)
    (hASD : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      F rho ≤ Cmean * meanSq rho R * Real.rpow (R - rho) (-2 : ℝ) +
        Cbase * budgets)
    (hmean : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      meanSq rho R ≤ 2 * slabSq rho R + Cosc * budgets)
    (hslab : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      ∃ delta : ℝ, 0 ≤ delta ∧ delta ≤ eta * (R - rho) ∧
        slabSq rho R ≤ Cslab * delta ^ 2 * (F R + budgets)) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.BudgetedRadiusRecurrence F
      (2 * Cmean * Cslab * eta ^ 2)
      (Cmean * Cosc * budgets)
      ((2 * Cmean * Cslab * eta ^ 2 + Cbase) * budgets) 2 := by
  intro rho R hrho hgap hR
  obtain ⟨delta, hdelta0, hdelta, hslabBound⟩ :=
    hslab rho R hrho hgap hR
  have hFR : 0 ≤ F R := hF R (hrho.trans_lt hgap) hR
  have hsum0 : 0 ≤ F R + budgets := add_nonneg hFR hbudgets
  have hgapRpow : 0 ≤ Real.rpow (R - rho) (-2 : ℝ) :=
    Real.rpow_nonneg (sub_pos.mpr hgap).le _
  have hmeanScaled :
      meanSq rho R * Real.rpow (R - rho) (-2 : ℝ) ≤
        2 * (slabSq rho R * Real.rpow (R - rho) (-2 : ℝ)) +
          Cosc * budgets * Real.rpow (R - rho) (-2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (hmean rho R hrho hgap hR) hgapRpow
    nlinarith only [h]
  have hslabScaled :
      slabSq rho R * Real.rpow (R - rho) (-2 : ℝ) ≤
        Cslab * eta ^ 2 * (F R + budgets) :=
    slabSq_mul_gapRpowNegTwo_le hsum0 hCslab hdelta0 heta hgap hdelta hslabBound
  have hmeanFinal :
      Cmean * (meanSq rho R * Real.rpow (R - rho) (-2 : ℝ)) ≤
        (2 * Cmean * Cslab * eta ^ 2) * F R +
          (Cmean * Cosc * budgets) * Real.rpow (R - rho) (-2 : ℝ) +
          (2 * Cmean * Cslab * eta ^ 2) * budgets := by
    have h1 := mul_le_mul_of_nonneg_left hmeanScaled hCmean
    have h2 := mul_le_mul_of_nonneg_left hslabScaled
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCmean)
    nlinarith only [h1, h2]
  have hasd := hASD rho R hrho hgap hR
  rw [show Cmean * meanSq rho R * Real.rpow (R - rho) (-2 : ℝ) =
    Cmean * (meanSq rho R * Real.rpow (R - rho) (-2 : ℝ)) by ring] at hasd
  calc
    F rho ≤ Cmean * (meanSq rho R * Real.rpow (R - rho) (-2 : ℝ)) +
        Cbase * budgets := hasd
    _ ≤ (2 * Cmean * Cslab * eta ^ 2) * F R +
        (Cmean * Cosc * budgets) * Real.rpow (R - rho) (-2 : ℝ) +
        (2 * Cmean * Cslab * eta ^ 2) * budgets + Cbase * budgets := by
      linarith only [hmeanFinal]
    _ = (2 * Cmean * Cslab * eta ^ 2) * F R +
        (Cmean * Cosc * budgets) * Real.rpow (R - rho) (-2 : ℝ) +
        ((2 * Cmean * Cslab * eta ^ 2 + Cbase) * budgets) := by ring

/-- Radius-row assembly after the concrete slab-to-parent volume ratio has
already been converted into its honest inverse-gap price.

This variant does not require the oscillation coefficient in the mean split
to be uniform in the slab thickness. -/
theorem budgetedRadiusRecurrence_of_scaledMeanRows
    (meanSq : ℝ → ℝ → ℝ) (profile : ℝ → ℝ)
    {Cmean Ccontract Cosc Cbase budgets beta : ℝ}
    (hCmean : 0 ≤ Cmean)
    (hASD : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      profile rho ≤ Cmean * meanSq rho R * Real.rpow (R - rho) (-2 : ℝ) +
        Cbase * budgets)
    (hmeanScaled : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      meanSq rho R * Real.rpow (R - rho) (-2 : ℝ) ≤
        Ccontract * profile R +
          Cosc * budgets * Real.rpow (R - rho) (-beta)) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.BudgetedRadiusRecurrence
      profile (Cmean * Ccontract) (Cmean * Cosc * budgets)
        (Cbase * budgets) beta := by
  intro rho R hrho hgap hR
  have hasd := hASD rho R hrho hgap hR
  have hscaled := hmeanScaled rho R hrho hgap hR
  have hmul := mul_le_mul_of_nonneg_left hscaled hCmean
  calc
    profile rho ≤
        Cmean * meanSq rho R * Real.rpow (R - rho) (-2 : ℝ) +
          Cbase * budgets := hasd
    _ = Cmean *
          (meanSq rho R * Real.rpow (R - rho) (-2 : ℝ)) +
            Cbase * budgets := by ring
    _ ≤ Cmean *
          (Ccontract * profile R +
            Cosc * budgets * Real.rpow (R - rho) (-beta)) +
            Cbase * budgets := by linarith only [hmul]
    _ = (Cmean * Ccontract) * profile R +
          (Cmean * Cosc * budgets) * Real.rpow (R - rho) (-beta) +
            Cbase * budgets := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
