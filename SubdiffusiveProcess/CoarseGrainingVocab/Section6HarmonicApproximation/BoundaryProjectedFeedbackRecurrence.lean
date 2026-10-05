module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicSeam.HalfStepRecurrence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProjectedComponentAssembly

@[expose] public section

/-!
# Separating projected-cell feedback in a radius recurrence

The affine-external half-step multiplies its complete projected-cell cap by
the inverse eighth power of the radius gap.  Consequently a term depending on
the outer profile belongs in the contraction slot only after that gap weight
has been included.  This file records that exact algebraic interface.

the radius-pair correction is the
the direct radius-recurrence argument.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization

noncomputable section

/-- A half-step whose gap-priced cap splits into outer-profile feedback and a
fixed budget is a `BudgetedRadiusRecurrence`.  Notice that `hcap` is stated
*after* multiplication by the inverse-gap factor; this prevents an
unjustified radius-independent cap from being placed in the theta slot. -/
theorem budgetedRadiusRecurrence_of_gapWeightedFeedback
    (F : ℝ → ℝ) (cap : ℝ → ℝ → ℝ)
    {thetaBase thetaFeedback A B beta : ℝ}
    (hstep : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      F rho ≤ thetaBase * F R +
        cap rho R * Real.rpow (R - rho) (-beta))
    (hcap : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      cap rho R * Real.rpow (R - rho) (-beta) ≤
        thetaFeedback * F R +
          A * Real.rpow (R - rho) (-beta) + B) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.BudgetedRadiusRecurrence
      F (thetaBase + thetaFeedback) A B beta := by
  intro rho R hrho hgap hR
  have hs := hstep rho R hrho hgap hR
  have hc := hcap rho R hrho hgap hR
  linarith

/-- Specialized bookkeeping for the proved affine-external half-step.  The
base contraction is exactly `1/2` and the gap power exactly `8`; only the
gap-weighted projected feedback is carried as a hypothesis. -/
theorem budgetedRadiusRecurrence_of_projectedHalfStepFeedback
    (F : ℝ → ℝ) (cap : ℝ → ℝ → ℝ) {thetaFeedback A B : ℝ}
    (hstep : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      F rho ≤ (1 / 2 : ℝ) * F R +
        cap rho R * Real.rpow (R - rho) (-8 : ℝ))
    (hcap : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      cap rho R * Real.rpow (R - rho) (-8 : ℝ) ≤
        thetaFeedback * F R +
          A * Real.rpow (R - rho) (-8 : ℝ) + B) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.BudgetedRadiusRecurrence
      F ((1 / 2 : ℝ) + thetaFeedback) A B 8 := by
  exact budgetedRadiusRecurrence_of_gapWeightedFeedback F cap hstep hcap

/-- Concrete projected-cell cap, with the common-gap feedback separated from
the four manuscript budgets.  The hypothesis `hX` is deliberately imposed
after the inverse eighth-power gap weight: its first term is the outer-radius
energy and hence belongs in the recurrence's theta slot.  The remaining four
prices are collected into its singular budget slot. -/
theorem budgetedRadiusRecurrence_of_projectedFourBudgetFeedback
    (F : ℝ → ℝ) (X : ℝ → ℝ → ℝ)
    {C K BE Ad Ag budgets thetaFeedback CX CBE CAd CAg : ℝ}
    (hC : 0 < C) (hK : 0 < K)
    (htheta : thetaFeedback < 1 / 2)
    (hstep : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      F rho ≤ (1 / 2 : ℝ) * F R +
        (X rho R + (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE +
          (5 / 2 : ℝ) * Ad + (5 / 2 : ℝ) * Ag) *
            Real.rpow (R - rho) (-8 : ℝ))
    (hX : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 1 →
      X rho R * Real.rpow (R - rho) (-8 : ℝ) ≤
        thetaFeedback * F R +
          CX * budgets * Real.rpow (R - rho) (-8 : ℝ))
    (hBE : BE ≤ CBE * budgets)
    (hAd : Ad ≤ CAd * budgets)
    (hAg : Ag ≤ CAg * budgets) :
    (1 / 2 : ℝ) + thetaFeedback < 1 ∧
      SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.BudgetedRadiusRecurrence
        F ((1 / 2 : ℝ) + thetaFeedback)
          ((CX + (1 / 8 + (64 * C ^ 4 * K)⁻¹) * CBE +
              (5 / 2 : ℝ) * CAd + (5 / 2 : ℝ) * CAg) * budgets)
          0 8 := by
  have hden : 0 < 64 * C ^ 4 * K := by positivity
  have hcoeff : 0 ≤ 1 / 8 + (64 * C ^ 4 * K)⁻¹ := by positivity
  have hcontract : (1 / 2 : ℝ) + thetaFeedback < 1 := by linarith
  refine ⟨hcontract, ?_⟩
  intro rho R hrho hlt hR
  have hgap : 0 < R - rho := sub_pos.mpr hlt
  have hpow : 0 ≤ Real.rpow (R - rho) (-8 : ℝ) :=
    Real.rpow_nonneg hgap.le _
  have hBE' :
      (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE *
          Real.rpow (R - rho) (-8 : ℝ) ≤
        (1 / 8 + (64 * C ^ 4 * K)⁻¹) * (CBE * budgets) *
          Real.rpow (R - rho) (-8 : ℝ) := by
    gcongr
  have hAd' : (5 / 2 : ℝ) * Ad * Real.rpow (R - rho) (-8 : ℝ) ≤
      (5 / 2 : ℝ) * (CAd * budgets) *
        Real.rpow (R - rho) (-8 : ℝ) := by
    gcongr
  have hAg' : (5 / 2 : ℝ) * Ag * Real.rpow (R - rho) (-8 : ℝ) ≤
      (5 / 2 : ℝ) * (CAg * budgets) *
        Real.rpow (R - rho) (-8 : ℝ) := by
    gcongr
  have hX' := hX rho R hrho hlt hR
  have hcap :
    (X rho R + (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE +
          (5 / 2 : ℝ) * Ad + (5 / 2 : ℝ) * Ag) *
        Real.rpow (R - rho) (-8 : ℝ) ≤
      thetaFeedback * F R +
        ((CX + (1 / 8 + (64 * C ^ 4 * K)⁻¹) * CBE +
            (5 / 2 : ℝ) * CAd + (5 / 2 : ℝ) * CAg) * budgets) *
          Real.rpow (R - rho) (-8 : ℝ) + 0 := by
    calc
      (X rho R + (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE +
            (5 / 2 : ℝ) * Ad + (5 / 2 : ℝ) * Ag) *
          Real.rpow (R - rho) (-8 : ℝ) =
      X rho R * Real.rpow (R - rho) (-8 : ℝ) +
        ((1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE *
          Real.rpow (R - rho) (-8 : ℝ)) +
        ((5 / 2 : ℝ) * Ad * Real.rpow (R - rho) (-8 : ℝ)) +
          ((5 / 2 : ℝ) * Ag * Real.rpow (R - rho) (-8 : ℝ)) := by ring
    _ ≤ (thetaFeedback * F R +
          CX * budgets * Real.rpow (R - rho) (-8 : ℝ)) +
        ((1 / 8 + (64 * C ^ 4 * K)⁻¹) * (CBE * budgets) *
          Real.rpow (R - rho) (-8 : ℝ)) +
        ((5 / 2 : ℝ) * (CAd * budgets) *
          Real.rpow (R - rho) (-8 : ℝ)) +
        ((5 / 2 : ℝ) * (CAg * budgets) *
          Real.rpow (R - rho) (-8 : ℝ)) := by
      gcongr
    _ = thetaFeedback * F R +
        ((CX + (1 / 8 + (64 * C ^ 4 * K)⁻¹) * CBE +
            (5 / 2 : ℝ) * CAd + (5 / 2 : ℝ) * CAg) * budgets) *
          Real.rpow (R - rho) (-8 : ℝ) + 0 := by ring
  have hs := hstep rho R hrho hlt hR
  linarith

/-- Epsilon-exposed form of the projected sharp-parent cap.

`hsharp` is exactly the output of
`exists_boundaryCommonGapPowerBudget_le_projectedSharpParentCap`.  The ASD
radius-pair argument is isolated in `hASD`: it may choose any explicit
`epsilon < 1/2`, and must place the resulting feedback against the outer
profile only after the inverse-gap weight is applied.  This is the strongest
transport justified by the committed sharp-parent theorem, which itself has
no adjustable parameter. -/
theorem boundaryCommonGapPowerBudget_mul_gapRpow_le_epsilonFeedback_of_projectedSharpParentCap
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {s sigma K C U G L gap epsilon outerEnergy budgetConstant budgets : ℝ}
    (u : Vec d → ℝ) (g : Vec d → Vec d)
    (hgap : 0 < gap) (hepsilon : epsilon < 1 / 2)
    (hsharp : boundaryCommonGapPowerBudget Q s sigma K C 0 u g ≤
      projectedPhysicalGapBudgetCap d Q s sigma K C U G L)
    (hASD : projectedPhysicalGapBudgetCap d Q s sigma K C U G L *
        Real.rpow gap (-8 : ℝ) ≤
      epsilon * outerEnergy +
        budgetConstant * budgets * Real.rpow gap (-8 : ℝ)) :
    epsilon < 1 / 2 ∧
      boundaryCommonGapPowerBudget Q s sigma K C 0 u g *
          Real.rpow gap (-8 : ℝ) ≤
        epsilon * outerEnergy +
          budgetConstant * budgets * Real.rpow gap (-8 : ℝ) := by
  refine ⟨hepsilon, ?_⟩
  exact (mul_le_mul_of_nonneg_right hsharp
    (Real.rpow_nonneg hgap.le _)).trans hASD

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
