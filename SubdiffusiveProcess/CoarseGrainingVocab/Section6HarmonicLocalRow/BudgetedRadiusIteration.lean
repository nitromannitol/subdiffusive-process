module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.AdjustableAbsorption
public import Homogenization.Deterministic.CoarseCaccioppoli.Basic

@[expose] public section

/-!
# Budgeted, free-contraction radius recurrence

CoarseGraining's `CoarseCaccioppoliRadiusRecurrence` fixes the contraction
factor at `1/2` and carries no additive term:

```text
F ρ₁ ≤ (1 / 2 : ℝ) * F ρ₂ + A * Real.rpow (ρ₂ - ρ₁) (-β)
```

The harmonic-approximation boundary row needs both generalizations.  The four
manuscript budgets are an *additive* constant — `affineBudget + forceBudget +
boundaryBudget` do not carry a `(ρ₂ - ρ₁)` price — and the contraction factor
is the free Young parameter of the face-trace step, which is not `1/2`.

This module supplies the budgeted analogue and collapses it through
`iterate_absorb_le_of_sum`, on the same interval `[1/3, 1]` and with the same
`rpow` price, so that the argument's existing radius profiles
(`boundaryCrossScaleEnergyProfile`, and `CoarseCaccioppoliRadiusBoundedAbove`
already proved at `Section6HarmonicApproximation/BoundaryCrossScaleRadius.lean`)
plug in unchanged.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow

open Homogenization Finset

/-- Budgeted, free-contraction analogue of `CoarseCaccioppoliRadiusRecurrence`.
`A` prices the part of the parent budget that scales like `(ρ₂ - ρ₁)^{-β}`;
`B` holds the budgets that carry no radius price. -/
def BudgetedRadiusRecurrence (F : ℝ → ℝ) (theta A B β : ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    F ρ₁ ≤ theta * F ρ₂ + A * Real.rpow (ρ₂ - ρ₁) (-β) + B

/-- The budgeted recurrence generalizes the CoarseGraining one: the existing
fixed-`1/2`, zero-budget interface is the special case. -/
theorem budgetedRadiusRecurrence_of_coarseCaccioppoliRadiusRecurrence
    {F : ℝ → ℝ} {A β : ℝ} (hrec : CoarseCaccioppoliRadiusRecurrence F A β) :
    BudgetedRadiusRecurrence F (1 / 2 : ℝ) A 0 β := by
  intro r1 r2 h1 h2 h3
  have h := hrec h1 h2 h3
  linarith

/-- Rewriting `(tau ^ i) ^ (-β)` as a geometric factor. -/
private theorem rpow_pow_neg {tau beta : ℝ} (htau0 : 0 < tau) (i : ℕ) :
    Real.rpow (tau ^ i) (-beta) = ((Real.rpow tau beta)⁻¹) ^ i := by
  have hpos : (0 : ℝ) ≤ tau := htau0.le
  have e1 : (tau ^ i : ℝ) = Real.rpow tau (i : ℝ) :=
    (Real.rpow_natCast tau i).symm
  have e2 : Real.rpow (Real.rpow tau (i : ℝ)) (-beta)
      = Real.rpow tau ((i : ℝ) * -beta) := (Real.rpow_mul hpos _ _).symm
  have e3 : Real.rpow tau ((i : ℝ) * -beta)
      = Real.rpow tau (-(beta * (i : ℝ))) := by ring_nf
  have e4 : Real.rpow tau (-(beta * (i : ℝ)))
      = (Real.rpow tau (beta * (i : ℝ)))⁻¹ := Real.rpow_neg hpos _
  have e5 : Real.rpow tau (beta * (i : ℝ))
      = Real.rpow (Real.rpow tau beta) (i : ℝ) := Real.rpow_mul hpos _ _
  have e6 : Real.rpow (Real.rpow tau beta) (i : ℝ) = (Real.rpow tau beta) ^ i :=
    Real.rpow_natCast _ i
  rw [e1, e2, e3, e4, e5, e6, inv_pow]

/-- **Budgeted radius iteration.**  A free-contraction recurrence on
`[1/3, 1]` with an additive budget collapses at the inner radius.  This is the
replacement for `coarseCaccioppoli_radius_iteration` whenever the estimate
carries budgets or a contraction factor other than `1/2`. -/
theorem budgetedRadius_iteration
    {F : ℝ → ℝ} {theta A B beta tau : ℝ}
    (hbeta : 0 ≤ beta) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htau0 : 0 < tau) (htau1 : tau < 1)
    (htheta0 : 0 ≤ theta) (hcontract : theta < Real.rpow tau beta)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hrec : BudgetedRadiusRecurrence F theta A B beta) :
    F (1 / 3 : ℝ) ≤
      (1 - theta / Real.rpow tau beta)⁻¹ *
          (A * Real.rpow ((1 - tau) * (2 / 3 : ℝ)) (-beta))
        + (1 - theta)⁻¹ * B := by
  obtain ⟨Mbd, hMbd⟩ := hbounded
  set T : ℝ := Real.rpow tau beta with hTdef
  have hTpos : 0 < T := Real.rpow_pos_of_pos htau0 beta
  have hTle : T ≤ 1 := Real.rpow_le_one htau0.le htau1.le hbeta
  have htheta1 : theta < 1 := lt_of_lt_of_le hcontract hTle
  have hx0 : 0 ≤ theta / T := div_nonneg htheta0 hTpos.le
  have hx1 : theta / T < 1 := (div_lt_one hTpos).mpr hcontract
  set c : ℝ := (1 - tau) * (2 / 3 : ℝ) with hcdef
  have hcpos : 0 < c := by
    have : (0 : ℝ) < 1 - tau := by linarith
    positivity
  refine iterate_absorb_le_of_sum F (fun t => A * Real.rpow t (-beta) + B)
    (by norm_num : (1 / 3 : ℝ) < 1) htau0 htau1 htheta0 htheta1
    (fun r h1 h2 => hMbd h1 h2)
    (fun rho R h1 h2 h3 => by
      have h := hrec h1 h2 h3
      linarith) ?_
  intro k
  -- closed form of the summand
  have hterm : ∀ i : ℕ,
      theta ^ i * (A * Real.rpow ((1 - tau) * tau ^ i * (1 - 1 / 3 : ℝ)) (-beta) + B)
        = (A * Real.rpow c (-beta)) * (theta / T) ^ i + B * theta ^ i := by
    intro i
    have hreorder : (1 - tau) * tau ^ i * (1 - 1 / 3 : ℝ) = c * tau ^ i := by
      rw [hcdef]; ring
    have htaui : (0 : ℝ) ≤ tau ^ i := (pow_pos htau0 i).le
    have hsplit : Real.rpow (c * tau ^ i) (-beta)
        = Real.rpow c (-beta) * Real.rpow (tau ^ i) (-beta) :=
      Real.mul_rpow hcpos.le htaui
    have hgeo : Real.rpow (tau ^ i) (-beta) = ((Real.rpow tau beta)⁻¹) ^ i :=
      rpow_pow_neg htau0 i
    have hdiv : (theta / T) ^ i = theta ^ i * ((Real.rpow tau beta)⁻¹) ^ i := by
      rw [hTdef, div_pow, inv_pow, div_eq_mul_inv]
    rw [hreorder, hsplit, hgeo, hdiv]
    ring
  have hrw : ∑ i ∈ Finset.range k,
        theta ^ i * (A * Real.rpow ((1 - tau) * tau ^ i * (1 - 1 / 3 : ℝ)) (-beta) + B)
      = (A * Real.rpow c (-beta)) * (∑ i ∈ Finset.range k, (theta / T) ^ i)
        + B * (∑ i ∈ Finset.range k, theta ^ i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hterm i
  have hAc : 0 ≤ A * Real.rpow c (-beta) :=
    mul_nonneg hA (Real.rpow_nonneg hcpos.le _)
  have h1 : (A * Real.rpow c (-beta)) * (∑ i ∈ Finset.range k, (theta / T) ^ i)
      ≤ (A * Real.rpow c (-beta)) * (1 - theta / T)⁻¹ :=
    mul_le_mul_of_nonneg_left (geom_partial_le hx0 hx1 k) hAc
  have h2 : B * (∑ i ∈ Finset.range k, theta ^ i) ≤ B * (1 - theta)⁻¹ :=
    mul_le_mul_of_nonneg_left (geom_partial_le htheta0 htheta1 k) hB
  rw [hrw]
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
