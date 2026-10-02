/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsCaccioppoli
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsSizeArithmetic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DirichletPrebalance
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TriadicMeanComparison




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.Frozen.Section8
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Cell volumes -/



theorem volume_translatedCube_toReal_eq_cubeVolume (k : ℤ) (z : Vec d) :
    (volume (translatedCube d k z)).toReal = cubeVolume (originCube d k) := by
  rw [Section6BoundedMultiplier.volume_translatedCube_toReal,
    cubeVolume_eq_pow_scale]
  rfl

/-! ## 1b. Real readout of the Section 6 prebalance at the flux-row orders -/

/-- **The Section 6 prebalance, read as a real inequality at the flux row's
fractional orders.**

`weightedLocalSymmetricEnergyLp_two_le_realBound` with
`s1 = 3σ/4`, `s = σ` (gap `σ/4 > 0`) and the parent bound taken at its own
value.  This is the input `hSle` of `fluxRowSlots_energy_slot_of_inputs`. -/
theorem fluxRowSlots_weightedEnergy_toReal_le
    [NeZero d] {m n : ℤ} (hn : n ≤ m)
    (a : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
    (u0 : H1Function (openCubeSet (originCube d m)))
    {sigma : ℝ} (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) :
    (weightedLocalSymmetricEnergyLp (originCube d m) n hn a u0
        (fluxRowLocalLowerOrder sigma hsigma) (fluxRowLocalOrder sigma hsigma)
        FiniteLpExponent.two).toReal ≤
      Section6Dirichlet.dirichletWeightedEnergyFactor (3 * sigma / 4) sigma *
        (localSymmetricEnergyENorm (originCube d m) a u0).toReal := by
  have hgap : 0 < (fluxRowLocalOrder sigma hsigma).1 -
      (fluxRowLocalLowerOrder sigma hsigma).1 := by
    simp only [fluxRowLocalOrder, fluxRowLocalLowerOrder]
    nlinarith [hsigma.1, hsigma.2]
  have hparent : localSymmetricEnergyENorm (originCube d m) a u0 ≤
      ENNReal.ofReal (localSymmetricEnergyENorm (originCube d m) a u0).toReal := by
    rw [ENNReal.ofReal_toReal (localSymmetricEnergyENorm_ne_top _ a u0)]
  have hmain := Section6Dirichlet.weightedLocalSymmetricEnergyLp_two_le_realBound
    (originCube d m) n hn a u0 (fluxRowLocalLowerOrder sigma hsigma)
    (fluxRowLocalOrder sigma hsigma) hgap hparent
  have hnn : 0 ≤ Section6Dirichlet.dirichletWeightedEnergyFactor
      (fluxRowLocalLowerOrder sigma hsigma).1 (fluxRowLocalOrder sigma hsigma).1 *
      (localSymmetricEnergyENorm (originCube d m) a u0).toReal :=
    mul_nonneg (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
      ENNReal.toReal_nonneg
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
  rwa [ENNReal.toReal_ofReal hnn] at this

/-! ## 2. The energy slot from its four inputs -/

/-- **The energy slot of `e.whole.resolvent.local.flux`.**

`V` is the cell volume, `S` the weighted energy read as a real, `S0` the plain
normalized symmetric energy, `K` the Section 6 weighting factor, `Cc` the
Caccioppoli constant and `mass` the `L²` mass of the solution on the parent
cell.  With the four inputs

* `hSle`   : `S ≤ K * S0` (Section 6 prebalance),
* `hcacc`  : `V * S0² ≤ Cc * mass` (the Caccioppoli step),
* `hmass`  : `mass ≤ θ^{dist/2} * fEnergy` (the pointwise graph decay), and
* `hbudget`: the deterministic constant budget,

the slot holds verbatim. -/
theorem fluxRowSlots_energy_slot_of_inputs
    {alpha t R sigma fEnergy theta cellSize S S0 K Cc mass lambdaInv V : ℝ}
    {graphDistance : ℕ}
    (halpha : 0 < alpha) (hV : 0 ≤ V) (hS : 0 ≤ S) (hCc : 0 ≤ Cc) (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (hSle : S ≤ K * S0)
    (hcacc : V * S0 ^ 2 ≤ Cc * mass)
    (hmass : mass ≤ Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy)
    (hbudget : alpha * K ^ 2 * Cc ≤
      alpha * t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6) *
        (1 + (alpha * lambdaInv) ^ 2)) :
    V * (Real.sqrt alpha * S) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
          graphDistance d * (1 + (alpha * lambdaInv) ^ 2) := by
  have hsqrt : Real.sqrt alpha ^ 2 = alpha := Real.sq_sqrt halpha.le
  have hthetapow : 0 ≤ Real.rpow theta ((graphDistance : ℝ) / 2) :=
    Real.rpow_nonneg htheta _
  have hstep1 : V * (Real.sqrt alpha * S) ^ 2 ≤ alpha * K ^ 2 * (V * S0 ^ 2) := by
    have hsq : S ^ 2 ≤ (K * S0) ^ 2 := by nlinarith [hS, hSle]
    have : V * (Real.sqrt alpha * S) ^ 2 = alpha * (V * S ^ 2) := by
      rw [mul_pow, hsqrt]; ring
    rw [this]
    have : V * S ^ 2 ≤ K ^ 2 * (V * S0 ^ 2) := by nlinarith [hV, hsq]
    nlinarith [halpha.le, this]
  have hstep2 : alpha * K ^ 2 * (V * S0 ^ 2) ≤ alpha * K ^ 2 * (Cc * mass) := by
    have hnn : 0 ≤ alpha * K ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hcacc hnn
  have hstep3 : alpha * K ^ 2 * (Cc * mass) ≤
      alpha * K ^ 2 * Cc *
        (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy) := by
    have hnn : 0 ≤ alpha * K ^ 2 * Cc := by positivity
    have := mul_le_mul_of_nonneg_left hmass hnn
    calc alpha * K ^ 2 * (Cc * mass) = alpha * K ^ 2 * Cc * mass := by ring
      _ ≤ _ := this
  have hstep4 : alpha * K ^ 2 * Cc *
        (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy) ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
          graphDistance d * (1 + (alpha * lambdaInv) ^ 2) := by
    have hnn : 0 ≤ Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy :=
      mul_nonneg hthetapow hfEnergy
    have := mul_le_mul_of_nonneg_right hbudget hnn
    calc alpha * K ^ 2 * Cc *
          (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy) ≤ _ := this
      _ = fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
            graphDistance d * (1 + (alpha * lambdaInv) ^ 2) := by
          unfold fluxRowRieszCellPhysicalScale; ring
  linarith

/-! ## 3. Discharging the constant budget -/

/-- **The constant budget from the manuscript's smallness of `t`.**

Because a stopping cell has side `size(Q) ≥ R` the relative size is at least
one, so `(size(Q)/R)^{d+6} ≥ 1`, and `1 + (ahom λ⁻¹)² ≥ 1`; the budget therefore
reduces to the manuscript's smallness condition on `t`
(`K² Cc ≤ t⁻¹ R^{2σ}`, i.e. `t Λ size(Q)⁻² ≲ R^{2σ}`), which is the
`t ℓ⁻² Λ` smallness of `l.local.L2.resolvent`. -/
theorem fluxRowSlots_energy_budget_of_smallness
    {alpha t R sigma cellSize K Cc lambdaInv : ℝ}
    (halpha : 0 < alpha) (ht : 0 < t) (hR : 0 < R) (hRS : R ≤ cellSize)
    (hsmall : K ^ 2 * Cc ≤ t⁻¹ * Real.rpow R (2 * sigma)) :
    alpha * K ^ 2 * Cc ≤
      alpha * t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6) *
        (1 + (alpha * lambdaInv) ^ 2) := by
  have hratio : 1 ≤ cellSize / R := fluxRowSlots_one_le_ratio hR hRS
  have hpow : (1 : ℝ) ≤ (cellSize / R) ^ (d + 6) := one_le_pow₀ hratio
  have hW : (1 : ℝ) ≤ 1 + (alpha * lambdaInv) ^ 2 := by nlinarith [sq_nonneg (alpha * lambdaInv)]
  have hbase : alpha * K ^ 2 * Cc ≤ alpha * (t⁻¹ * Real.rpow R (2 * sigma)) := by
    nlinarith [halpha.le, hsmall]
  have hnn : 0 ≤ alpha * (t⁻¹ * Real.rpow R (2 * sigma)) := by
    have h1 : (0 : ℝ) ≤ t⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ Real.rpow R (2 * sigma) := Real.rpow_nonneg hR.le _
    positivity
  calc alpha * K ^ 2 * Cc ≤ alpha * (t⁻¹ * Real.rpow R (2 * sigma)) := hbase
    _ ≤ alpha * (t⁻¹ * Real.rpow R (2 * sigma)) *
          ((cellSize / R) ^ (d + 6) * (1 + (alpha * lambdaInv) ^ 2)) := by
        have hone : (1 : ℝ) ≤ (cellSize / R) ^ (d + 6) *
            (1 + (alpha * lambdaInv) ^ 2) := by nlinarith [hpow, hW]
        exact le_mul_of_one_le_right hnn hone
    _ = alpha * t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6) *
          (1 + (alpha * lambdaInv) ^ 2) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
