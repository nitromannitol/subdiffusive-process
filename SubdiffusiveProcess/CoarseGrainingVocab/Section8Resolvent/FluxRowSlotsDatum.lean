/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsEnergy




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The price's physical scale is nonnegative -/

/-- The part of the local cell price before `W_Q` is nonnegative. -/
theorem fluxRowRieszCellPhysicalScale_nonneg
    {alpha t R sigma fEnergy theta cellSize : ℝ} {graphDistance : ℕ}
    (halpha : 0 ≤ alpha) (ht : 0 < t) (hR : 0 < R) (hcellSize : 0 ≤ cellSize)
    (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta) :
    0 ≤ fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
      graphDistance d := by
  unfold fluxRowRieszCellPhysicalScale
  have h1 : (0 : ℝ) ≤ t⁻¹ := by positivity
  have h2 : (0 : ℝ) ≤ Real.rpow R (2 * sigma) := Real.rpow_nonneg hR.le _
  have h3 : (0 : ℝ) ≤ Real.rpow theta ((graphDistance : ℝ) / 2) :=
    Real.rpow_nonneg htheta _
  have h4 : (0 : ℝ) ≤ cellSize / R := by positivity
  have h5 : (0 : ℝ) ≤ (cellSize / R) ^ (d + 6) := by positivity
  positivity

/-! ## 2. Cells away from the source: the vanishing datum -/

/-- The Gagliardo kernel of the zero field vanishes, hence so does the paper's
fractional seminorm. -/
theorem paperFractionalSeminorm_of_forall_eq_zero (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) {F : Vec d → Vec d}
    (hF : ∀ x, F x = 0) :
    paperFractionalSeminorm Q s p F = 0 := by
  have hker : cubeEuclideanWspKernel s p F = fun _ ↦ 0 := by
    funext z
    simp [cubeEuclideanWspKernel, hF]
  unfold paperFractionalSeminorm Homogenization.cubeEuclideanWspESeminorm
  rw [hker]
  simp

/-- **The datum vanishes on the cell.**

The Gagliardo measure of a triadic cube is carried by `cubeSet Q ×ˢ cubeSet Q`,
so a datum field vanishing on the cell has zero fractional seminorm there.  This
is the form actually available for the manuscript's `g = -∇ψ`: `f` is supported
in `B_R(x₀)`, so on a cell away from the source the datum term is absent. -/
theorem paperFractionalSeminorm_of_eqOn_zero (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) {F : Vec d → Vec d}
    (hF : ∀ x ∈ cubeSet Q, F x = 0) :
    paperFractionalSeminorm Q s p F = 0 := by
  have hmeas : MeasurableSet (cubeSet Q ×ˢ cubeSet Q) :=
    (measurableSet_cubeSet Q).prod (measurableSet_cubeSet Q)
  have hprod : Gagliardo.gagliardoCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) •
        ((volume.prod volume).restrict (cubeSet Q ×ˢ cubeSet Q)) := by
    rw [Gagliardo.gagliardoCubeMeasure, normalizedCubeMeasure, cubeMeasure,
      MeasureTheory.Measure.prod_smul_left, MeasureTheory.Measure.prod_restrict]
  have hae : ∀ᵐ z ∂ Gagliardo.gagliardoCubeMeasure Q,
      z ∈ cubeSet Q ×ˢ cubeSet Q := by
    rw [hprod]
    exact MeasureTheory.Measure.ae_smul_measure
      (MeasureTheory.ae_restrict_mem hmeas) _
  have hker : cubeEuclideanWspKernel s p F =ᵐ[Gagliardo.gagliardoCubeMeasure Q]
      0 := by
    filter_upwards [hae] with z hz
    have h1 : F z.1 = 0 := hF z.1 hz.1
    have h2 : F z.2 = 0 := hF z.2 hz.2
    simp [cubeEuclideanWspKernel, h1, h2]
  unfold paperFractionalSeminorm Homogenization.cubeEuclideanWspESeminorm
  rw [MeasureTheory.eLpNorm_congr_ae hker, MeasureTheory.eLpNorm_zero, mul_zero]

/-- **The datum slot on a cell carrying no source.**

If the recentred datum has zero fractional seminorm on the cell — which is the
manuscript's "the terms containing `f` occur only for `Q ∈ 𝒞`" — then the datum
slot is the trivial inequality. -/
theorem fluxRowSlots_datum_slot_of_seminorm_zero
    {alpha t R sigma fEnergy theta cellSize V scaleFactor : ℝ}
    {graphDistance : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} {F : Vec d → Vec d}
    (halpha : 0 ≤ alpha) (ht : 0 < t) (hR : 0 < R) (hcellSize : 0 ≤ cellSize)
    (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (hzero : paperFractionalSeminorm Q s p F = 0) :
    V * (scaleFactor * (paperFractionalSeminorm Q s p F).toReal) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
        graphDistance d := by
  rw [hzero]
  simpa using
    fluxRowRieszCellPhysicalScale_nonneg (d := d) (graphDistance := graphDistance)
      halpha ht hR hcellSize hfEnergy htheta

/-- The same, from the vanishing of the datum field itself. -/
theorem fluxRowSlots_datum_slot_of_vanishing_field
    {alpha t R sigma fEnergy theta cellSize V scaleFactor : ℝ}
    {graphDistance : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} {F : Vec d → Vec d}
    (halpha : 0 ≤ alpha) (ht : 0 < t) (hR : 0 < R) (hcellSize : 0 ≤ cellSize)
    (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (hF : ∀ x, F x = 0) :
    V * (scaleFactor * (paperFractionalSeminorm Q s p F).toReal) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
        graphDistance d :=
  fluxRowSlots_datum_slot_of_seminorm_zero halpha ht hR hcellSize hfEnergy htheta
    (paperFractionalSeminorm_of_forall_eq_zero Q s p hF)

/-- The datum slot on a cell on which the datum field vanishes. -/
theorem fluxRowSlots_datum_slot_of_eqOn_zero
    {alpha t R sigma fEnergy theta cellSize V scaleFactor : ℝ}
    {graphDistance : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} {F : Vec d → Vec d}
    (halpha : 0 ≤ alpha) (ht : 0 < t) (hR : 0 < R) (hcellSize : 0 ≤ cellSize)
    (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (hF : ∀ x ∈ cubeSet Q, F x = 0) :
    V * (scaleFactor * (paperFractionalSeminorm Q s p F).toReal) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
        graphDistance d :=
  fluxRowSlots_datum_slot_of_seminorm_zero halpha ht hR hcellSize hfEnergy htheta
    (paperFractionalSeminorm_of_eqOn_zero Q s p hF)

/-! ## 3. Cells carrying the source: the reduction -/

/-- **The datum slot at the source.**

`hdatum` is the analytic input — elliptic regularity for the manuscript's `ψ`
followed by `l.local.L2.resolvent`, giving the cell datum seminorm in terms of
the `L²` mass of the solution on the parent cell — `hmass` is the pointwise
graph decay, and `hbudget` is the deterministic constant budget, discharged
exactly as in `fluxRowSlots_energy_budget_of_smallness`. -/
theorem fluxRowSlots_datum_slot_of_inputs
    {alpha t R sigma fEnergy theta cellSize D N mass V : ℝ}
    {graphDistance : ℕ}
    (hN : 0 ≤ N) (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (hdatum : V * D ^ 2 ≤ N * mass)
    (hmass : mass ≤ Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy)
    (hbudget : N ≤ alpha * t⁻¹ * Real.rpow R (2 * sigma) *
      (cellSize / R) ^ (d + 6)) :
    V * D ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
        graphDistance d := by
  have hthetapow : 0 ≤ Real.rpow theta ((graphDistance : ℝ) / 2) :=
    Real.rpow_nonneg htheta _
  have hprod : 0 ≤ Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy :=
    mul_nonneg hthetapow hfEnergy
  have hstep1 : V * D ^ 2 ≤
      N * (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy) := by
    refine hdatum.trans ?_
    exact mul_le_mul_of_nonneg_left hmass hN
  have hstep2 : N * (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy) ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
        graphDistance d := by
    have := mul_le_mul_of_nonneg_right hbudget hprod
    calc N * (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy) ≤ _ := this
      _ = fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
            graphDistance d := by
          unfold fluxRowRieszCellPhysicalScale; ring
  exact hstep1.trans hstep2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
