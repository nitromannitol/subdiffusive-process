module

public import SubdiffusiveProcess.MacroAllCube.ResidualLaw
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.CutoffPotential

@[expose] public section

open MeasureTheory
open SubdiffusiveProcess
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess.MacroAllCube
variable {d : ℕ}

/-- The finitely many ultraviolet layers moved into the infrared part by
normalizing a small root cube. -/
def lowAnchor (k : ℕ) (om : BilateralField d) : ℝ :=
  ∑ i ∈ Finset.range k, om (-(Int.ofNat i)) 0

theorem infraredPartialSum_residualShift (r : ℝ) (k L : ℕ)
    (om : BilateralField d) (x : SpatialCoordinates d) :
    infraredPartialSum (residualShift r k om) (k + L) x =
      infraredPartialSum om L (r • x) +
        (∑ i ∈ Finset.range k, om (-(Int.ofNat i)) (r • x)) - lowAnchor k om := by
  simp only [infraredPartialSum, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.sub_apply, ContinuousMap.const_apply,
    residualShift_apply, smul_zero, lowAnchor]
  rw [Finset.sum_range_add]
  have hlo :
      (∑ i ∈ Finset.range k,
          (om (Int.ofNat (i + 1) - (k : ℤ)) (r • x) -
            om (Int.ofNat (i + 1) - (k : ℤ)) 0)) =
        ∑ i ∈ Finset.range k,
          (om (-(Int.ofNat i)) (r • x) - om (-(Int.ofNat i)) 0) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik := Finset.mem_range.1 hi
    have heq : Int.ofNat (k - 1 - i + 1) - (k : ℤ) = -(Int.ofNat i) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [heq]
  have hhi :
      (∑ i ∈ Finset.range L,
          (om (Int.ofNat (k + i + 1) - (k : ℤ)) (r • x) -
            om (Int.ofNat (k + i + 1) - (k : ℤ)) 0)) =
        ∑ i ∈ Finset.range L,
          (om (Int.ofNat (i + 1)) (r • x) - om (Int.ofNat (i + 1)) 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show Int.ofNat (k + i + 1) - (k : ℤ) = Int.ofNat (i + 1) by
      simp only [Int.ofNat_eq_natCast]
      omega]
  rw [hlo, hhi, Finset.sum_sub_distrib]
  ring

/-- Exact physical potential identity, with the cutoff written `N+k` so
that no natural subtraction is hidden. The infrared identity is supplied
by taking the limit in `infraredPartialSum_residualShift`. -/
theorem cutoffPotential_residualShift
    (H Hs : BilateralField d → C(SpatialCoordinates d, ℝ))
    (r : ℝ) (k N : ℕ) (om : BilateralField d)
    (hIR : ∀ x : SpatialCoordinates d,
      Hs (residualShift r k om) x = H om (r • x) +
        (∑ i ∈ Finset.range k, om (-(Int.ofNat i)) (r • x)) - lowAnchor k om)
    (x : SpatialCoordinates d) :
    cutoffPotential H om (N + k) (r • x) =
      cutoffPotential Hs (residualShift r k om) N x + lowAnchor k om := by
  unfold cutoffPotential
  rw [hIR x, show N + k + 1 = k + (N + 1) by omega,
    Finset.sum_range_add]
  have hhi :
      (∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat (k + i))) (r • x)) =
        ∑ i ∈ Finset.range (N + 1), residualShift r k om (-(Int.ofNat i)) x := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [residualShift_apply]
    rw [show -(Int.ofNat (k + i)) = -(Int.ofNat i) - (k : ℤ) by
      simp only [Int.ofNat_eq_natCast]
      omega]
  rw [hhi]
  ring

/-- The scalar normalization price after a cutoff shift. The only
unresolved model-dependent factor is the displayed homogenized ratio. -/
theorem normalized_coefficient_shift (aOld aNew P A tau : ℝ)
    (haNew : aNew ≠ 0) (k N : ℕ) :
    aOld⁻¹ * Real.exp (P + A - ((N + k : ℕ) + 1 : ℝ) * tau) =
      (aNew / aOld * Real.exp (A - (k : ℝ) * tau)) *
        (aNew⁻¹ * Real.exp (P - ((N : ℝ) + 1) * tau)) := by
  have he : Real.exp (A - (k : ℝ) * tau) *
      Real.exp (P - ((N : ℝ) + 1) * tau) =
      Real.exp (P + A - ((N + k : ℕ) + 1 : ℝ) * tau) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [← he]
  simp only [div_eq_mul_inv]
  calc
    aOld⁻¹ * (Real.exp (A - (k : ℝ) * tau) *
        Real.exp (P - ((N : ℝ) + 1) * tau)) =
        aOld⁻¹ * (aNew * aNew⁻¹) *
          (Real.exp (A - (k : ℝ) * tau) *
            Real.exp (P - ((N : ℝ) + 1) * tau)) := by
      rw [mul_inv_cancel₀ haNew, mul_one]
    _ = _ := by ring


end SubdiffusiveProcess.MacroAllCube



