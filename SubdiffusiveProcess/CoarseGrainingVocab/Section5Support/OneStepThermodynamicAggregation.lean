import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellMomentAggregation

/-!
# Thermodynamic closure for the one-step cell inequalities

The one-step proof first obtains a finite-volume inequality on the interior
cells and then discards a boundary layer whose normalized contribution tends
to zero.  This file packages that order-limit step without baking any PDE or
probability input into it.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Filter

/-- A pointwise finite-volume inequality passes to the thermodynamic limits
of both sides. -/
theorem oneStep_limit_le_of_finiteVolume_le
    {energy bound : ℕ → ℝ} {energyInf boundInf : ℝ}
    (henergy : Tendsto energy atTop (nhds energyInf))
    (hbound : Tendsto bound atTop (nhds boundInf))
    (hle : ∀ K : ℕ, energy K ≤ bound K) :
    energyInf ≤ boundInf :=
  le_of_tendsto_of_tendsto henergy hbound
    (Filter.Eventually.of_forall hle)

/-- The source's boundary-layer passage: if the full finite-volume energy is
bounded by the interior-cell expression plus a boundary contribution tending
to zero, its thermodynamic limit is bounded by the interior limit. -/
theorem oneStep_limit_le_of_interior_add_boundary
    {energy interior boundary : ℕ → ℝ} {energyInf interiorInf : ℝ}
    (henergy : Tendsto energy atTop (nhds energyInf))
    (hinterior : Tendsto interior atTop (nhds interiorInf))
    (hboundary : Tendsto boundary atTop (nhds 0))
    (hle : ∀ K : ℕ, energy K ≤ interior K + boundary K) :
    energyInf ≤ interiorInf := by
  have hrhs : Tendsto (fun K => interior K + boundary K) atTop
      (nhds (interiorInf + 0)) := hinterior.add hboundary
  simpa only [add_zero] using oneStep_limit_le_of_finiteVolume_le
    henergy hrhs hle

/-- A constant interior budget survives the thermodynamic limit after the
vanishing boundary layer is removed. -/
theorem oneStep_limit_le_of_uniform_interior_bound
    {energy interior boundary : ℕ → ℝ} {energyInf budget : ℝ}
    (henergy : Tendsto energy atTop (nhds energyInf))
    (hboundary : Tendsto boundary atTop (nhds 0))
    (hle : ∀ K : ℕ, energy K ≤ interior K + boundary K)
    (hinterior : ∀ K : ℕ, interior K ≤ budget) :
    energyInf ≤ budget := by
  have hfinite : ∀ K : ℕ, energy K ≤ budget + boundary K := by
    intro K
    exact (hle K).trans (add_le_add (hinterior K) le_rfl)
  have hrhs : Tendsto (fun K => budget + boundary K) atTop
      (nhds (budget + 0)) := tendsto_const_nhds.add hboundary
  simpa only [add_zero] using oneStep_limit_le_of_finiteVolume_le
    henergy hrhs hfinite

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
