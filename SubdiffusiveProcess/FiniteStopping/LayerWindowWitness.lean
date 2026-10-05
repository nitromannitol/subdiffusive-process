module

public import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison

@[expose] public section

/-! This module records original-field failure windows and the exact trace-window family;
it does not assert the existence of either family. -/

open MeasureTheory Set SubdiffusiveProcess
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.FiniteStopping

/-- Failure is almost surely covered by original-layer measurable windows of the prescribed rate. -/
def has_layer_windows {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) (k : ℕ) (B : ℝ)
    (Good : BilateralField d → Prop) : Prop :=
  ∃ W : ℕ+ → Set (BilateralField d),
    (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
      ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).domRestrict)
      (inferInstance : MeasurableSpace
        ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
          C(SpatialCoordinates d, ℝ)))] (W h)) ∧
    (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-B * (h : ℝ)))) ∧
    (∀ᵐ omega ∂P, ¬ Good omega → omega ∈ ⋃ h : ℕ+, W h)

/-- The exact normalized trace comparison has failure windows after one remaining-cutoff threshold. -/
def has_trace_windows {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (alpha B : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ m0 : ℕ,
    ∃ TraceClose : ℕ → ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop,
      (∀ N M k z omega, TraceClose N M k z omega ↔
        trace_close model H alpha eta N M k z omega) ∧
      ∀ (N M k : ℕ) (z : SpatialCoordinates d),
        k ≤ N → k ≤ M → m0 ≤ N - k → m0 ≤ M - k →
        has_layer_windows (chaosSampleLaw model).toMeasure k B (TraceClose N M k z)

end SubdiffusiveProcess.FiniteStopping
