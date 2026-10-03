module

public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess Set
open scoped ENNReal

noncomputable section

namespace Paper



def physical_scale_dictionary
    (d : Nat)
    [MeasurableSpace C(SpatialCoordinates d, Real)]
    [BorelSpace C(SpatialCoordinates d, Real)]
    (nu : ProbabilityMeasure C(SpatialCoordinates d, Real))
    (rescaled : Nat → BilateralField d → Nat → C(SpatialCoordinates d, Real))
    (physicalCube : Nat → Nat → SpatialCoordinates d → Set (SpatialCoordinates d))
    («prefix» : Nat → Nat → Nat → Finset Int) : Prop :=
  (∀ N omega i y,
    rescaled N omega i y =
      omega ((i : Int) - (N : Int)) ((3 : Real) ^ (-(N : Real)) • y)) ∧
  (∀ N, Measure.map (rescaled N) (commonScaleLaw d nu).toMeasure =
    Measure.map (fun omega : BilateralField d => fun i : Nat => omega (i : Int))
      (commonScaleLaw d nu).toMeasure) ∧
  (∀ N k z, physicalCube N k z =
    Metric.ball (((3 : Real) ^ (N : Real)) • z)
      (((3 : Real) ^ ((N : Real) - (k : Real))) / 2)) ∧
  (∀ N k D, «prefix» N k D =
    Finset.Icc ((N : Int) - (k : Int) - (D : Int)) ((N : Int) - (k : Int))) ∧
  (∀ N k D j, j ∈ «prefix» N k D ↔
    ∃ i : Nat, k ≤ i ∧ i ≤ k + D ∧ j = (N : Int) - (i : Int))

end Paper
