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

namespace SubdiffusiveProcess.Paper

/--
- Supplier in_common_scale_coupling fixes the common bilateral product law; rescaled reads exactly g_(i-N)(3^(-N)y) from the same sample.
- The rescaled nonnegative-index family has the law of the original nonnegative-index family, not independent new samples chosen at each cutoff.
- A cell of ultraviolet depth k and centre z becomes the actual physical cube with centre 3^N z and side 3^(N-k).
- Each prefix uses one N for every entry: its indices are exactly N-k-D through N-k, including both endpoints.
- Scope: no assertion is made for a prefix assembled from different cutoffs. The paper's Bernoulli example X_(n,N)=xi_(n+N), N_n=J-n illustrates the excluded operation, whose entries all become xi_J. This is a scope restriction, not an additional probabilistic conclusion.
-/
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

end SubdiffusiveProcess.Paper
