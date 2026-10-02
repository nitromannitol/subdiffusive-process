import SubdiffusiveProcess.Paper.primitive_scores
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Geometry.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory SubdiffusiveProcess Set Topology
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.Lane3
open scoped BigOperators ENNReal NNReal

namespace Paper



def coherent_score_attachment
    (d : Nat) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, Real)]
    [BorelSpace C(SpatialCoordinates d, Real)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, Real))
    (N : Nat) (omega : BilateralField d)
    (s eps : Real) (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (F P R D : Nat → Vec d → ENNReal) (Z : Nat → Vec d → Real)
    (good : Nat → Vec d → Prop)
    (k : Nat) (z : SpatialCoordinates d)
    (pre : Nat → Finset Nat)
    (physicalCell q : Set (SpatialCoordinates d))
    (coeffPhysical : SpatialCoordinates d → Real) (sRef : Real) : Prop :=
  k ≤ N ∧
  (∀ (i : Nat) (y : Vec d),
    eta i y = omega ((i : Int) - (N : Int))
      (((3 : Real) ^ (-(N : Int))) • y)) ∧
  primitive_scores d M s eps eta F P R D Z good ∧
  (let r : Real := (3 : Real) ^ (-(k : Int))
   q = Metric.ball z (r / 2)) ∧
  physicalCell = {y | ((3 : Real) ^ (-(N : Int))) • y ∈ q} ∧
  physicalCell =
    Metric.ball (((3 : Real) ^ N) • z)
      (((3 : Real) ^ ((N : Int) - (k : Int))) / 2) ∧
  (∀ (D₀ : Nat), D₀ ≤ N - k →
    pre D₀ = Finset.Icc (N - k - D₀) (N - k)) ∧
  (∀ y,
    coeffPhysical y =
      cutoffCoefficient M H omega N (((3 : Real) ^ (-(N : Int))) • y)) ∧
  (∀ y,
    coeffPhysical y =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M N eta y *
          Real.exp (H omega (((3 : Real) ^ (-(N : Int))) • y))) ∧
  (let kappa : Nat → Real := fun J =>
      Real.exp (((J : Real) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
   sRef = (kappa (N - k) / kappa N) *
     Real.exp (H omega z +
       ∑ j ∈ Finset.range k, omega (-(j : Int)) z))

end Paper
