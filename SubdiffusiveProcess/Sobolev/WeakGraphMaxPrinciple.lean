module

public import SubdiffusiveProcess.Sobolev.HarmonicityTransfer
public import SubdiffusiveProcess.Sobolev.HarmonicMaxPrincipleClosure
public import Mathlib.Topology.Sets.Opens

@[expose] public section




open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization
open TopologicalSpace

namespace SubdiffusiveProcess

/-- Continuous representatives of weakly harmonic graph elements inherit a
comparison bound from matched H10 traces and a bounded comparison pair. -/
theorem abs_sub_le_on_closure_of_weakSobolevGraph_harmonic
    {d : ℕ} [NeZero d] {Ω : Opens (SpatialCoordinates d)}
    (hΩ : IsOpenBoundedConvexDomain (Ω : Set (SpatialCoordinates d)))
    (v1 v2 : weakSobolevGraph Ω)
    (hv1 : ∀ psi : killedSobolevGraph Ω,
      inner ℝ (sobolevGradient v1.val)
        (subspaceGradient (killedSobolevGraph Ω) psi) = 0)
    (hv2 : ∀ psi : killedSobolevGraph Ω,
      inner ℝ (sobolevGradient v2.val)
        (subspaceGradient (killedSobolevGraph Ω) psi) = 0)
    (phi1 phi2 : H1Function (Ω : Set (SpatialCoordinates d)))
    (hzero1 : ∀ w : H1Function (Ω : Set (SpatialCoordinates d)),
      (w : SpatialCoordinates d → ℝ) = (fun x => v1.val.1 x) →
        HasZeroTraceDifferenceOn (Ω : Set (SpatialCoordinates d)) w phi1)
    (hzero2 : ∀ w : H1Function (Ω : Set (SpatialCoordinates d)),
      (w : SpatialCoordinates d → ℝ) = (fun x => v2.val.1 x) →
        HasZeroTraceDifferenceOn (Ω : Set (SpatialCoordinates d)) w phi2)
    {C : ℝ} (hC : 0 ≤ C)
    (hphi : ∀ x ∈ (Ω : Set (SpatialCoordinates d)),
      |phi1.toFun x - phi2.toFun x| ≤ C)
    (V1 V2 : SpatialCoordinates d → ℝ)
    (hV1 : ContinuousOn V1 (closure (Ω : Set (SpatialCoordinates d))))
    (hV2 : ContinuousOn V2 (closure (Ω : Set (SpatialCoordinates d))))
    (hrep1 : ((v1 : SobolevData Ω).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))] V1)
    (hrep2 : ((v2 : SobolevData Ω).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))] V2) :
    ∀ x ∈ closure (Ω : Set (SpatialCoordinates d)), |V1 x - V2 x| ≤ C := by
  obtain ⟨w1, hw1val, hw1harm⟩ :=
    isWeaklyHarmonicOn_of_weakSobolevGraph_harm v1 hv1
  obtain ⟨w2, hw2val, hw2harm⟩ :=
    isWeaklyHarmonicOn_of_weakSobolevGraph_harm v2 hv2
  have hz1 := hzero1 w1 hw1val
  have hz2 := hzero2 w2 hw2val
  have hrep1' : w1.toFun =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] V1 := by
    filter_upwards [hrep1] with x hx
    exact (congrFun hw1val x).trans hx
  have hrep2' : w2.toFun =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] V2 := by
    filter_upwards [hrep2] with x hx
    exact (congrFun hw2val x).trans hx
  exact abs_sub_le_on_closure_of_isWeaklyHarmonicOn hΩ w1 w2 hw1harm hw2harm
    phi1 phi2 hz1 hz2 hC hphi V1 V2 hV1 hV2 hrep1' hrep2'

end SubdiffusiveProcess
