import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.InfraredCharacterization

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}



def weighted_killed_form (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (omega : BilateralField d)
    (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (arho : PositiveCoefficient (centeredCube z r hr))
    (rho : SpatialCoordinates d → ℝ)
    (hrhocont : ContinuousOn rho
      (closure ((centeredCube z r hr) : Set (SpatialCoordinates d))))
    (hrhopos : ∀ x ∈ closure ((centeredCube z r hr) : Set (SpatialCoordinates d)),
      0 < rho x)
    (Eweight : S.space → S.space → ℝ)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)) :
    Prop :=
  let a := Lane4.cutoffPositiveCoefficient M H omega N z hr
  (arho.val
      =ᵐ[volume.restrict ((centeredCube z r hr) : Set (SpatialCoordinates d))]
        (fun x => rho x * a.val x)) ∧
  (∀ u v : S.space, Eweight u v =
    ∫ x in ((centeredCube z r hr) : Set (SpatialCoordinates d)),
      rho x * (a.val x * ∑ i : Fin d, (u.val.2 i x) * (v.val.2 i x))) ∧
  (∀ f : DomainL2 (centeredCube z r hr),
    G f =
      (responseSolution S arho
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)

end Paper
