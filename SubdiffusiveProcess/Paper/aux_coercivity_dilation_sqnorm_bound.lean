module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.gagliardo_dilation_scaling

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Proof-step fine child: combine the two normalized square-norm summands. -/
theorem aux_coercivity_dilation_sqnorm_bound
    (d k : ℕ) (hd : 2 ≤ d) (z z' : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1)
    (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin k → DomainL2 (centeredCube z r hr))
    (g : Fin k → DomainL2 (centeredCube z' 1 h1)) (R : ℝ)
    (hsemi : cubeFractionalVecSeminormSq hd z r hr s f =
      R * cubeFractionalVecSeminormSq hd z' 1 h1 s g)
    (hL2 : (∑ i : Fin k, ‖f i‖ ^ 2) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (∑ i : Fin k, ‖g i‖ ^ 2) /
        volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d)))
    (hR : 1 ≤ R) :
    cubeFractionalVecSqNorm hd z r hr s f ≤
      R * cubeFractionalVecSqNorm hd z' 1 h1 s g := by
  rw [cubeFractionalVecSqNorm, cubeFractionalVecSqNorm, hsemi, hL2]
  have hvol : 0 < volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) :=
    centeredCube_volume_pos z' h1
  have hnonneg :
      0 ≤ (∑ i : Fin k, ‖g i‖ ^ 2) /
        volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) := by
    exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg ‖g i‖)) hvol.le
  nlinarith

end SubdiffusiveProcess.Paper
