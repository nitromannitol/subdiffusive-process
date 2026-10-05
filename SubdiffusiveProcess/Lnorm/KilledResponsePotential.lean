module

public import SubdiffusiveProcess.Lnorm.RegroupedResponseCompactness
public import SubdiffusiveProcess.ResponseMoments.ResponseInstances

@[expose] public section

/-! The positive-response proxy for a volume source is exactly the actual cutoff inverse response.
This identity does not supply moment bounds or compactness. -/

open MeasureTheory TopologicalSpace
open _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity

noncomputable section
namespace SubdiffusiveProcess.Lnorm

/-- Evaluating the source proxy recovers the inverse response for the actual cutoff coefficient. -/
theorem potentialResponseOriginal_inverse
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (L : S.space →L[ℝ] ℝ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d) :
    potentialResponseOriginal z r hr (inverseResponseData S L) M H N omega =
      inverseResponse S (cutoffPositiveCoefficient M H omega N z hr) L := by
  change inverseResponse S (expPotentialCoefficient (proxy_pot (H omega) M N omega z r hr)) L = _
  rw [← proxy_pot_eq_coefficient M H N omega z r hr]

end SubdiffusiveProcess.Lnorm
