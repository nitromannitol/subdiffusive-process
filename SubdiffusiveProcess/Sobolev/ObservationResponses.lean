module

public import SubdiffusiveProcess.Geometry.TriadicObservationResidual
public import SubdiffusiveProcess.Sobolev.FoldedDefect
public import SubdiffusiveProcess.Sobolev.TriadicDefectSup

@[expose] public section

/-! # Actual response data on observation descendants

Ordinary Poincare and compact-root coefficients are transported along the
proved equality between global descendants and local observation cubes.
The fold itself is still defined on the single original compact root.
-/
open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- Identical actual domains give identical compact-potential defects, independently of proof witnesses. -/
theorem affineDiagonalDefect_compactPotential_domain_eq
    {U Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (U : Set (SpatialCoordinates d)))]
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (h : U = Ω) (hU : Bornology.IsBounded (U : Set (SpatialCoordinates d)))
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvU : 0 < volume.real (U : Set (SpatialCoordinates d)))
    (hvΩ : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hDU : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph U,
      ‖(u : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) u‖)
    (hDΩ : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (hNU : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph U,
      ‖(u : SobolevData U).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph U) u‖)
    (hNΩ : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) u‖)
    (K : Compacts (SpatialCoordinates d)) (g : C(K, ℝ)) (p : Fin d → ℝ) :
    affineDiagonalDefect hU hvU hDU hNU (expPotentialCoefficient (compactPotentialLp K g)) p =
      affineDiagonalDefect hΩ hvΩ hDΩ hNΩ (expPotentialCoefficient (compactPotentialLp K g)) p := by
  cases h
  rfl

/-- Killed Poincare transports along equality of the actual open domains. -/
theorem killedPoincare_domain_eq {U Ω : Opens (SpatialCoordinates d)} (h : U = Ω)
    (hD : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph U,
      ‖(u : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) u‖) :
    ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖ := by
  cases h
  exact hD

/-- Mean-zero Poincare transports along equality of actual finite-volume domains. -/
theorem meanZeroPoincare_domain_eq {U Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (U : Set (SpatialCoordinates d)))]
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))] (h : U = Ω)
    (hN : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph U,
      ‖(u : SobolevData U).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph U) u‖) :
    ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) u‖ := by
  cases h
  exact hN

variable (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
variable
  (hD : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)
  (hN : ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
    ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
      ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
      K * ‖subspaceGradient (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖)

include hD in
/-- Ordinary killed Poincare on the original grid supplies it on every local observation descendant. -/
theorem observation_killedPoincare (N : ℕ) (k : OddGridIndex d (triadicHalf N))
    (J : ℕ) (l : OddGridIndex d (triadicHalf J)) :
    ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
      (oddGridCell (oddGridCenter z r (triadicHalf N) k)
        (r / (2 * (triadicHalf N : ℝ) + 1)) (div_pos hr (by positivity)) (triadicHalf J) l),
      ‖(u : SobolevData (oddGridCell (oddGridCenter z r (triadicHalf N) k)
        (r / (2 * (triadicHalf N : ℝ) + 1)) (div_pos hr (by positivity)) (triadicHalf J) l)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (oddGridCell (oddGridCenter z r (triadicHalf N) k)
        (r / (2 * (triadicHalf N : ℝ) + 1)) (div_pos hr (by positivity)) (triadicHalf J) l)) u‖ := by
  exact killedPoincare_domain_eq (triadicDescendant_cell z hr N J k l)
    (hD (N + J) (triadicDescendant N J k l))

include hN in
/-- Ordinary mean-zero Poincare is routed to the same literal local descendants. -/
theorem observation_meanZeroPoincare (N : ℕ) (k : OddGridIndex d (triadicHalf N))
    (J : ℕ) (l : OddGridIndex d (triadicHalf J)) :
    ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph
      (oddGridCell (oddGridCenter z r (triadicHalf N) k)
        (r / (2 * (triadicHalf N : ℝ) + 1)) (div_pos hr (by positivity)) (triadicHalf J) l),
      ‖(u : SobolevData (oddGridCell (oddGridCenter z r (triadicHalf N) k)
        (r / (2 * (triadicHalf N : ℝ) + 1)) (div_pos hr (by positivity)) (triadicHalf J) l)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (oddGridCell (oddGridCenter z r (triadicHalf N) k)
        (r / (2 * (triadicHalf N : ℝ) + 1)) (div_pos hr (by positivity)) (triadicHalf J) l)) u‖ := by
  exact meanZeroPoincare_domain_eq (triadicDescendant_cell z hr N J k l)
    (hN (N + J) (triadicDescendant N J k l))

/-- Each actual locally retained folded response is bounded by the global original-grid supremum. -/
theorem affineDiagonalDefect_observation_retained_le (hd : 0 < d) (N J : ℕ)
    (k : OddGridIndex d (triadicHalf N)) (I P : Finset (Fin d))
    (g : C(closedCube z r hr, ℝ))
    {l : OddGridIndex d (triadicHalf (J + 1))}
    (hl : l ∈ triadicRetainedLabels J (triadicObservationPlanes N I k))
    {p : Fin d → ℝ} (hp : (∑ i : Fin d, (p i)^2) = 1) :
    affineDiagonalDefect (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
      (observation_killedPoincare z hr hD N k (J + 1) l)
      (observation_meanZeroPoincare z hr hN N k (J + 1) l)
      (expPotentialCoefficient (compactPotentialLp (closedCube z r hr)
        (g.comp (coordinateFoldOnCube z hr I P)))) p ≤
    triadicDefectSup z hr hD hN
      (expPotentialCoefficient (compactPotentialLp (closedCube z r hr) g)) hd (N + (J + 1)) := by
  let q := triadicDescendant N (J + 1) k l
  have hq : q ∉ oddGridUnresolved (triadicHalf (N + (J + 1))) I := by
    intro h
    exact (Finset.mem_filter.mp hl).2.2
      ((triadicDescendant_mem_unresolved_iff N (J + 1) I k l).mp h)
  have he := affineDiagonalDefect_compactPotential_domain_eq
    (triadicDescendant_cell z hr N (J + 1) k l).symm
    (centeredCube_isBounded _ _) (centeredCube_isBounded _ _)
    (centeredCube_volume_pos _ _) (centeredCube_volume_pos _ _)
    (observation_killedPoincare z hr hD N k (J + 1) l) (hD (N + (J + 1)) q)
    (observation_meanZeroPoincare z hr hN N k (J + 1) l) (hN (N + (J + 1)) q)
    (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P)) p
  erw [he]
  rw [← positiveCoefficientRestrict_compactPotential
    (oddGridCell_subset z hr (triadicHalf (N + (J + 1))) q)]
  erw [affineDiagonalDefect_fold_cell z hr (hD (N + (J + 1))) (hN (N + (J + 1))) I P q hq]
  apply le_triadicDefectSup
  rw [coordinateReflectionDerivative_sum_sq]
  exact hp

end SubdiffusiveProcess
