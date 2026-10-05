module

public import SubdiffusiveProcess.EllipticRegularity.ResponseJBridge
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The same normalized Ch02 response bounds both affine coordinates of the
Sobolev response bank on one cube, with the same coefficient. This is a
conditional carrier identity; cutoff moment and limit producers remain work
for the parent shallow-grid theorem. -/
theorem lem_as_coarse_shallow_grid_responseJ_bridge {d : ℕ}
    (U : Homogenization.Book.Ch02.Domain d)
    (Om : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    (hset : (Om : Set (SpatialCoordinates d)) = (U : Set (Homogenization.Vec d)))
    {a : Homogenization.Vec d → ℝ}
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (hOm : Bornology.IsBounded (Om : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Om) w‖)
    (hN : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Om) w‖)
    (aQ : PositiveCoefficient Om)
    (haQ : ((aQ.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a))
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1) :
    affineDirichletResponse hOm hD aQ e ≤
        2 * volume.real (Om : Set (SpatialCoordinates d)) *
          (Homogenization.Book.Ch02.responseJ U data.toCoeffOn e e + 1) ∧
      affineInverseNeumannResponse hN aQ e ≤
        2 * volume.real (Om : Set (SpatialCoordinates d)) *
          (Homogenization.Book.Ch02.responseJ U data.toCoeffOn e e + 1) := by
  have hbridge := responseJ_eq_affineDiagonalDefect U Om hset (by norm_num : (0 : ℝ) < 1)
    data hOm hvol hD hN aQ (by simpa using haQ) e he
  simp only [Real.sqrt_one, inv_one, one_smul] at hbridge
  have hDnn : 0 ≤ affineDirichletResponse hOm hD aQ e :=
    dirichletResponse_nonneg (killedResponseSpace hD) aQ (affineSobolev hOm e 0)
  have hNnn : 0 ≤ affineInverseNeumannResponse hN aQ e :=
    inverseResponse_nonneg (meanZeroResponseSpace hN) aQ _
  have heSq : (∑ i : Fin d, (e i) ^ 2) = 1 := by
    rw [← he, Homogenization.vecNormSq, Homogenization.vecDot]
    exact Finset.sum_congr rfl fun i _ => sq (e i)
  unfold affineDiagonalDefect at hbridge
  rw [heSq] at hbridge
  have hsum : affineDirichletResponse hOm hD aQ e +
      affineInverseNeumannResponse hN aQ e =
        2 * volume.real (Om : Set (SpatialCoordinates d)) *
          (Homogenization.Book.Ch02.responseJ U data.toCoeffOn e e + 1) := by
    have hv : 0 < 2 * volume.real (Om : Set (SpatialCoordinates d)) := by positivity
    have hdiv : (affineDirichletResponse hOm hD aQ e +
        affineInverseNeumannResponse hN aQ e) /
        (2 * volume.real (Om : Set (SpatialCoordinates d))) =
          Homogenization.Book.Ch02.responseJ U data.toCoeffOn e e + 1 := by
      linarith [hbridge]
    have hmul := (div_eq_iff hv.ne').mp hdiv
    nlinarith [hmul]
  constructor <;> linarith

end SubdiffusiveProcess.Paper
