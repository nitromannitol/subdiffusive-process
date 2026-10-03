module

public import SubdiffusiveProcess.Paper.weighted_killed_form
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Sobolev.ResponseComparison
public import SubdiffusiveProcess.Sobolev.RelativePerturbation

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace Paper



theorem lem_weighted_cluster_form_bounds
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a arho : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (ha : ∀ n, (a n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] A n)
    (rho : SpatialCoordinates d → ℝ)
    (hrhocont : ContinuousOn rho
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hrhopos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      0 < rho x)
    (lo hi : ℝ) (hlo : 0 < lo)
    (hlodef : lo = sInf (rho '' closure
      (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hhidef : hi = sSup (rho '' closure
      (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hrhobounds : ∀ x, x ∈ closure
      (centeredCube z r hr : Set (SpatialCoordinates d)) →
      lo ≤ rho x ∧ rho x ≤ hi)
    (harho : ∀ n, (arho n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))]
      (fun x => rho x * A n x)) :
    ∀ n (u : S.space),
      lo * responseForm S (a n) u u ≤ responseForm S (arho n) u u ∧
      responseForm S (arho n) u u ≤ hi * responseForm S (a n) u u := by
  intro n u
  obtain ⟨c, hc, hcae⟩ := (a n).property
  have hzmem : z ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    change z ∈ Metric.ball z (r / 2)
    exact Metric.mem_ball_self (half_pos hr)
  have hzclosure : z ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    subset_closure hzmem
  have hhi : 0 < hi :=
    lt_of_lt_of_le hlo ((hrhobounds z hzclosure).1.trans (hrhobounds z hzclosure).2)
  have hlow : ∀ᵐ x ∂volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo * (a n).val x ≤ (arho n).val x := by
    filter_upwards [ha n, harho n, hcae,
      self_mem_ae_restrict (centeredCube z r hr).isOpen.measurableSet]
      with x hA hArho hpos hx
    have hAnneg : 0 ≤ A n x := by
      rw [← hA]
      exact hc.le.trans hpos
    rw [hA, hArho]
    exact mul_le_mul_of_nonneg_right (hrhobounds x (subset_closure hx)).1 hAnneg
  have hupp : ∀ᵐ x ∂volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)),
      (arho n).val x ≤ hi * (a n).val x := by
    filter_upwards [ha n, harho n, hcae,
      self_mem_ae_restrict (centeredCube z r hr).isOpen.measurableSet]
      with x hA hArho hpos hx
    have hAnneg : 0 ≤ A n x := by
      rw [← hA]
      exact hc.le.trans hpos
    rw [hArho, hA]
    exact mul_le_mul_of_nonneg_right (hrhobounds x (subset_closure hx)).2 hAnneg
  constructor
  · change lo * weightedGradientForm (a n).val
        (subspaceGradient S.space u) (subspaceGradient S.space u) ≤
      weightedGradientForm (arho n).val
        (subspaceGradient S.space u) (subspaceGradient S.space u)
    exact weightedGradientForm_mul_le (a n) (arho n) hlo hlow
      (subspaceGradient S.space u)
  · change weightedGradientForm (arho n).val
        (subspaceGradient S.space u) (subspaceGradient S.space u) ≤
      hi * weightedGradientForm (a n).val
        (subspaceGradient S.space u) (subspaceGradient S.space u)
    exact weightedGradientForm_le_mul (arho n) (a n) hi hupp
      (subspaceGradient S.space u)

end Paper

