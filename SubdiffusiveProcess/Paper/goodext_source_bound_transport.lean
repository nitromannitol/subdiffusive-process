import SubdiffusiveProcess.Sobolev.HolderAffinePullback
import SubdiffusiveProcess.Sobolev.GoodextHolderLimit
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.RepresentativeReadout
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative

/-! Transport of the candidate sourced Hölder bound from the candidate representative to the
common continuous representative of the same `L²` class, in `lem_goodext`.  No new estimate
is claimed. -/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology

noncomputable section
namespace Paper

/-- Two continuous representatives of one `L²` class carry the same normalized sourced Hölder
bound on a cell whose padded parent lies in the domain. -/
theorem goodext_source_bound_transport {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (z : SpatialCoordinates d) (r alpha Cs se fsup cq : ℝ) (hr : 0 < r)
    (U Ucge : SpatialCoordinates d → ℝ) (u : DomainL2 Q)
    (hcgeC : ContinuousOn Ucge (closure (Q : Set (SpatialCoordinates d))))
    (hcgeRep : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (Q : Set (SpatialCoordinates d))] Ucge)
    (hUc : ContinuousOn U (closure (Q : Set (SpatialCoordinates d))))
    (hUr : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (Q : Set (SpatialCoordinates d))] U)
    (hUh : IsHolderOn alpha (closure (Q : Set (SpatialCoordinates d))) U)
    (h3qQ : Metric.ball z (3 * r / 2) ⊆ (Q : Set (SpatialCoordinates d)))
    (hcgeNorm : cAlphaNorm alpha
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => Ucge (z + r • x) - cq) ≤
        Cs * (normalizedL2On (Metric.ball z (3 * r / 2))
          (fun x => Ucge x - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
            ∫ y in Metric.ball z (3 * r / 2), Ucge y) + r ^ 2 * se⁻¹ * fsup)) :
    ∃ cq : ℝ,
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + r • x) - cq) ≤
        Cs * (normalizedL2On (Metric.ball z (3 * r / 2))
          (fun x => U x - (volume (Metric.ball z (3 * r / 2))).toReal⁻¹ *
            ∫ y in Metric.ball z (3 * r / 2), U y) + r ^ (2 : ℝ) * se⁻¹ * fsup) := by
  let unitClosed : Set (SpatialCoordinates d) :=
    (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
  have hqQ : Metric.ball z (r / 2) ⊆ (Q : Set (SpatialCoordinates d)) :=
    (Metric.ball_subset_ball (by linarith only [hr.le] : r / 2 ≤ 3 * r / 2)).trans h3qQ
  have hEq : EqOn Ucge U (closure (Q : Set (SpatialCoordinates d))) :=
    eqOn_closure_of_ae_eq_restrict Q.isOpen hcgeC hUc (hcgeRep.symm.trans hUr)
  have hMap : MapsTo (fun x => z + r • x) unitClosed (closure (Metric.ball z (r / 2))) := by
    intro x hx
    rw [closure_ball z (half_pos hr).ne']
    have hx' : ‖x‖ ≤ 1 / 2 := by
      change dist x (0 : SpatialCoordinates d) ≤ 1 / 2 at hx
      simpa only [dist_zero_right] using hx
    change dist (z + r • x) z ≤ r / 2
    rw [dist_eq_norm, show z + r • x - z = r • x by abel,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    linarith only [mul_le_mul_of_nonneg_left hx' hr.le]
  have hNormEq : cAlphaNorm alpha unitClosed (fun x => Ucge (z + r • x) - cq) =
      cAlphaNorm alpha unitClosed (fun x => U (z + r • x) - cq) := by
    apply cAlphaNorm_congr
    intro x hx
    exact congrArg (fun v : ℝ => v - cq) (hEq (closure_mono hqQ (hMap hx)))
  have hEq3 : Ucge =ᵐ[volume.restrict (Metric.ball z (3 * r / 2))] U :=
    ae_restrict_of_ae_restrict_of_subset h3qQ (hcgeRep.symm.trans hUr)
  have hOscEq :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.normalizedL2On_sub_average_eq_of_ae_eq hEq3
  change normalizedL2On (Metric.ball z (3 * r / 2))
    (fun x => Ucge x - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
      ∫ y in Metric.ball z (3 * r / 2), Ucge y) =
    normalizedL2On (Metric.ball z (3 * r / 2))
    (fun x => U x - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
      ∫ y in Metric.ball z (3 * r / 2), U y) at hOscEq
  rw [hNormEq, hOscEq] at hcgeNorm
  refine ⟨cq, isHolderOn_comp_affine_sub_const alpha unitClosed
    (closure (Q : Set (SpatialCoordinates d))) z r cq hr U
    (fun x hx => closure_mono hqQ (hMap hx)) hUh, ?_⟩
  simpa only [Real.rpow_two] using hcgeNorm

end Paper
