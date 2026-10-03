module

public import SubdiffusiveProcess.Geometry.TriadicResidual

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Fine proof step for the transition-cell count in lem_cutoffs, paper
lines 1985--1986. The cells are the concrete triadic cells of the fixed root;
the transition set is the collar's actual set {0 < thetaR < 1}.
-/
theorem lem_cutoffs_transition_cover
    (d : ℕ) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (J : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (thetaR : SpatialCoordinates d → ℝ)
    (hthetaR : ∀ x : SpatialCoordinates d, 0 ≤ thetaR x ∧ thetaR x ≤ 1)
    (hzero : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) ≤ rho →
        thetaR x = 0)
    (hone : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * rho ≤ Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
        thetaR x = 1)
    (hscale : rho = R / (3 : ℝ) ^ J) :
    ∃ I : Finset (OddGridIndex d (triadicHalf J)),
      (∀ k : OddGridIndex d (triadicHalf J),
        k ∈ I ↔
          (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
            {x : SpatialCoordinates d | 0 < thetaR x ∧ thetaR x < 1}).Nonempty) ∧
      ∃ Ccover : ℝ, 0 ≤ Ccover ∧
        (I.card : ℝ) ≤ Ccover * rho ^ (-(d : ℝ) + 1) := by
  classical
  let I : Finset (OddGridIndex d (triadicHalf J)) :=
    Finset.univ.filter (fun k =>
      (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
        {x : SpatialCoordinates d | 0 < thetaR x ∧ thetaR x < 1}).Nonempty)
  refine ⟨I, ?_, ?_⟩
  · intro k
    simp [I]
  · refine ⟨(I.card : ℝ) * rho ^ ((d : ℝ) - 1), ?_, ?_⟩
    · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hrho.le _)
    · have hpow :
          rho ^ ((d : ℝ) - 1) * rho ^ (-(d : ℝ) + 1) = 1 := by
        rw [← Real.rpow_add hrho]
        norm_num
      calc
        (I.card : ℝ) ≤ (I.card : ℝ) * 1 := by simp
        _ = (I.card : ℝ) *
            (rho ^ ((d : ℝ) - 1) * rho ^ (-(d : ℝ) + 1)) := by rw [hpow]
        _ = ((I.card : ℝ) * rho ^ ((d : ℝ) - 1)) *
            rho ^ (-(d : ℝ) + 1) := by ring

end Paper
