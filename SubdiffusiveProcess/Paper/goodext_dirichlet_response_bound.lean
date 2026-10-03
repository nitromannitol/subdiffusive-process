module

public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative
@[expose] public section

/-! This file derives a uniform finite Dirichlet-response estimate from the
boundary Holder extension theorem; it makes no stochastic claim. -/
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology
noncomputable section
namespace Paper
/-- A Holder boundary datum controls the response of every weak datum with the same
continuous boundary representative, uniformly over coefficients. -/
theorem goodext_dirichlet_response_bound
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (X : in_extension d hd I) (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr))
        (g : SpatialCoordinates d → ℝ) (Lam : ℝ),
        I.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 ≤ Lam →
        IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) g →
        ∀ (b : weakSobolevGraph (centeredCube z r hr)) (B : SpatialCoordinates d → ℝ),
          ContinuousOn B (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
          ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] B) →
          EqOn B g (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) →
          dirichletResponse (killedResponseSpace hP) a b ≤
            C * Lam * r ^ ((d : ℝ) - 2) *
              (r ^ beta * holderSeminorm beta
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) g) ^ 2
:= by
  classical
  obtain ⟨C, hC, hExt⟩ := (Paper.lem_extension d hd I X Sob).1 beta hbeta
  refine ⟨C, hC, ?_⟩
  intro z r hr hr1 hP a g Lam hLam hHolder b B hCont hAE hEq
  have hclosure :
      closure (centeredCube z r hr : Set (SpatialCoordinates d)) =
        closedCube z r hr := by
    change closure (Metric.ball z (r / 2)) = Metric.closedBall z (r / 2)
    exact closure_ball z (ne_of_gt (half_pos hr))
  have hContClosed : ContinuousOn B (closedCube z r hr : Set (SpatialCoordinates d)) := by
    rw [← hclosure]
    exact hCont
  have hHolderB :
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) B :=
    (isHolderOn_congr hEq).mpr hHolder
  have hSemi :
      holderSeminorm beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) B =
        holderSeminorm beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) g := by
    unfold holderSeminorm
    rw [holderRatioSet_congr hEq]
  have hBound := hExt z r hr hr1 hP a B b hContClosed hHolderB hAE
  have hRadius : 0 ≤ r ^ ((d : ℝ) - 2) := (Real.rpow_pos_of_pos hr _).le
  have hSquare :
      0 ≤ (r ^ beta *
        holderSeminorm beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) g) ^ 2 :=
    sq_nonneg _
  have hCoefficient :
      C * I.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 ≤ C * Lam :=
    mul_le_mul_of_nonneg_left hLam hC.le
  calc
    dirichletResponse (killedResponseSpace hP) a b ≤
        C * I.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
          r ^ ((d : ℝ) - 2) *
            (r ^ beta *
              holderSeminorm beta
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) g) ^ 2 :=
      by simpa only [hSemi] using hBound
    _ ≤ C * Lam * r ^ ((d : ℝ) - 2) *
          (r ^ beta *
            holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) g) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCoefficient hRadius) hSquare
