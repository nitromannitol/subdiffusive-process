import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy

/-! Convert uniform zero-source smooth-datum growth to minimizer regularity.
The given coefficient sequence and its actual minimizers are retained. -/
open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess.Lane4
open scoped NNReal Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess

/-- A uniform smooth-data growth bound gives the regularity bank for harmonic minimizers. -/
theorem smooth_minimizer_regularity_of_growth
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖u.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr)) (alpha K : ℝ) (hK : 0 ≤ K)
    (hGrowth : ∀ n (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
      ContDiff ℝ 2 phi → c2Norm (closedCube z r hr) phi ≤ Cphi →
      ∀ b u : weakSobolevGraph (centeredCube z r hr),
        ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] phi) →
        SolvesDirichlet (a n) (fun _ => 0) b u →
        ∃ V : SpatialCoordinates d → ℝ, Continuous V ∧
          ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] V) ∧
          IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) V ≤ K * Cphi) :
    ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph (centeredCube z r hr)),
        ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] phi) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
          ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer (killedResponseSpace hP) (a n) b).val.1 :
            SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
          IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) V ≤ C := by
  intro phi hphi b hb
  let Cphi := max (c2Norm (closedCube z r hr) phi) 0
  refine ⟨K * Cphi, mul_nonneg hK (le_max_right _ _), ?_⟩
  intro n
  obtain ⟨V, hc, hrep, hHol, hnorm⟩ := hGrowth n phi Cphi
    (hphi.of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)) (le_max_left _ _) b
    (dirichletMinimizer (killedResponseSpace hP) (a n) b) hb
    (dirichletMinimizer_solves_zero hP (a n) b)
  exact ⟨V, hc.continuousOn, hrep, hHol, hnorm⟩

end SubdiffusiveProcess
