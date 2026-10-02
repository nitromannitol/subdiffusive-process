import SubdiffusiveProcess.Sobolev.NativeBoundaryResponse
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Sobolev.DomainPoincare

/-! Convert cell-local growth at radius one to a boundary-energy bound.
These deterministic identities use the actual harmonic minimizer and do not
assert convergence or probabilistic bounds for any coefficient sequence. -/

open MeasureTheory Set TopologicalSpace Homogenization SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped NNReal

namespace SubdiffusiveProcess
noncomputable section

/-- Every positive-side cube has a killed Poincare bound on its Sobolev graph. -/
theorem centeredCube_killedPoincare
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖ := by
  have hdom : IsOpenBoundedConvexDomain (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    ⟨(centeredCube z r hr).isOpen, (centeredCube_isBounded z hr).isBoundedDomain,
      convex_ball z (r / 2)⟩
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube z r hr) hdom).1

/-- The killed harmonic minimizer solves the Dirichlet equation with zero source. -/
theorem dirichletMinimizer_solves_zero
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) w‖)
    (a : PositiveCoefficient Q) (b : weakSobolevGraph Q) :
    SolvesDirichlet a (fun _ => 0) b (dirichletMinimizer (killedResponseSpace hP) a b) := by
  refine ⟨dirichletMinimizer_mem_affine (killedResponseSpace hP) a b, ?_⟩
  intro w
  simpa only [zero_mul, integral_zero] using
    dirichletMinimizer_euler (killedResponseSpace hP) a b w

/-- A cube of side at most one lies in the open unit ball about its center. -/
theorem centeredCube_unit_ball_inter
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Metric.ball z 1 ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  apply inter_eq_right.mpr
  exact Metric.ball_subset_ball (by linarith only [hr1])

/-- Growth of a harmonic minimizer at radius one bounds its full Dirichlet response. -/
theorem dirichletResponse_le_of_unit_growth
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr)) (B : ℝ)
    (hB : localGradientEnergy a
      (s := Metric.ball z 1 ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
      (sobolevGradient (dirichletMinimizer (killedResponseSpace hP) a b).val) ≤ B) :
    dirichletResponse (killedResponseSpace hP) a b ≤ B := by
  simp only [centeredCube_unit_ball_inter z hr hr1,
    localGradientEnergy_domain_eq_sobolevCoefficientForm] at hB
  exact hB

/-- The native cell infimum inherits the radius-one growth bound of its harmonic minimizer. -/
theorem cellDirichletInfimum_le_of_unit_growth
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr)) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c)
    (beta : H1Function (centeredCube z r hr : Set (SpatialCoordinates d))) (B : ℝ)
    (hB : localGradientEnergy a
      (s := Metric.ball z 1 ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
      (sobolevGradient (dirichletMinimizer (killedResponseSpace hP) a
        ⟨sobolevDataOfH1 beta, sobolevDataOfH1_mem_weak beta⟩).val) ≤ B) :
    cellDirichletInfimum c (centeredCube z r hr : Set (SpatialCoordinates d)) beta ≤ B := by
  rw [cellDirichletInfimum_eq_dirichletResponse hP a c hc beta]
  exact dirichletResponse_le_of_unit_growth z hr hr1 hP a _ B hB

end
end SubdiffusiveProcess
