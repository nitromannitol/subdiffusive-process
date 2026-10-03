module

public import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy

@[expose] public section

/-! Identify native minimizing boundary competitors with the killed graph minimizer.
This is a fixed-coefficient statement and makes no limiting or probabilistic claim. -/

open MeasureTheory Set TopologicalSpace Homogenization SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped NNReal

namespace SubdiffusiveProcess
noncomputable section

/-- A native boundary-energy minimizer represents the unique killed graph minimizer. -/
theorem native_boundary_minimizer_eq
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) w‖)
    (a : PositiveCoefficient Q) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (beta v : H1Function (Q : Set (SpatialCoordinates d)))
    (hv : HasZeroTraceDifferenceOn (Q : Set (SpatialCoordinates d)) v beta)
    (hmin : energy c (Q : Set (SpatialCoordinates d)) v ≤
      cellDirichletInfimum c (Q : Set (SpatialCoordinates d)) beta) :
    (⟨sobolevDataOfH1 v, sobolevDataOfH1_mem_weak v⟩ : weakSobolevGraph Q) =
      dirichletMinimizer (killedResponseSpace hP) a
        ⟨sobolevDataOfH1 beta, sobolevDataOfH1_mem_weak beta⟩ := by
  obtain ⟨w, hwf, hwg⟩ := hv
  let wS : (killedResponseSpace hP).space :=
    ⟨sobolevDataOfH1 w.toH1Function, sobolevDataOfH1_mem_killed w⟩
  have heq : sobolevDataOfH1 v = sobolevDataOfH1 beta + wS.val := by
    rw [← sobolevDataOfH1_add]
    exact sobolevDataOfH1_eq_of_representatives v (beta + w.toH1Function) hwf hwg
  rw [energy_eq_sobolevCoefficientForm a c hc,
    cellDirichletInfimum_eq_dirichletResponse hP a c hc beta, heq] at hmin
  exact Subtype.ext (heq.trans (dirichletMinimizer_unique (killedResponseSpace hP) a
    ⟨sobolevDataOfH1 beta, sobolevDataOfH1_mem_weak beta⟩ wS hmin))

/-- A native minimum with its prescribed trace solves the zero-source graph equation. -/
theorem solvesDirichlet_zero_of_native_minimum
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
      ‖w.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) w‖)
    (a : PositiveCoefficient Q) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (beta v : H1Function (Q : Set (SpatialCoordinates d)))
    (hv : HasZeroTraceDifferenceOn (Q : Set (SpatialCoordinates d)) v beta)
    (hmin : energy c (Q : Set (SpatialCoordinates d)) v ≤
      cellDirichletInfimum c (Q : Set (SpatialCoordinates d)) beta) :
    SolvesDirichlet a (fun _ => 0)
      ⟨sobolevDataOfH1 beta, sobolevDataOfH1_mem_weak beta⟩
      ⟨sobolevDataOfH1 v, sobolevDataOfH1_mem_weak v⟩ := by
  rw [native_boundary_minimizer_eq hP a c hc beta v hv hmin]
  exact dirichletMinimizer_solves_zero hP a _

end
end SubdiffusiveProcess
