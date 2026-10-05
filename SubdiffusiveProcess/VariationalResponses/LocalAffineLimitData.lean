module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.DirichletForm.KilledCoreClosure
public import SubdiffusiveProcess.DirichletForm.EnergyMeasure
public import SubdiffusiveProcess.Sobolev.AffineResponses

@[expose] public section

/-! The operator and affine response data of a supplied cutoff limit on two cells.
This structure records convergence and identification only; it asserts no growth or concentration. -/
open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology
namespace SubdiffusiveProcess

/-- A supplied ambient form limit and the coordinate responses on its observation cell. -/
structure LocalAffineLimitData
    {d : ℕ} {Q q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (q : Set (SpatialCoordinates d)))]
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (hq : Bornology.IsBounded (q : Set (SpatialCoordinates d)))
    (hP : ∃ C : ℝ≥0, ∀ u : killedSobolevGraph q,
      ‖u.val.1‖ ≤ C * ‖subspaceGradient (killedSobolevGraph q) u‖)
    (b : ℕ → PositiveCoefficient q) (L : Fin d → ℝ) where
  GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q
  G : DomainL2 Q →L[ℝ] DomainL2 Q
  E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))
  Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm
  inverse_eq : ∀ n f, GN n f =
    (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1
  inverse_tendsto : Tendsto GN atTop (𝓝 G)
  energy_eq : ∀ v, E.energy v = limitFormEnergy G v
  core : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C
  affine_tendsto : ∀ i : Fin d, Tendsto
    (fun n => affineDirichletResponse hq hP (b n) (Pi.single i 1)) atTop (𝓝 (L i))

end SubdiffusiveProcess
