module

public import SubdiffusiveProcess.DirichletForm.KilledCoreClosure
public import SubdiffusiveProcess.DirichletForm.EnergyMeasure
public import SubdiffusiveProcess.Sobolev.AffineData
public import SubdiffusiveProcess.Geometry.Cube

@[expose] public section

/-! Data of a local affine minimizer in an ambient killed form.
Response and growth fields concern the energy measure on the observation cell. -/
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace DirichletForm

/-- A local affine minimizer together with its cell response and quantitative energy-measure growth. -/
structure LocalAffineMinimizer
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : EnergyMeasure E.toClosedForm) (p : Fin d → ℝ) (L K t : ℝ) where
  u : DomainL2 (centeredCube z (3 * r) h3r)
  representative : SpatialCoordinates d → ℝ
  mem : u ∈ E.toClosedForm.domain
  continuous : ContinuousOn representative
    (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
  coeFn : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
    (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] representative
  boundary : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
    representative x = ∑ i, p i * x i
  frontier_null : Gamma.measure u (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0
  orthogonal : ∀ v ∈ E.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d)),
    E.form u v = 0
  response_eq : (Gamma.measure u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal = L
  minimal : ∀ v ∈ E.toClosedForm.domain, ∀ vc : SpatialCoordinates d → ℝ,
    ContinuousOn vc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
    (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] vc →
    (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), vc x = ∑ i, p i * x i) →
    (Gamma.measure u (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
      (Gamma.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  growth : ∀ x ∈ centeredCube z r hr, ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
    Gamma.measure u (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
      ENNReal.ofReal (K * rho ^ t)

end DirichletForm
