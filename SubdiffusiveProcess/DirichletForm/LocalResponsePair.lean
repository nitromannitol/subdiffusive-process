module

public import SubdiffusiveProcess.DirichletForm.KilledCoreClosure
public import SubdiffusiveProcess.DirichletForm.LocalEnergyQuadratic

@[expose] public section

/-! Common-trace local variational data for two closed forms.
This record describes deterministic minimizers and their quadratic responses, with no probabilistic assumptions. -/
open MeasureTheory Set
namespace DirichletForm

/-- Two local quadratic responses represented by minimizers in a common affine trace class. -/
structure LocalResponsePair
    {X V : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [AddCommGroup V] [Module ℝ V] {mu : Measure X}
    (E F : ClosedForm mu) (GammaE : EnergyMeasure E) (GammaF : EnergyMeasure F)
    (A : Set X) (D : Submodule ℝ (Lp ℝ 2 mu)) where
  domain_eq : E.domain = F.domain
  killed : IsKilledDomain E A D
  boundary : V →ₗ[ℝ] E.domain
  uF : V → Lp ℝ 2 mu
  QE : QuadraticForm ℝ V
  QF : QuadraticForm ℝ V
  memF : ∀ p, uF p ∈ F.domain
  traceF : ∀ p, uF p - (boundary p : Lp ℝ 2 mu) ∈ D
  minE : ∀ p, ∀ v ∈ E.domain, v - (boundary p : Lp ℝ 2 mu) ∈ D →
    (GammaE.measure (boundary p) A).toReal ≤ (GammaE.measure v A).toReal
  minF : ∀ p, ∀ v ∈ F.domain, v - (boundary p : Lp ℝ 2 mu) ∈ D →
    (GammaF.measure (uF p) A).toReal ≤ (GammaF.measure v A).toReal
  responseE : ∀ p, QE p = (GammaE.measure (boundary p) A).toReal
  responseF : ∀ p, QF p = (GammaF.measure (uF p) A).toReal

end DirichletForm
