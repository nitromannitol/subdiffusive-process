module

public import SubdiffusiveProcess.DirichletForm.EnergyMeasure

@[expose] public section

/-! Local energy minimality depends only on the function inside the open cell.
This transfers a variational inequality between representatives without changing the variation space. -/
open MeasureTheory Set
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.DirichletForm.EnergyMeasure

/-- Two domain elements equal on an open cell have the same local variational minimum. -/
theorem local_minimum_of_ae_eq
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    {mu : Measure X} {E : ClosedForm mu} (Gamma : EnergyMeasure E)
    (U : Set X) (hU : IsOpen U) (D : Submodule ℝ (Lp ℝ 2 mu)) (hD : D ≤ E.domain)
    (u v : Lp ℝ 2 mu) (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (heq : (u : X → ℝ) =ᵐ[mu.restrict U] (v : X → ℝ))
    (hmin : ∀ w ∈ E.domain, w - u ∈ D →
      (Gamma.measure u U).toReal ≤ (Gamma.measure w U).toReal) :
    ∀ w ∈ E.domain, w - v ∈ D →
      (Gamma.measure v U).toReal ≤ (Gamma.measure w U).toReal := by
  intro w hw hdiff
  let w' : Lp ℝ 2 mu := u + (w - v)
  have hw' : w' ∈ E.domain := E.domain.add_mem hu (hD hdiff)
  have hw'trace : w' - u ∈ D := by
    simpa only [w', add_sub_cancel_left] using hdiff
  have hw'eq : (w' : X → ℝ) =ᵐ[mu.restrict U] (w : X → ℝ) := by
    filter_upwards [heq, ae_restrict_of_ae (Lp.coeFn_add u (w - v)),
      ae_restrict_of_ae (Lp.coeFn_sub w v)] with x hx hsum hsub
    change (u + (w - v)) x = w x
    rw [hsum, Pi.add_apply, hsub, Pi.sub_apply, hx]
    ring
  have h := hmin w' hw' hw'trace
  rw [Gamma.locality_apply hu hv hU heq, Gamma.locality_apply hw' hw hU hw'eq] at h
  exact h

end SubdiffusiveProcess.DirichletForm.EnergyMeasure
