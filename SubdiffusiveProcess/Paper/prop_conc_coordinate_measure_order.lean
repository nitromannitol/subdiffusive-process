import SubdiffusiveProcess.Paper.prop_conc_local_affine_order

/-! Local form order controls coordinate energy measures on every set.
This upgrades the measurable-set comparison; it does not assume energy growth. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

/-- Positive local form order gives an inequality of the full energy measures. -/
theorem aux_prop_conc_coordinate_measure_order_single
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hFcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m : ℝ) (hm : 0 < m) (hform : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v)
    (u : DomainL2 Q) (hu : u ∈ F.domain) :
    GammaE.measure u ≤ ENNReal.ofReal m⁻¹ • GammaF.measure u := by
  have huE : u ∈ E.domain := hdom.symm ▸ hu
  apply Measure.le_iff.mpr
  intro A hA
  have h := aux_thm_prop_endpoint_invariance_energy_order_one_sided_light Q E F hFcore hdom
    GammaE GammaF m hm hform u huE A hA
  have hreal : (GammaE.measure u A).toReal ≤ m⁻¹ * (GammaF.measure u A).toReal :=
    (le_inv_mul_iff₀ hm).mpr h
  calc
    GammaE.measure u A = ENNReal.ofReal (GammaE.measure u A).toReal :=
      (ENNReal.ofReal_toReal (GammaE.measure_ne_top huE A)).symm
    _ ≤ ENNReal.ofReal (m⁻¹ * (GammaF.measure u A).toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = (ENNReal.ofReal m⁻¹ • GammaF.measure u) A := by
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hm.le),
        ENNReal.ofReal_toReal (GammaF.measure_ne_top hu A), Measure.smul_apply, smul_eq_mul]

/-- The cross-coordinate energy measure is bounded by the reciprocal form-order constant. -/
theorem prop_conc_coordinate_measure_order
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hFcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m : ℝ) (hm : 0 < m) (hform : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v)
    (u : Fin d → DomainL2 Q) (hu : ∀ i, u i ∈ F.domain) :
    ∀ A : Set (SpatialCoordinates d),
      ((∑ i, GammaE.measure (u i)) A).toReal ≤
        m⁻¹ * ((∑ i, GammaF.measure (u i)) A).toReal := by
  have hle : (∑ i, GammaE.measure (u i)) ≤
      ENNReal.ofReal m⁻¹ • ∑ i, GammaF.measure (u i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_le_sum fun i _ =>
      aux_prop_conc_coordinate_measure_order_single Q E F hFcore hdom GammaE GammaF m hm hform
        (u i) (hu i)
  intro A
  have hfin : (∑ i, GammaF.measure (u i)) A ≠ ⊤ := by
    rw [Measure.finset_sum_apply]
    exact ENNReal.sum_ne_top.mpr (fun i _ => GammaF.measure_ne_top (hu i) A)
  have hA := hle A
  rw [Measure.smul_apply, smul_eq_mul] at hA
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hA
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hm.le)] using h

end
end Paper
