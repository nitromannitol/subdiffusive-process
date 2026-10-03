module

public import SubdiffusiveProcess.Paper.prop_conc_local_affine_order
public import SubdiffusiveProcess.Paper.prop_conc_core_measure_data
public import SubdiffusiveProcess.Paper.lem_borel_weights_form
public import SubdiffusiveProcess.DirichletForm.EnergyMeasureCongruence

@[expose] public section

/-! Weighted diagonal energy determines the full local weighted energy-measure calculus.
This is a deterministic identification on the common form domain, with no limiting or moment assertion. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

/-- Equal forms on a common domain have equal polarized energy measures. -/
theorem aux_prop_conc_weighted_measure_identification_cross_eq
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hEc : ∃ C, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hFc : ∃ C, DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = F.domain)
    (hdiag : ∀ u ∈ E.domain, E.form u u = F.form u u) :
    ∀ u ∈ E.domain, ∀ v ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      GammaE.cross u v A = GammaF.cross u v A := by
  have hle := aux_thm_prop_endpoint_invariance_energy_order_one_sided_light Q E F hFc hdom
    GammaE GammaF 1 one_pos (fun u hu => by rw [one_mul, hdiag u hu])
  have hge := aux_thm_prop_endpoint_invariance_energy_order_one_sided_light Q F E hEc hdom.symm
    GammaF GammaE 1 one_pos (fun u hu => by rw [one_mul, hdiag u (hdom.symm ▸ hu)])
  have heq : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      (GammaE.measure u A).toReal = (GammaF.measure u A).toReal := by
    intro u hu A hA
    exact le_antisymm (by simpa only [one_mul] using hle u hu A hA)
      (by simpa only [one_mul] using hge u (hdom ▸ hu) A hA)
  intro u hu v hv A hA
  rw [GammaE.cross_eq_polarization hu hv A,
    GammaF.cross_eq_polarization (hdom ▸ hu) (hdom ▸ hv) A,
    GammaE.cross_self _ (E.domain.add_mem hu hv) A hA,
    GammaE.cross_self _ (E.domain.sub_mem hu hv) A hA,
    GammaF.cross_self _ (F.domain.add_mem (hdom ▸ hu) (hdom ▸ hv)) A hA,
    GammaF.cross_self _ (F.domain.sub_mem (hdom ▸ hu) (hdom ▸ hv)) A hA,
    heq _ (E.domain.add_mem hu hv) A hA, heq _ (E.domain.sub_mem hu hv) A hA]

/-- The weighted form identity identifies the actual weighted measures and all their polarizations. -/
theorem prop_conc_weighted_measure_identification
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hEc : ∃ C, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hFc : ∃ C, DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hEloc : DirichletForm.IsStronglyLocal E.toClosedForm)
    (hdom : E.domain = F.domain)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (K : ℝ) (hK : ∀ x, |g x| ≤ K)
    (hdiag : ∀ u ∈ E.domain, F.form u u = ∫ x, Real.exp (g x) ∂(GammaE.measure u)) :
    (∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      GammaF.measure u A = ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u)) ∧
    (∀ u ∈ E.domain, ∀ v ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      GammaF.cross u v A = DirichletForm.signedIntegralOn (GammaE.cross u v) A
        (fun x => Real.exp (g x))) := by
  have hreg := aux_prop_conc_core_measure_data_isRegular_of_core Q E.toClosedForm hEc
  have halg : DirichletForm.IsCoreAlgebra E.toClosedForm :=
    ⟨hreg, DirichletForm.mul_mem E, DirichletForm.comp_mem E,
      DirichletForm.mul_comp_mem E, DirichletForm.mul_mem_of_bounded E⟩
  obtain ⟨Eg, GammaG, hGD, hGF, _hGreg, hGC, _hGloc, hGcross⟩ :=
    lem_borel_weights_form E GammaE g hg K hK hreg hEc hEloc halg
  have hexp : ∀ x, |Real.exp (g x)| ≤ Real.exp K := fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hK x))
  have hGFdiag : ∀ u ∈ Eg.domain, Eg.form u u = F.form u u := by
    intro u hu
    have huE : u ∈ E.domain := hGD ▸ hu
    rw [hGF u huE u huE, hdiag u huE,
      DirichletForm.aux_signedIntegralOn_cross_self E.toClosedForm GammaE u huE
        (fun x => Real.exp (g x)) ⟨hg.exp, ⟨Real.exp K, hexp⟩⟩, Measure.restrict_univ]
  have hcross : ∀ u ∈ E.domain, ∀ v ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      GammaF.cross u v A = DirichletForm.signedIntegralOn (GammaE.cross u v) A
        (fun x => Real.exp (g x)) := by
    intro u hu v hv A hA
    rw [← aux_prop_conc_weighted_measure_identification_cross_eq Q Eg F GammaG GammaF
      hGC hFc (hGD.trans hdom) hGFdiag u (hGD.symm ▸ hu) v (hGD.symm ▸ hv) A hA]
    exact hGcross u hu v hv A hA
  refine ⟨?_, hcross⟩
  intro u hu A hA
  letI finiteE : IsFiniteMeasure (GammaE.measure u) := ⟨GammaE.measure_univ_lt_top u hu⟩
  letI finiteF : IsFiniteMeasure (GammaF.measure u) := ⟨GammaF.measure_univ_lt_top u (hdom ▸ hu)⟩
  have hmeasure : GammaF.measure u = (GammaE.measure u).withDensity
      (fun x => ENNReal.ofReal (Real.exp (g x))) :=
    DirichletForm.aux_measure_eq_withDensity_of_setIntegral (GammaE.measure u) (GammaF.measure u)
      (fun x => Real.exp (g x)) hg.exp (fun x => (Real.exp_pos _).le) (fun B hB => by
        rw [← GammaF.cross_self u (hdom ▸ hu) B hB, hcross u hu u hu B hB,
          DirichletForm.aux_signedIntegralOn_cross_self E.toClosedForm GammaE u hu
            (fun x => Real.exp (g x)) ⟨hg.exp, ⟨Real.exp K, hexp⟩⟩])
  rw [hmeasure, withDensity_apply _ hA]

end
end Paper
