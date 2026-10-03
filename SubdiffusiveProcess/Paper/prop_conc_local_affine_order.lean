module

public import SubdiffusiveProcess.Paper.energy_order_of_form_order
public import SubdiffusiveProcess.Lane2.LimitForm
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper
noncomputable section

/-! Checked local energy-order and boundary-response declarations extracted
verbatim from the saved K7 candidate. The cell energy is Gamma(v)(q), and
its affine matrix uses the factor |q|. The killed ambient cube supplies
only the form domain and the continuous boundary trace class. -/

theorem aux_thm_prop_endpoint_invariance_core_lower_one_sided
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hFreg : ∃ Cc : Set (DomainL2 Q),
      DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m : ℝ) (hm : 0 < m) (hform : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v)
    {w : DomainL2 Q} (hw : F.toClosedForm.MemCoreOn (Q : Set (SpatialCoordinates d)) w)
    (A : Set (SpatialCoordinates d)) :
    m * (GammaE.measure w A).toReal ≤ (GammaF.measure w A).toReal := by
  have hwE : E.toClosedForm.MemCoreOn (Q : Set (SpatialCoordinates d)) w := ⟨hdom.symm ▸ hw.1, hw.2⟩
  have horder : ∀ w' : DomainL2 Q,
      F.toClosedForm.MemCoreOn (Q : Set (SpatialCoordinates d)) w' →
      E.form w' w' ≤ (m⁻¹ : ℝ) * F.form w' w' := by
    intro w' hw'
    have hw'E : w' ∈ E.domain := hdom ▸ hw'.mem_domain
    exact (le_inv_mul_iff₀ hm).mpr (hform w' hw'E)
  have hCeq : ((m⁻¹).toNNReal : ℝ) = m⁻¹ := Real.coe_toNNReal m⁻¹ (inv_nonneg.mpr hm.le)
  have key := aux_lem_sincos_of_mul_comp F E hFreg hdom.symm GammaF GammaE
    (Q : Set (SpatialCoordinates d)) Q.isOpen subset_rfl
    (DirichletForm.mul_comp_mem F (Q : Set (SpatialCoordinates d)))
    (m⁻¹).toNNReal (by rw [hCeq]; exact horder) w hw.memCore (A ∩ (Q : Set (SpatialCoordinates d)))
    inter_subset_right
  have hwF : w ∈ F.domain := hw.mem_domain
  have hwEdom : w ∈ E.domain := hwE.mem_domain
  have h : (GammaE.measure w (A ∩ (Q : Set (SpatialCoordinates d)))).toReal ≤
      m⁻¹ * (GammaF.measure w (A ∩ (Q : Set (SpatialCoordinates d)))).toReal := by
    calc (GammaE.measure w (A ∩ (Q : Set (SpatialCoordinates d)))).toReal
        ≤ (((m⁻¹).toNNReal : ℝ≥0∞) * GammaF.measure w
            (A ∩ (Q : Set (SpatialCoordinates d)))).toReal :=
          ENNReal.toReal_mono
            (ENNReal.mul_ne_top ENNReal.coe_ne_top (GammaF.measure_ne_top hwF _)) key
      _ = m⁻¹ * (GammaF.measure w (A ∩ (Q : Set (SpatialCoordinates d)))).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.coe_toReal, hCeq]
  rw [aux_energy_order_of_form_order_inter GammaF hw,
    aux_energy_order_of_form_order_inter GammaE hwE] at h
  exact (le_inv_mul_iff₀ hm).mp h


theorem aux_thm_prop_endpoint_invariance_energy_order_one_sided_light
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hFreg : ∃ Cc : Set (DomainL2 Q),
      DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m : ℝ) (hm : 0 < m)
    (hform : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v) :
    ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      m * (GammaE.measure u A).toReal ≤ (GammaF.measure u A).toReal := by
  intro u hu A hA
  have huF : u ∈ F.domain := hdom ▸ hu
  obtain ⟨Cc, hCc⟩ := id hFreg
  have hbound : ∀ v : DomainL2 Q, v ∈ E.domain → ∀ ε : ℝ, 0 < ε →
      F.toClosedForm.energyNormSq v < ε ^ 2 * min 1 m →
      Real.sqrt (GammaE.measure v A).toReal ≤ ε ∧
        Real.sqrt (GammaF.measure v A).toReal ≤ ε := by
    intro v hvE ε hε hv
    have hvF : v ∈ F.domain := hdom ▸ hvE
    have hminm : min (1 : ℝ) m ≤ m := min_le_right 1 m
    have hmin1 : min (1 : ℝ) m ≤ 1 := min_le_left 1 m
    have hFv : F.form v v < ε ^ 2 * min 1 m :=
      lt_of_le_of_lt F.toClosedForm.form_le_energyNormSq hv
    have hle := hform v hvE
    have hFv' : F.form v v < ε ^ 2 := by nlinarith [sq_nonneg ε, hFv, hmin1]
    have hEm : m * E.form v v < ε ^ 2 * m := by nlinarith [sq_nonneg ε, hFv, hminm, hle]
    have hEv : E.form v v < ε ^ 2 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hEm, hm, mul_le_mul_of_nonneg_left hcon hm.le]
    have hGE : (GammaE.measure v A).toReal ≤ ε ^ 2 :=
      (GammaE.toReal_measure_le_form hvE A).trans hEv.le
    have hGF : (GammaF.measure v A).toReal ≤ ε ^ 2 :=
      (GammaF.toReal_measure_le_form hvF A).trans hFv'.le
    exact ⟨(Real.sqrt_le_sqrt hGE).trans_eq (Real.sqrt_sq hε.le),
      (Real.sqrt_le_sqrt hGF).trans_eq (Real.sqrt_sq hε.le)⟩
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ w : DomainL2 Q,
      F.toClosedForm.MemCoreOn (Q : Set (SpatialCoordinates d)) w ∧
      Real.sqrt (GammaE.measure u A).toReal ≤ Real.sqrt (GammaE.measure w A).toReal + ε ∧
      Real.sqrt (GammaE.measure w A).toReal ≤ Real.sqrt (GammaE.measure u A).toReal + ε ∧
      Real.sqrt (GammaF.measure u A).toReal ≤ Real.sqrt (GammaF.measure w A).toReal + ε ∧
      Real.sqrt (GammaF.measure w A).toReal ≤ Real.sqrt (GammaF.measure u A).toReal + ε := by
    intro ε hε
    have hδ : 0 < ε ^ 2 * min 1 m := by positivity
    obtain ⟨w, hwC, hsmallF⟩ := hCc.denseEnergy u huF _ hδ
    have hwFcore := hCc.memCoreOn w hwC
    have hwF : w ∈ F.domain := hwFcore.mem_domain
    have hwE : w ∈ E.domain := hdom ▸ hwF
    have huw : u - w ∈ E.domain := E.domain.sub_mem hu hwE
    have hwu : w - u ∈ E.domain := E.domain.sub_mem hwE hu
    have hsmallF' : F.toClosedForm.energyNormSq (w - u) < ε ^ 2 * min 1 m := by
      rw [← F.toClosedForm.energyNormSq_sub_comm huF hwF]; exact hsmallF
    obtain ⟨s1, s2⟩ := hbound (u - w) huw ε hε hsmallF
    obtain ⟨s3, s4⟩ := hbound (w - u) hwu ε hε hsmallF'
    have m1 := aux_energy_order_of_form_order_sqrt_le GammaE hu hwE hA
    have m2 := aux_energy_order_of_form_order_sqrt_le GammaE hwE hu hA
    have m3 := aux_energy_order_of_form_order_sqrt_le GammaF huF hwF hA
    have m4 := aux_energy_order_of_form_order_sqrt_le GammaF hwF huF hA
    exact ⟨w, hwFcore, by linarith, by linarith, by linarith, by linarith⟩
  have h := aux_energy_order_of_form_order_le_of_approx hm.le zero_le_one
    (ENNReal.toReal_nonneg : 0 ≤ (GammaE.measure u A).toReal)
    (ENNReal.toReal_nonneg : 0 ≤ (GammaF.measure u A).toReal) (fun ε hε => by
      obtain ⟨w, hw, a1, -, -, a4⟩ := happrox ε hε
      refine ⟨_, _, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, a1, a4, ?_⟩
      rw [one_mul]
      exact aux_thm_prop_endpoint_invariance_core_lower_one_sided Q E F hFreg hdom
        GammaE GammaF m hm hform hw A)
  rwa [one_mul] at h


def aux_thm_prop_boundary_energy_set
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (q : Set (SpatialCoordinates d)) (b : SpatialCoordinates d → ℝ) : Set ℝ :=
  {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
    v ∈ E.domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
    (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
    (∀ x ∈ frontier q, V x = b x) ∧ e = (Gamma.measure v q).toReal}


theorem aux_thm_prop_boundary_glb_order
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hdom : E.domain = F.domain)
    (hFcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm
      (Q : Set (SpatialCoordinates d)) C)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m : ℝ) (hm : 0 < m)
    (horder : ∀ u ∈ E.domain, m * E.form u u ≤ F.form u u)
    (q : Set (SpatialCoordinates d)) (hq : MeasurableSet q)
    (b : SpatialCoordinates d → ℝ) (e f : ℝ)
    (he : IsGLB (aux_thm_prop_boundary_energy_set Q E.toClosedForm GammaE q b) e)
    (hf : IsGLB (aux_thm_prop_boundary_energy_set Q F.toClosedForm GammaF q b) f) :
    m * e ≤ f := by
  apply hf.2
  rintro t ⟨v, V, hv, hV, hrep, hb, rfl⟩
  have hvE : v ∈ E.domain := hdom.symm ▸ hv
  have hev := he.1 (show (GammaE.measure v q).toReal ∈
      aux_thm_prop_boundary_energy_set Q E.toClosedForm GammaE q b from
    ⟨v, V, hvE, hV, hrep, hb, rfl⟩)
  exact (mul_le_mul_of_nonneg_left hev hm.le).trans
    (aux_thm_prop_endpoint_invariance_energy_order_one_sided_light
      Q E F hFcore hdom GammaE GammaF m hm horder v hvE q hq)


theorem aux_thm_prop_affine_matrix_order
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hdom : E.domain = F.domain)
    (hEcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (Q : Set (SpatialCoordinates d)) C)
    (hFcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm
      (Q : Set (SpatialCoordinates d)) C)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (horder : ∀ u ∈ E.domain,
      m * E.form u u ≤ F.form u u ∧ F.form u u ≤ M * E.form u u)
    (q : Set (SpatialCoordinates d)) (hq : MeasurableSet q)
    (hvol : 0 < (volume q).toReal)
    (AE AF : Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ p : Fin d → ℝ,
      IsGLB (aux_thm_prop_boundary_energy_set Q E.toClosedForm GammaE q
        (fun x => ∑ i, p i * x i)) ((volume q).toReal * (p ⬝ᵥ AE.mulVec p)))
    (hAF : ∀ p : Fin d → ℝ,
      IsGLB (aux_thm_prop_boundary_energy_set Q F.toClosedForm GammaF q
        (fun x => ∑ i, p i * x i)) ((volume q).toReal * (p ⬝ᵥ AF.mulVec p))) :
    ∀ p : Fin d → ℝ,
      m * (p ⬝ᵥ AE.mulVec p) ≤ p ⬝ᵥ AF.mulVec p ∧
      p ⬝ᵥ AF.mulVec p ≤ M * (p ⬝ᵥ AE.mulVec p) := by
  intro p
  have hlo := aux_thm_prop_boundary_glb_order Q E F hdom hFcore GammaE GammaF
    m hm (fun u hu => (horder u hu).1) q hq _ _ _ (hAE p) (hAF p)
  have hrev : ∀ u ∈ F.domain, M⁻¹ * F.form u u ≤ E.form u u := by
    intro u hu
    exact (inv_mul_le_iff₀ hM).mpr (horder u (hdom.symm ▸ hu)).2
  have hhi := aux_thm_prop_boundary_glb_order Q F E hdom.symm hEcore GammaF GammaE
    M⁻¹ (inv_pos.mpr hM) hrev q hq _ _ _ (hAF p) (hAE p)
  have hhi' := (inv_mul_le_iff₀ hM).mp hhi
  constructor
  · apply (mul_le_mul_iff_left₀ hvol).mp
    nlinarith [hlo]
  · apply (mul_le_mul_iff_left₀ hvol).mp
    nlinarith [hhi']


end
end Paper



set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped BigOperators

namespace Paper
noncomputable section

/-- Local Gamma boundary minima, normalized by the cell volume, inherit
comparison of the two ambient forms. Reuses the checked K7 proof. -/
theorem prop_conc_local_affine_order
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hdom : E.domain = F.domain)
    (hEcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (Q : Set (SpatialCoordinates d)) C)
    (hFcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm
      (Q : Set (SpatialCoordinates d)) C)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (horder : ∀ u ∈ E.domain,
      m * E.form u u ≤ F.form u u ∧ F.form u u ≤ M * E.form u u)
    (q : Set (SpatialCoordinates d)) (hq : MeasurableSet q)
    (hvol : 0 < (volume q).toReal)
    (AE AF : Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ p : Fin d → ℝ,
      IsGLB (aux_thm_prop_boundary_energy_set Q E.toClosedForm GammaE q
        (fun x => ∑ i, p i * x i)) ((volume q).toReal * (p ⬝ᵥ AE.mulVec p)))
    (hAF : ∀ p : Fin d → ℝ,
      IsGLB (aux_thm_prop_boundary_energy_set Q F.toClosedForm GammaF q
        (fun x => ∑ i, p i * x i)) ((volume q).toReal * (p ⬝ᵥ AF.mulVec p))) :
    ∀ p : Fin d → ℝ,
      m * (p ⬝ᵥ AE.mulVec p) ≤ p ⬝ᵥ AF.mulVec p ∧
      p ⬝ᵥ AF.mulVec p ≤ M * (p ⬝ᵥ AE.mulVec p) := by
  exact aux_thm_prop_affine_matrix_order Q E F hdom hEcore hFcore
    GammaE GammaF m M hm hM horder q hq hvol AE AF hAE hAF

end
end Paper

