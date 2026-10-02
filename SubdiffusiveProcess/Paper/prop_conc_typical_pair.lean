import SubdiffusiveProcess.Paper.prop_conc_local_affine_identified_order
import SubdiffusiveProcess.Paper.prop_conc_linear_family_minimum
import SubdiffusiveProcess.Paper.prop_conc_common_trace_representatives
import SubdiffusiveProcess.Paper.prop_conc_slope_measure_bound
import SubdiffusiveProcess.Paper.prop_conc_pair_data
import SubdiffusiveProcess.Paper.prop_conc_setup
import SubdiffusiveProcess.Paper.prop_conc_growth_moments_of_form_comparison
import SubdiffusiveProcess.Paper.prop_conc_cutoff_affine_coercivity
import SubdiffusiveProcess.Paper.prop_conc_actual_affine_identification
import SubdiffusiveProcess.Paper.prop_conc_form_gamma
import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.DirichletForm.EnergyEquality
import SubdiffusiveProcess.DirichletForm.LocalResponsePair
import SubdiffusiveProcess.DirichletForm.LocalAffineFamily
import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy
import Mathlib.Tactic

/-! A typical configuration carries a pair of limiting forms with its local minimizers in one affine
trace class (`prop_conc_pair_data`), realizing the matrices `A_E`, `A_F` and the growth
`ν(B_ρ ∩ q) ≤ K (ρ/r)^t` of the normalized energy measure, with `‖K‖_{L^p} ≤ B` uniform in the level. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

/-- Closed forms with the same extended energy have the same bilinear values on their domain. -/
theorem aux_prop_conc_typical_pair_form_eq_of_energy_eq
    {X : Type*} [MeasurableSpace X] {m : Measure X}
    {E F : DirichletForm.ClosedForm m} (h : ∀ u, E.energy u = F.energy u)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form u v = F.form u v := by
  have huF := (DirichletForm.ClosedForm.mem_domain_iff_of_energy_eq h u).mp hu
  have hvF := (DirichletForm.ClosedForm.mem_domain_iff_of_energy_eq h v).mp hv
  have h1 := E.form_add_self hu hv
  have h2 := F.form_add_self huF hvF
  have h3 := DirichletForm.ClosedForm.form_self_eq_of_energy_eq h (E.domain.add_mem hu hv)
  have h4 := DirichletForm.ClosedForm.form_self_eq_of_energy_eq h hu
  have h5 := DirichletForm.ClosedForm.form_self_eq_of_energy_eq h hv
  linarith

/-- Strong locality transports across equality of the extended energies. -/
theorem aux_prop_conc_typical_pair_isStronglyLocal_of_energy_eq
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
    {E F : DirichletForm.ClosedForm m} (h : ∀ u, E.energy u = F.energy u)
    (hF : DirichletForm.IsStronglyLocal F) : DirichletForm.IsStronglyLocal E := by
  intro u hu v hv hcu hcv c W hW hvW huW
  have huF := (DirichletForm.ClosedForm.mem_domain_iff_of_energy_eq h u).mp hu
  have hvF := (DirichletForm.ClosedForm.mem_domain_iff_of_energy_eq h v).mp hv
  rw [aux_prop_conc_typical_pair_form_eq_of_energy_eq h hu hv]
  exact hF u huF v hvF hcu hcv c W hW hvW huW

/-- The dual energy of a bounded operator controls the squared `L²` norm. -/
theorem aux_prop_conc_typical_pair_coercive {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) (hu : u ∈ limitFormDomain G) :
    ‖u‖ ^ 2 ≤ (‖G‖ + 1) * (limitFormEnergy G u).toReal := by
  set L : ℝ := ‖G‖ + 1 with hL
  have hLpos : 0 < L := by positivity
  set f : DomainL2 Q := L⁻¹ • u with hf
  have hle : ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal) ≤ limitFormEnergy G u :=
    le_iSup (fun f : DomainL2 Q => ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) f
  have hfin : limitFormEnergy G u < ⊤ := hu
  have hbot : limitFormEnergy G u ≠ ⊥ :=
    (lt_of_lt_of_le (EReal.bot_lt_zero) (limitFormEnergy_nonneg G u)).ne'
  have hreal : 2 * inner ℝ f u - inner ℝ f (G f) ≤ (limitFormEnergy G u).toReal := by
    have := EReal.toReal_le_toReal hle (EReal.coe_ne_bot _) hfin.ne
    rwa [EReal.toReal_coe] at this
  have h1 : inner ℝ f u = L⁻¹ * ‖u‖ ^ 2 := by
    rw [hf, inner_smul_left, real_inner_self_eq_norm_sq]; simp
  have h2 : inner ℝ f (G f) ≤ L⁻¹ ^ 2 * ‖G‖ * ‖u‖ ^ 2 := by
    have hcs : inner ℝ f (G f) ≤ ‖f‖ * ‖G f‖ := real_inner_le_norm _ _
    have hGf : ‖G f‖ ≤ ‖G‖ * ‖f‖ := G.le_opNorm f
    have hfn : ‖f‖ = L⁻¹ * ‖u‖ := by
      rw [hf, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hLpos)]
    calc inner ℝ f (G f) ≤ ‖f‖ * (‖G‖ * ‖f‖) :=
          hcs.trans (mul_le_mul_of_nonneg_left hGf (norm_nonneg _))
      _ = L⁻¹ ^ 2 * ‖G‖ * ‖u‖ ^ 2 := by rw [hfn]; ring
  have hGL : ‖G‖ ≤ L := by rw [hL]; linarith
  have h3 : L⁻¹ ^ 2 * ‖G‖ * ‖u‖ ^ 2 ≤ L⁻¹ * ‖u‖ ^ 2 := by
    have : L⁻¹ ^ 2 * ‖G‖ ≤ L⁻¹ := by
      calc L⁻¹ ^ 2 * ‖G‖ ≤ L⁻¹ ^ 2 * L := mul_le_mul_of_nonneg_left hGL (by positivity)
        _ = L⁻¹ := by field_simp
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h4 : L⁻¹ * ‖u‖ ^ 2 ≤ (limitFormEnergy G u).toReal := by linarith
  have h5 : ‖u‖ ^ 2 ≤ L * (limitFormEnergy G u).toReal := by
    have := mul_le_mul_of_nonneg_left h4 hLpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hLpos.ne', one_mul] at this
  exact h5





theorem aux_prop_conc_typical_pair_response_pair
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (E F : _root_.DirichletForm (volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hEc : ∃ C, DirichletForm.IsCoreOn E.toClosedForm (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (hFc : ∃ C, DirichletForm.IsCoreOn F.toClosedForm (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = F.domain) (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (horder : ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v ∧ F.form v v ≤ M * E.form v v)
    (LE LF : Fin d → ℝ) (KE KF t : ℝ)
    (uE : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer z r hr h3r E GammaE (Pi.single i 1) (LE i) KE t)
    (uF : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer z r hr h3r F GammaF (Pi.single i 1) (LF i) KF t)
    (AE AF : Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ p : Fin d → ℝ,
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) E.toClosedForm GammaE
        (centeredCube z r hr : Set (SpatialCoordinates d)) (fun x => ∑ i, p i * x i))
        ((volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal * (p ⬝ᵥ AE.mulVec p)))
    (hAF : ∀ p : Fin d → ℝ,
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube z (3 * r) h3r) F.toClosedForm GammaF
        (centeredCube z r hr : Set (SpatialCoordinates d)) (fun x => ∑ i, p i * x i))
        ((volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal * (p ⬝ᵥ AF.mulVec p))) :
    ∃ P : DirichletForm.LocalResponsePair (V := Fin d → ℝ) E.toClosedForm F.toClosedForm GammaE GammaF
        (centeredCube z r hr : Set (SpatialCoordinates d))
        (E.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d))),
      (∀ p, P.QE p = (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal * (p ⬝ᵥ AE.mulVec p) ∧
        P.QF p = (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal * (p ⬝ᵥ AF.mulVec p)) ∧
      (∀ p, (P.boundary p : DomainL2 (centeredCube z (3 * r) h3r)) =
        (DirichletForm.LocalAffineMinimizer.linearFamily uE p : DomainL2 (centeredCube z (3 * r) h3r))) ∧
      (∀ p, (GammaE.measure (P.uF p)).restrict (centeredCube z r hr : Set (SpatialCoordinates d)) =
        (GammaE.measure (DirichletForm.LocalAffineMinimizer.linearFamily uF p :
          DomainL2 (centeredCube z (3 * r) h3r))).restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  let bE := DirichletForm.LocalAffineMinimizer.linearFamily uE
  let bF := DirichletForm.LocalAffineMinimizer.linearFamily uF
  have hEm := prop_conc_linear_family_minimum hd z r hr h3r E GammaE hEc LE KE t uE AE hAE
  have hFm := prop_conc_linear_family_minimum hd z r hr h3r F GammaF hFc LF KF t uF AF hAF
  have hglue (p : Fin d → ℝ) := prop_conc_common_trace_representatives hd z r hr h3r
    E F GammaE GammaF hEc hdom m M hm hM horder (bE p) (bF p) (bE p).property (bF p).property
    (DirichletForm.LocalAffineMinimizer.linearRepresentative uE p)
    (DirichletForm.LocalAffineMinimizer.linearRepresentative uF p) (fun x => ∑ i, p i * x i)
    (DirichletForm.LocalAffineMinimizer.linearRepresentative_continuous uE p)
    (DirichletForm.LocalAffineMinimizer.linearRepresentative_continuous uF p)
    (DirichletForm.LocalAffineMinimizer.linearFamily_coeFn uE p)
    (DirichletForm.LocalAffineMinimizer.linearFamily_coeFn uF p)
    (DirichletForm.LocalAffineMinimizer.linearRepresentative_boundary uE p)
    (DirichletForm.LocalAffineMinimizer.linearRepresentative_boundary uF p) (hFm p).2
  choose vF hvF htrace hGE hGF hminF using hglue
  let e : (Fin d → ℝ) →ₗ[ℝ] DomainL2 (centeredCube z (3 * r) h3r) := E.domain.subtype.comp bE
  let f : (Fin d → ℝ) →ₗ[ℝ] DomainL2 (centeredCube z (3 * r) h3r) := F.domain.subtype.comp bF
  let q : Set (SpatialCoordinates d) := centeredCube z r hr
  have hq := (centeredCube z r hr).isOpen.measurableSet
  let QE := GammaE.localQuadratic e (fun p => (bE p).property) q
  let QF := GammaF.localQuadratic f (fun p => (bF p).property) q
  have hFq (p : Fin d → ℝ) : GammaF.measure (vF p) q = GammaF.measure (bF p) q := by
    have h := congrArg (fun nu => nu Set.univ) (hGF p)
    simpa only [Measure.restrict_apply_univ] using h
  let P : DirichletForm.LocalResponsePair (V := Fin d → ℝ) E.toClosedForm F.toClosedForm GammaE GammaF q
      (E.toClosedForm.killedCoreClosure q) := {
    domain_eq := hdom
    killed := DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _
    boundary := bE
    uF := vF
    QE := QE
    QF := QF
    memF := hvF
    traceF := htrace
    minE := fun p => (hEm p).2
    minF := hminF
    responseE := fun p => GammaE.localQuadratic_apply e (fun p => (bE p).property) q hq p
    responseF := fun p => by
      rw [hFq]
      exact GammaF.localQuadratic_apply f (fun p => (bF p).property) q hq p }
  refine ⟨P, ?_, ?_, ?_⟩
  · intro p
    constructor
    · exact (P.responseE p).trans (hEm p).1
    · exact (P.responseF p).trans ((congrArg ENNReal.toReal (hFq p)).trans (hFm p).1)
  · intro p
    rfl
  · intro p
    exact hGE p


/-- The domain equality and two-sided form order of two limit forms from the operator-level data
(`prop_conc_setup.horder`), via `E.form v v = (limitFormEnergy G v).toReal` on the form domain. -/
theorem aux_prop_conc_typical_pair_form_order {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEe : ∀ u, E.toClosedForm.energy u = limitFormEnergy GE u)
    (hFe : ∀ u, F.toClosedForm.energy u = limitFormEnergy GF u)
    (m M : ℝ) (hdomG : limitFormDomain GE = limitFormDomain GF)
    (horderG : ∀ u ∈ limitFormDomain GE,
      m * (limitFormEnergy GE u).toReal ≤ (limitFormEnergy GF u).toReal ∧
        (limitFormEnergy GF u).toReal ≤ M * (limitFormEnergy GE u).toReal) :
    E.domain = F.domain ∧
      ∀ v ∈ E.domain, m * E.form v v ≤ F.form v v ∧ F.form v v ≤ M * E.form v v := by
  have hEd := aux_thm_prop_domain_eq_of_energy E.toClosedForm GE hEe
  have hFd := aux_thm_prop_domain_eq_of_energy F.toClosedForm GF hFe
  have hdom : E.domain = F.domain := by
    apply SetLike.coe_injective
    exact hEd.trans (hdomG.trans hFd.symm)
  refine ⟨hdom, ?_⟩
  intro v hv
  have hvG : v ∈ limitFormDomain GE := hEd ▸ hv
  have hvF : v ∈ F.domain := hdom ▸ hv
  rw [aux_thm_prop_form_eq_toReal_energy E.toClosedForm GE hEe v hv,
    aux_thm_prop_form_eq_toReal_energy F.toClosedForm GF hFe v hvF]
  exact horderG v hvG

theorem aux_prop_conc_typical_pair_unit_quadratic {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    (Pi.single i (1 : ℝ) : Fin d → ℝ) ⬝ᵥ A.mulVec (Pi.single i (1 : ℝ)) = A i i := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Deterministic assembly of the typical pair data from the actual limit data of one configuration. -/
theorem aux_prop_conc_typical_pair_core
    {d : ℕ} (hd : 2 ≤ d) (zcell : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (t C0 m M : ℝ) (hC0 : 1 ≤ C0) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
    (GE GF : DomainL2 (centeredCube zcell (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube zcell (3 * r) h3r))
    (E F : _root_.DirichletForm (volume.restrict
      (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d))))
    (hEe : ∀ u, E.toClosedForm.energy u = limitFormEnergy GE u)
    (hFe : ∀ u, F.toClosedForm.energy u = limitFormEnergy GF u)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (hEc : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (hFc : ∃ C, DirichletForm.IsCoreOn F.toClosedForm
      (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (hEl : DirichletForm.IsStronglyLocal E.toClosedForm)
    (hFl : DirichletForm.IsStronglyLocal F.toClosedForm)
    (hinside : closure (centeredCube zcell r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d)))
    (AEm AFm : Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ p : Fin d → ℝ,
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube zcell (3 * r) h3r) E.toClosedForm GammaE
        (centeredCube zcell r hr : Set (SpatialCoordinates d)) (fun x => ∑ i, p i * x i))
        ((volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
          (p ⬝ᵥ AEm.mulVec p)))
    (hAF : ∀ p : Fin d → ℝ,
      IsGLB (aux_thm_prop_boundary_energy_set (centeredCube zcell (3 * r) h3r) F.toClosedForm GammaF
        (centeredCube zcell r hr : Set (SpatialCoordinates d)) (fun x => ∑ i, p i * x i))
        ((volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
          (p ⬝ᵥ AFm.mulVec p)))
    (hdomG : limitFormDomain GE = limitFormDomain GF)
    (horderG : ∀ u ∈ limitFormDomain GE,
      m * (limitFormEnergy GE u).toReal ≤ (limitFormEnergy GF u).toReal ∧
        (limitFormEnergy GF u).toReal ≤ M * (limitFormEnergy GE u).toReal)
    (hTE : 0 < Matrix.trace AEm) (K KEc KFc : ℝ) (LEv LFv : Fin d → ℝ) (Dv : ℝ)
    (hDv : Dv = (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
      Matrix.trace AEm)
    (uE : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer zcell r hr h3r E GammaE (Pi.single i 1)
      (LEv i) KEc t)
    (uF : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer zcell r hr h3r F GammaF (Pi.single i 1)
      (LFv i) KFc t)
    (hgrowth : ∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho → rho ≤ r →
      ((ENNReal.ofReal Dv⁻¹ •
        ((∑ i, GammaE.measure (uE i).u) + ∑ i, GammaE.measure (uF i).u))
        (Metric.ball x rho ∩ (centeredCube zcell r hr : Set (SpatialCoordinates d)))).toReal ≤
      K * (rho / r) ^ t) :
    ∃ Y : prop_conc_pair_data (centeredCube zcell (3 * r) h3r) zcell r hr C0 m M,
      (∀ u, Y.E.toClosedForm.energy u = limitFormEnergy GE u) ∧
      (∀ u, Y.F.toClosedForm.energy u = limitFormEnergy GF u) ∧
      (∀ pvec : Fin d → ℝ,
        Y.P.QE pvec = (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
          (pvec ⬝ᵥ AEm.mulVec pvec) ∧
        Y.P.QF pvec = (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal *
          (pvec ⬝ᵥ AFm.mulVec pvec)) ∧
      aux_prop_conc_pair_data_affine Y ∧
      aux_prop_conc_pair_data_growth Y (aux_prop_conc_pair_data_slopes d) t
        (((2 : ℝ) ^ d * ∑ p ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (p i) ^ 2) * K) := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (inv_pos.mpr (zero_lt_one.trans_le hC0)) hm
  have hM0 : 0 ≤ M := (hm0.trans_le hmM).le
  have hEd := aux_thm_prop_domain_eq_of_energy E.toClosedForm GE hEe
  have hFd := aux_thm_prop_domain_eq_of_energy F.toClosedForm GF hFe
  obtain ⟨hdom, horder⟩ := aux_prop_conc_typical_pair_form_order E F GE GF hEe hFe m M hdomG horderG
  obtain ⟨P, hPQ, hPbd, hPuF⟩ := aux_prop_conc_typical_pair_response_pair hd zcell r hr h3r
    E F GammaE GammaF hEc hFc hdom m M hm0 hM0 horder LEv LFv KEc KFc t uE uF AEm AFm hAE hAF
  have hvol : (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal = r ^ d :=
    centeredCube_volume_real zcell hr
  have hDsum : ∑ i : Fin d, P.QE (Pi.single i 1) =
      (volume (centeredCube zcell r hr : Set (SpatialCoordinates d))).toReal * Matrix.trace AEm := by
    simp_rw [(hPQ _).1, aux_prop_conc_typical_pair_unit_quadratic]
    simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
  have hDpos : 0 < ∑ i : Fin d, P.QE (Pi.single i 1) := by
    rw [hDsum, hvol]
    exact mul_pos (pow_pos hr d) hTE
  let Y : prop_conc_pair_data (centeredCube zcell (3 * r) h3r) zcell r hr C0 m M :=
    { hd := hd
      hQ := ⟨zcell, 3 * r, h3r, rfl⟩
      hinside := hinside
      E := E
      F := F
      GammaE := GammaE
      GammaF := GammaF
      D := E.toClosedForm.killedCoreClosure (centeredCube zcell r hr : Set (SpatialCoordinates d))
      P := P
      hEc := hEc
      hFc := hFc
      hEl := hEl
      hFl := hFl
      hC0 := hC0
      hm := hm
      hmM := hmM
      hM := hM
      horder := horder
      CE := ‖GE‖ + 1
      CF := ‖GF‖ + 1
      hCE := by positivity
      hCF := by positivity
      hcoE := fun v hv => by
        have hvG : v ∈ limitFormDomain GE := hEd ▸ hv
        rw [aux_thm_prop_form_eq_toReal_energy E.toClosedForm GE hEe v hv]
        exact aux_prop_conc_typical_pair_coercive GE v hvG
      hcoF := fun v hv => by
        have hvG : v ∈ limitFormDomain GF := hFd ▸ hv
        rw [aux_thm_prop_form_eq_toReal_energy F.toClosedForm GF hFe v hv]
        exact aux_prop_conc_typical_pair_coercive GF v hvG
      hDpos := hDpos }
  refine ⟨Y, hEe, hFe, hPQ, ?_, ?_⟩
  · intro p
    refine ⟨DirichletForm.LocalAffineMinimizer.linearRepresentative uE p,
      DirichletForm.LocalAffineMinimizer.linearRepresentative_continuous uE p, ?_,
      fun x hx => DirichletForm.LocalAffineMinimizer.linearRepresentative_boundary uE p x hx⟩
    have h1 : (Y.P.boundary p : DomainL2 (centeredCube zcell (3 * r) h3r)) =
        (DirichletForm.LocalAffineMinimizer.linearFamily uE p :
          DomainL2 (centeredCube zcell (3 * r) h3r)) := hPbd p
    rw [h1]
    exact DirichletForm.LocalAffineMinimizer.linearFamily_coeFn uE p
  · intro x rho hrho hrhor
    let bE : (Fin d → ℝ) →ₗ[ℝ] DomainL2 (centeredCube zcell (3 * r) h3r) :=
      E.domain.subtype.comp (DirichletForm.LocalAffineMinimizer.linearFamily uE)
    let bF : (Fin d → ℝ) →ₗ[ℝ] DomainL2 (centeredCube zcell (3 * r) h3r) :=
      F.domain.subtype.comp (DirichletForm.LocalAffineMinimizer.linearFamily uF)
    have hbE : ∀ p, bE p ∈ E.toClosedForm.domain := fun p =>
      (DirichletForm.LocalAffineMinimizer.linearFamily uE p).property
    have hbF : ∀ p, bF p ∈ E.toClosedForm.domain := fun p =>
      hdom ▸ (DirichletForm.LocalAffineMinimizer.linearFamily uF p).property
    let B := Metric.ball x rho ∩ (centeredCube zcell r hr : Set (SpatialCoordinates d))
    have hBm : MeasurableSet B :=
      Metric.isOpen_ball.measurableSet.inter (centeredCube zcell r hr).isOpen.measurableSet
    have hBq : B ⊆ (centeredCube zcell r hr : Set (SpatialCoordinates d)) := Set.inter_subset_right
    have hnuB : aux_prop_conc_pair_data_nu Y (aux_prop_conc_pair_data_slopes d) B =
        (ENNReal.ofReal Dv⁻¹ •
          ∑ p ∈ aux_prop_conc_pair_data_slopes d, (GammaE.measure (bE p) + GammaE.measure (bF p))) B := by
      unfold aux_prop_conc_pair_data_nu
      change (ENNReal.ofReal (∑ i : Fin d, P.QE (Pi.single i 1))⁻¹ •
        ∑ p ∈ aux_prop_conc_pair_data_slopes d, (GammaE.measure (P.boundary p) +
          GammaE.measure (P.uF p))) B = _
      rw [hDsum, ← hDv]
      simp only [Measure.smul_apply, smul_eq_mul, Measure.finset_sum_apply, Measure.add_apply]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      · have h : (P.boundary p : DomainL2 (centeredCube zcell (3 * r) h3r)) = bE p := hPbd p
        rw [h]
      · have h := congrArg (fun μ : Measure (SpatialCoordinates d) => μ B) (hPuF p)
        simp only [Measure.restrict_apply hBm, Set.inter_eq_left.mpr hBq] at h
        exact h
    have hDposR : 0 < Dv := by
      rw [hDv, hvol]
      exact mul_pos (pow_pos hr d) hTE
    have hsl := prop_conc_slope_measure_bound E.toClosedForm GammaE bE bF hbE hbF
      (aux_prop_conc_pair_data_slopes d) Dv hDposR B hBm
    have hcoord : (∑ i : Fin d, (GammaE.measure (bE (Pi.single i 1)) +
        GammaE.measure (bF (Pi.single i 1)))) =
        (∑ i, GammaE.measure (uE i).u) + ∑ i, GammaE.measure (uF i).u := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : bE (Pi.single i 1) = (uE i).u :=
        DirichletForm.LocalAffineMinimizer.linearFamily_single uE i
      have h2 : bF (Pi.single i 1) = (uF i).u :=
        DirichletForm.LocalAffineMinimizer.linearFamily_single uF i
      rw [h1, h2]
    rw [hnuB]
    refine hsl.trans ?_
    rw [hcoord]
    have hcs : 0 ≤ (2 : ℝ) ^ d * ∑ p ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (p i) ^ 2 := by
      positivity
    calc _ ≤ ((2 : ℝ) ^ d * ∑ p ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (p i) ^ 2) *
          (K * (rho / r) ^ t) := mul_le_mul_of_nonneg_left (hgrowth x rho hrho hrhor) hcs
      _ = _ := by ring

/-- `ResponseSpace` with the killed graph as variation space is the canonical killed response space. -/
theorem aux_prop_conc_typical_pair_response_space_eq {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
      ‖(w : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) w‖)
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q) : S = killedResponseSpace hP := by
  cases S with
  | mk sp lw cl po =>
    simp only [killedResponseSpace] at hS ⊢
    subst hS
    rfl

/-- Diagonal of the limiting volume-normalized affine responses, defined pathwise by `limUnder`. -/
def aux_prop_conc_typical_pair_diag {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (zcell : SpatialCoordinates d)
    (rr : ℝ) (hr : 0 < rr)
    (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell rr hr),
      ‖(v : SobolevData (centeredCube zcell rr hr)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell rr hr)) v‖)
    (N : ℕ → ℕ) (om : BilateralField d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal (fun i => limUnder atTop (fun n => affineDirichletResponse
    (centeredCube_isBounded zcell hr) hP (cutoffPositiveCoefficient M H om (N n) zcell hr)
      (Pi.single i 1) /
    (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal))

/-- Almost-sure convergence on the represented space passes to the chaos law, for the `limUnder` diagonal. -/
theorem aux_prop_conc_typical_pair_diag_ae {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (zcell : SpatialCoordinates d) (rr : ℝ) (hr : 0 < rr)
    (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell rr hr),
      ‖(v : SobolevData (centeredCube zcell rr hr)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell rr hr)) v‖)
    (N : ℕ → ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (hfm : Measurable field) (hfmap : Measure.map field P = (chaosSampleLaw M).toMeasure)
    (hex : ∀ᵐ ω ∂P, ∀ i : Fin d, ∃ l : ℝ, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient M H (field ω) (N n) zcell hr) (Pi.single i 1) /
        (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal) atTop (𝓝 l)) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ i : Fin d, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient M H om (N n) zcell hr) (Pi.single i 1) /
        (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal) atTop
      (𝓝 (aux_prop_conc_typical_pair_diag M H zcell rr hr hP N om i i)) := by
  let A : Set (BilateralField d) := {om | ∀ i : Fin d, ∃ l : ℝ, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient M H om (N n) zcell hr) (Pi.single i 1) /
        (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal) atTop (𝓝 l)}
  have hA : MeasurableSet A := by
    have : A = ⋂ i : Fin d, {om | ∃ l : ℝ, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient M H om (N n) zcell hr) (Pi.single i 1) /
        (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal) atTop (𝓝 l)} := by
      ext om; simp [A]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    exact measurableSet_exists_tendsto fun n =>
      (aux_prop_conc_resp_measurable M H hH (N n) zcell hr hP (Pi.single i 1)).div_const _
  have hnull : (chaosSampleLaw M).toMeasure Aᶜ = 0 := by
    rw [← hfmap, Measure.map_apply hfm hA.compl]
    exact ae_iff.mp hex
  have hae : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, om ∈ A := by
    rw [ae_iff]
    simpa using hnull
  filter_upwards [hae] with om hom i
  exact tendsto_nhds_limUnder (hom i) |> fun h => by
    simpa [aux_prop_conc_typical_pair_diag, Matrix.diagonal_apply_eq] using h

/-- The actual limit datum of one cutoff sequence on the padded cell, bundled as `LocalAffineLimitData`. -/
def aux_prop_conc_typical_pair_limit_data {d : ℕ}
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (zcell : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (S : ResponseSpace (centeredCube zcell (3 * r) h3r))
    (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell r hr),
      ‖(v : SobolevData (centeredCube zcell r hr)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) v‖)
    (N : ℕ → ℕ)
    (GN : ℕ → DomainL2 (centeredCube zcell (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube zcell (3 * r) h3r))
    (G : DomainL2 (centeredCube zcell (3 * r) h3r) →L[ℝ] DomainL2 (centeredCube zcell (3 * r) h3r))
    (E : _root_.DirichletForm (volume.restrict
      (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm) (L : Fin d → ℝ)
    (hGN : ∀ n f, GN n f = (responseSolution S
      (cutoffPositiveCoefficient model H om (N n) zcell h3r)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hlim : Tendsto GN atTop (𝓝 G))
    (hE : ∀ v, E.toClosedForm.energy v = limitFormEnergy G v)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zcell (3 * r) h3r : Set (SpatialCoordinates d)) C)
    (haff : ∀ i : Fin d, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient model H om (N n) zcell hr) (Pi.single i 1)) atTop (𝓝 (L i))) :
    LocalAffineLimitData S (fun n => cutoffPositiveCoefficient model H om (N n) zcell h3r)
      (centeredCube_isBounded zcell hr) hP
      (fun n => cutoffPositiveCoefficient model H om (N n) zcell hr) L where
  GN := GN
  G := G
  E := E
  Gamma := Gamma
  inverse_eq := hGN
  inverse_tendsto := hlim
  energy_eq := hE
  core := hcore
  affine_tendsto := haff

/-- Volume-normalized responses converging to `a` means the raw responses converge to `|q| a`. -/
theorem aux_prop_conc_typical_pair_raw_tendsto (f : ℕ → ℝ) (v a : ℝ) (hv : 0 < v)
    (h : Tendsto (fun n => f n / v) atTop (𝓝 a)) : Tendsto f atTop (𝓝 (v * a)) := by
  have h2 := h.const_mul v
  refine h2.congr' (Filter.Eventually.of_forall fun n => ?_)
  field_simp


/-- One side (`E` or `F`) of the typical pair: the identified form with its energy measure, core,
strong locality (transported from the regular strongly local realization by equality of energies),
containment and the boundary minimum identifying the affine matrix. -/
theorem aux_prop_conc_typical_pair_side {d : ℕ} (zcell : SpatialCoordinates d) (rr : ℝ)
    (hr : 0 < rr) (h3r : 0 < 3 * rr)
    (G : DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ] DomainL2 (centeredCube zcell (3 * rr) h3r))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hId : Nonempty (aux_prop_conc_LocalAffineIdentification (centeredCube zcell (3 * rr) h3r)
      (centeredCube zcell rr hr : Set (SpatialCoordinates d)) G A))
    (hStr : ∃ E' : _root_.DirichletForm (volume.restrict
        (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d))),
      (∀ u, E'.toClosedForm.energy u = limitFormEnergy G u) ∧
        DirichletForm.IsStronglyLocal E'.toClosedForm) :
    ∃ (E : _root_.DirichletForm (volume.restrict
        (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d))))
      (Gam : DirichletForm.EnergyMeasure E.toClosedForm),
      (∀ u, E.toClosedForm.energy u = limitFormEnergy G u) ∧
      (∃ C, DirichletForm.IsCoreOn E.toClosedForm
        (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d)) C) ∧
      DirichletForm.IsStronglyLocal E.toClosedForm ∧
      closure (centeredCube zcell rr hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d)) ∧
      (∀ p : Fin d → ℝ,
        IsGLB (aux_thm_prop_boundary_energy_set (centeredCube zcell (3 * rr) h3r) E.toClosedForm
          Gam (centeredCube zcell rr hr : Set (SpatialCoordinates d)) (fun x => ∑ i, p i * x i))
          ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
            (p ⬝ᵥ A.mulVec p))) := by
  obtain ⟨id⟩ := hId
  obtain ⟨E', hE'e, hE'l⟩ := hStr
  exact ⟨id.form, id.gamma, id.energy_eq, id.core,
    aux_prop_conc_typical_pair_isStronglyLocal_of_energy_eq
      (fun u => (id.energy_eq u).trans (hE'e u).symm) hE'l,
    id.contained, id.boundary_minimum⟩

/-- The pointwise (fixed configuration) assembly of the typical pair: sides, limit data, the growth helper
(consumed as `hKa`), and the deterministic core. -/
theorem aux_prop_conc_typical_pair_omega {d : ℕ}
    (hd : 2 ≤ d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (zcell : SpatialCoordinates d) (rr : ℝ) (hr : 0 < rr) (h3r : 0 < 3 * rr)
    (t C0 m M : ℝ) (hC0 : 1 ≤ C0) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
    (hPpad : ∃ C : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube zcell (3 * rr) h3r),
      ‖(w : SobolevData (centeredCube zcell (3 * rr) h3r)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell (3 * rr) h3r)) w‖)
    (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell rr hr),
      ‖(v : SobolevData (centeredCube zcell rr hr)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell rr hr)) v‖)
    (NE NF : ℕ → ℕ)
    (GNE GNF : ℕ → DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
      DomainL2 (centeredCube zcell (3 * rr) h3r))
    (GEo GFo : DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
      DomainL2 (centeredCube zcell (3 * rr) h3r))
    (hGNE : ∀ n f, GNE n f = (responseSolution (killedResponseSpace hPpad)
      (cutoffPositiveCoefficient model H om (NE n) zcell h3r)
      ((sobolevVolumeLoad f).comp (killedResponseSpace hPpad).space.subtypeL)).val.1)
    (hGNF : ∀ n f, GNF n f = (responseSolution (killedResponseSpace hPpad)
      (cutoffPositiveCoefficient model H om (NF n) zcell h3r)
      ((sobolevVolumeLoad f).comp (killedResponseSpace hPpad).space.subtypeL)).val.1)
    (hlimE : Tendsto GNE atTop (𝓝 GEo)) (hlimF : Tendsto GNF atTop (𝓝 GFo))
    (hdomG : limitFormDomain GEo = limitFormDomain GFo)
    (horderG : ∀ u ∈ limitFormDomain GEo,
      m * (limitFormEnergy GEo u).toReal ≤ (limitFormEnergy GFo u).toReal ∧
        (limitFormEnergy GFo u).toReal ≤ M * (limitFormEnergy GEo u).toReal)
    (AEm AFm AEdm AFdm : Matrix (Fin d) (Fin d) ℝ)
    (hdiagE : ∀ i, AEdm i i = AEm i i) (hdiagF : ∀ i, AFdm i i = AFm i i)
    (hAEfull : ∀ p : Fin d → ℝ, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient model H om (NE n) zcell hr) p /
        (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal) atTop
      (𝓝 (p ⬝ᵥ AEm.mulVec p)))
    (hAFfull : ∀ p : Fin d → ℝ, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient model H om (NF n) zcell hr) p /
        (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal) atTop
      (𝓝 (p ⬝ᵥ AFm.mulVec p)))
    (hIdE : Nonempty (aux_prop_conc_LocalAffineIdentification (centeredCube zcell (3 * rr) h3r)
      (centeredCube zcell rr hr : Set (SpatialCoordinates d)) GEo AEm))
    (hIdF : Nonempty (aux_prop_conc_LocalAffineIdentification (centeredCube zcell (3 * rr) h3r)
      (centeredCube zcell rr hr : Set (SpatialCoordinates d)) GFo AFm))
    (hStrE : ∃ E' : _root_.DirichletForm (volume.restrict
        (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d))),
      (∀ u, E'.toClosedForm.energy u = limitFormEnergy GEo u) ∧
        DirichletForm.IsStronglyLocal E'.toClosedForm)
    (hStrF : ∃ E' : _root_.DirichletForm (volume.restrict
        (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d))),
      (∀ u, E'.toClosedForm.energy u = limitFormEnergy GFo u) ∧
        DirichletForm.IsStronglyLocal E'.toClosedForm)
    (hTp : 0 < Matrix.trace AEdm) (K KE KF : ℝ)
    (hKa : ∀ (DE : LocalAffineLimitData (killedResponseSpace hPpad)
          (fun n => cutoffPositiveCoefficient model H om (NE n) zcell h3r)
          (centeredCube_isBounded zcell hr) hP
          (fun n => cutoffPositiveCoefficient model H om (NE n) zcell hr)
          (fun i => (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
            AEdm i i))
        (DF : LocalAffineLimitData (killedResponseSpace hPpad)
          (fun n => cutoffPositiveCoefficient model H om (NF n) zcell h3r)
          (centeredCube_isBounded zcell hr) hP
          (fun n => cutoffPositiveCoefficient model H om (NF n) zcell hr)
          (fun i => (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
            AFdm i i)),
        DE.E.domain = DF.E.domain →
        ∀ m' : ℝ, C0⁻¹ ≤ m' →
        ∀ Mo : ℝ, m' ≤ Mo → Mo ≤ C0 →
        (∀ v ∈ DE.E.domain, m' * DE.E.form v v ≤ DF.E.form v v) →
        (∀ v ∈ DE.E.domain, DF.E.form v v ≤ Mo * DE.E.form v v) →
        ∃ (uE : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer zcell rr hr h3r DE.E DE.Gamma
            (Pi.single i 1)
            ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
              AEdm i i) KE t)
          (uF : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer zcell rr hr h3r DF.E DF.Gamma
            (Pi.single i 1)
            ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
              AFdm i i) KF t),
        ∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho → rho ≤ rr →
          ((ENNReal.ofReal ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
              Matrix.trace AEdm)⁻¹ •
            ((∑ i, DE.Gamma.measure (uE i).u) + ∑ i, DE.Gamma.measure (uF i).u))
            (Metric.ball x rho ∩ (centeredCube zcell rr hr : Set (SpatialCoordinates d)))).toReal ≤
          K * (rho / rr) ^ t) :
    ∃ Y : prop_conc_pair_data (centeredCube zcell (3 * rr) h3r) zcell rr hr C0 m M,
      (∀ u, Y.E.toClosedForm.energy u = limitFormEnergy GEo u) ∧
      (∀ u, Y.F.toClosedForm.energy u = limitFormEnergy GFo u) ∧
      (∀ pvec : Fin d → ℝ,
        Y.P.QE pvec = (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
          (pvec ⬝ᵥ AEm.mulVec pvec) ∧
        Y.P.QF pvec = (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
          (pvec ⬝ᵥ AFm.mulVec pvec)) ∧
      aux_prop_conc_pair_data_affine Y ∧
      aux_prop_conc_pair_data_growth Y (aux_prop_conc_pair_data_slopes d) t
        (((2 : ℝ) ^ d * ∑ p ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (p i) ^ 2) * K) := by
  obtain ⟨E, GammaE, hEe, hEc, hEl, hinside, hAE⟩ :=
    aux_prop_conc_typical_pair_side zcell rr hr h3r GEo AEm hIdE hStrE
  obtain ⟨F, GammaF, hFe, hFc, hFl, -, hAF⟩ :=
    aux_prop_conc_typical_pair_side zcell rr hr h3r GFo AFm hIdF hStrF
  obtain ⟨hdomEF, hlowup⟩ := aux_prop_conc_typical_pair_form_order E F GEo GFo hEe hFe m M
    hdomG horderG
  have hvol : (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal = rr ^ d :=
    centeredCube_volume_real zcell hr
  have hvpos : 0 < (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal := by
    rw [hvol]; exact pow_pos hr d
  have haffE : ∀ i : Fin d, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient model H om (NE n) zcell hr) (Pi.single i 1)) atTop
      (𝓝 ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal * AEdm i i)) := by
    intro i
    have h := hAEfull (Pi.single i 1)
    rw [aux_prop_conc_typical_pair_unit_quadratic, ← hdiagE] at h
    exact aux_prop_conc_typical_pair_raw_tendsto _ _ _ hvpos h
  have haffF : ∀ i : Fin d, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient model H om (NF n) zcell hr) (Pi.single i 1)) atTop
      (𝓝 ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal * AFdm i i)) := by
    intro i
    have h := hAFfull (Pi.single i 1)
    rw [aux_prop_conc_typical_pair_unit_quadratic, ← hdiagF] at h
    exact aux_prop_conc_typical_pair_raw_tendsto _ _ _ hvpos h
  obtain ⟨uE, uF, hgr⟩ := hKa
    (aux_prop_conc_typical_pair_limit_data model H om zcell rr hr h3r (killedResponseSpace hPpad)
      hP NE GNE GEo E GammaE _ hGNE hlimE hEe hEc haffE)
    (aux_prop_conc_typical_pair_limit_data model H om zcell rr hr h3r (killedResponseSpace hPpad)
      hP NF GNF GFo F GammaF _ hGNF hlimF hFe hFc haffF)
    hdomEF m hm M hmM hM (fun v hv => (hlowup v hv).1) (fun v hv => (hlowup v hv).2)
  have htrE : Matrix.trace AEdm = Matrix.trace AEm := by
    simp only [Matrix.trace, Matrix.diag_apply, hdiagE]
  have hTE : 0 < Matrix.trace AEm := by rw [← htrE]; exact hTp
  exact aux_prop_conc_typical_pair_core hd zcell rr hr h3r t C0 m M hC0 hm hmM hM GEo GFo E F hEe
    hFe GammaE GammaF hEc hFc hEl hFl hinside AEm AFm hAE hAF hdomG horderG hTE K KE KF
    (fun i => (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal * AEdm i i)
    (fun i => (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal * AFdm i i)
    ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
      Matrix.trace AEdm)
    (by rw [htrE]) uE uF hgr

/-- The chaos-a.s. existence of the diagonal limits from the joint setup limits on the represented space. -/
theorem aux_prop_conc_typical_pair_diag_ae_of_setup {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (zcell : SpatialCoordinates d) (k : ℕ)
    (hr0 : 0 < (3 : ℝ) ^ (-(k : ℝ)))
    (hPk : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph
        (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0),
      ‖(v : SobolevData (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph
          (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0)) v‖)
    (N : ℕ → ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (hfm : Measurable field) (hfmap : Measure.map field P = (chaosSampleLaw model).toMeasure)
    (AEo : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hAEs : ∀ᵐ ω ∂P, ∀ pvec : Fin d → ℝ,
      Tendsto (fun j : ℕ => aux_prop_conc_setup_resp model H zcell k hPk (N j) (field ω) pvec)
        atTop (𝓝 (pvec ⬝ᵥ (AEo ω).mulVec pvec))) :
    ∀ᵐ om ∂(chaosSampleLaw model).toMeasure, ∀ i : Fin d, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr0) hPk
      (cutoffPositiveCoefficient model H om (N n) zcell hr0) (Pi.single i 1) /
        (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 :
          Set (SpatialCoordinates d))).toReal) atTop
      (𝓝 (aux_prop_conc_typical_pair_diag model H zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 hPk N
        om i i)) := by
  refine aux_prop_conc_typical_pair_diag_ae model H hH zcell _ hr0 hPk N P field hfm hfmap ?_
  filter_upwards [hAEs] with ω hω i
  refine ⟨AEo ω i i, ?_⟩
  have h := hω (Pi.single i 1)
  rw [aux_prop_conc_typical_pair_unit_quadratic] at h
  exact h

/-- One side from the raw model-level identification and regular-form statements. -/
theorem aux_prop_conc_typical_pair_side_raw {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (zcell : SpatialCoordinates d) (rr : ℝ) (hr : 0 < rr) (h3r : 0 < 3 * rr)
    (hPpad : ∃ C : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube zcell (3 * rr) h3r),
      ‖(w : SobolevData (centeredCube zcell (3 * rr) h3r)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell (3 * rr) h3r)) w‖)
    (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell rr hr),
      ‖(v : SobolevData (centeredCube zcell rr hr)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell rr hr)) v‖)
    (N : ℕ → ℕ)
    (hAff : ∀ (S : ResponseSpace (centeredCube zcell (3 * rr) h3r)),
      S.space = killedSobolevGraph (centeredCube zcell (3 * rr) h3r) →
      ∀ (GN : ℕ → DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * rr) h3r))
        (G : DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * rr) h3r))
        (A : Matrix (Fin d) (Fin d) ℝ),
      (∀ n f, GN n f =
        (responseSolution S (cutoffPositiveCoefficient model H om (N n) zcell h3r)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) →
      (∀ p : Fin d → ℝ,
        Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded zcell hr) hP
          (cutoffPositiveCoefficient model H om (N n) zcell hr) p /
          (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal)
          atTop (𝓝 (p ⬝ᵥ A.mulVec p))) →
      Nonempty (aux_prop_conc_LocalAffineIdentification (centeredCube zcell (3 * rr) h3r)
        (centeredCube zcell rr hr : Set (SpatialCoordinates d)) G A))
    (hGam : ∀ (GN : ℕ → DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * rr) h3r))
        (G : DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * rr) h3r)),
      (∀ n f, GN n f =
        (responseSolution (killedResponseSpace hPpad)
          (cutoffPositiveCoefficient model H om (N n) zcell h3r)
          ((sobolevVolumeLoad f).comp (killedResponseSpace hPpad).space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) →
      ∃ E : _root_.DirichletForm (volume.restrict
          (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d))),
        (∀ u, E.toClosedForm.energy u = limitFormEnergy G u) ∧
        DirichletForm.HasNormalContractions E ∧
        (∃ C, DirichletForm.IsCoreOn E.toClosedForm
          (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d)) C) ∧
        DirichletForm.IsRegular E.toClosedForm ∧
        DirichletForm.IsStronglyLocal E.toClosedForm ∧
        Nonempty (DirichletForm.EnergyMeasure E.toClosedForm))
    (GN : ℕ → DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
      DomainL2 (centeredCube zcell (3 * rr) h3r))
    (G : DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
      DomainL2 (centeredCube zcell (3 * rr) h3r))
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hGN : ∀ n f, GN n f = (responseSolution (killedResponseSpace hPpad)
      (cutoffPositiveCoefficient model H om (N n) zcell h3r)
      ((sobolevVolumeLoad f).comp (killedResponseSpace hPpad).space.subtypeL)).val.1)
    (hlim : Tendsto GN atTop (𝓝 G))
    (hA : ∀ p : Fin d → ℝ, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient model H om (N n) zcell hr) p /
        (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal) atTop
      (𝓝 (p ⬝ᵥ A.mulVec p))) :
    ∃ (E : _root_.DirichletForm (volume.restrict
        (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d))))
      (Gam : DirichletForm.EnergyMeasure E.toClosedForm),
      (∀ u, E.toClosedForm.energy u = limitFormEnergy G u) ∧
      (∃ C, DirichletForm.IsCoreOn E.toClosedForm
        (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d)) C) ∧
      DirichletForm.IsStronglyLocal E.toClosedForm ∧
      closure (centeredCube zcell rr hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d)) ∧
      (∀ p : Fin d → ℝ,
        IsGLB (aux_thm_prop_boundary_energy_set (centeredCube zcell (3 * rr) h3r) E.toClosedForm
          Gam (centeredCube zcell rr hr : Set (SpatialCoordinates d)) (fun x => ∑ i, p i * x i))
          ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
            (p ⬝ᵥ A.mulVec p))) := by
  refine aux_prop_conc_typical_pair_side zcell rr hr h3r G A
    (hAff (killedResponseSpace hPpad) rfl GN G A hGN hlim hA) ?_
  obtain ⟨E', hE'e, -, -, -, hE'l, -⟩ := hGam GN G hGN hlim
  exact ⟨E', hE'e, hE'l⟩

/-- Pointwise assembly consuming the raw model-level identification/regularity statements. -/
theorem aux_prop_conc_typical_pair_omega2 {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (zcell : SpatialCoordinates d) (rr : ℝ) (hr : 0 < rr) (h3r : 0 < 3 * rr)
    (t C0 m M : ℝ) (hC0 : 1 ≤ C0) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
    (hPpad : ∃ C : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube zcell (3 * rr) h3r),
      ‖(w : SobolevData (centeredCube zcell (3 * rr) h3r)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell (3 * rr) h3r)) w‖)
    (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zcell rr hr),
      ‖(v : SobolevData (centeredCube zcell rr hr)).1‖ ≤
        C * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell rr hr)) v‖)
    (NE NF : ℕ → ℕ)
    (GNE GNF : ℕ → DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
      DomainL2 (centeredCube zcell (3 * rr) h3r))
    (GEo GFo : DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
      DomainL2 (centeredCube zcell (3 * rr) h3r))
    (hGNE : ∀ n f, GNE n f = (responseSolution (killedResponseSpace hPpad)
      (cutoffPositiveCoefficient model H om (NE n) zcell h3r)
      ((sobolevVolumeLoad f).comp (killedResponseSpace hPpad).space.subtypeL)).val.1)
    (hGNF : ∀ n f, GNF n f = (responseSolution (killedResponseSpace hPpad)
      (cutoffPositiveCoefficient model H om (NF n) zcell h3r)
      ((sobolevVolumeLoad f).comp (killedResponseSpace hPpad).space.subtypeL)).val.1)
    (hlimE : Tendsto GNE atTop (𝓝 GEo)) (hlimF : Tendsto GNF atTop (𝓝 GFo))
    (hdomG : limitFormDomain GEo = limitFormDomain GFo)
    (horderG : ∀ u ∈ limitFormDomain GEo,
      m * (limitFormEnergy GEo u).toReal ≤ (limitFormEnergy GFo u).toReal ∧
        (limitFormEnergy GFo u).toReal ≤ M * (limitFormEnergy GEo u).toReal)
    (AEm AFm AEdm AFdm : Matrix (Fin d) (Fin d) ℝ)
    (hdiagE : ∀ i, AEdm i i = AEm i i) (hdiagF : ∀ i, AFdm i i = AFm i i)
    (hAEfull : ∀ p : Fin d → ℝ, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient model H om (NE n) zcell hr) p /
        (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal) atTop
      (𝓝 (p ⬝ᵥ AEm.mulVec p)))
    (hAFfull : ∀ p : Fin d → ℝ, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient model H om (NF n) zcell hr) p /
        (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal) atTop
      (𝓝 (p ⬝ᵥ AFm.mulVec p)))
    (hAffE : ∀ (S : ResponseSpace (centeredCube zcell (3 * rr) h3r)),
      S.space = killedSobolevGraph (centeredCube zcell (3 * rr) h3r) →
      ∀ (GN : ℕ → DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * rr) h3r))
        (G : DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * rr) h3r))
        (A : Matrix (Fin d) (Fin d) ℝ),
      (∀ n f, GN n f =
        (responseSolution S (cutoffPositiveCoefficient model H om (NE n) zcell h3r)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) →
      (∀ p : Fin d → ℝ,
        Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded zcell hr) hP
          (cutoffPositiveCoefficient model H om (NE n) zcell hr) p /
          (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal)
          atTop (𝓝 (p ⬝ᵥ A.mulVec p))) →
      Nonempty (aux_prop_conc_LocalAffineIdentification (centeredCube zcell (3 * rr) h3r)
        (centeredCube zcell rr hr : Set (SpatialCoordinates d)) G A))
    (hGamE : ∀ (GN : ℕ → DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * rr) h3r))
        (G : DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * rr) h3r)),
      (∀ n f, GN n f =
        (responseSolution (killedResponseSpace hPpad)
          (cutoffPositiveCoefficient model H om (NE n) zcell h3r)
          ((sobolevVolumeLoad f).comp (killedResponseSpace hPpad).space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) →
      ∃ E : _root_.DirichletForm (volume.restrict
          (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d))),
        (∀ u, E.toClosedForm.energy u = limitFormEnergy G u) ∧
        DirichletForm.HasNormalContractions E ∧
        (∃ C, DirichletForm.IsCoreOn E.toClosedForm
          (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d)) C) ∧
        DirichletForm.IsRegular E.toClosedForm ∧
        DirichletForm.IsStronglyLocal E.toClosedForm ∧
        Nonempty (DirichletForm.EnergyMeasure E.toClosedForm))
    (hAffF : ∀ (S : ResponseSpace (centeredCube zcell (3 * rr) h3r)),
      S.space = killedSobolevGraph (centeredCube zcell (3 * rr) h3r) →
      ∀ (GN : ℕ → DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * rr) h3r))
        (G : DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * rr) h3r))
        (A : Matrix (Fin d) (Fin d) ℝ),
      (∀ n f, GN n f =
        (responseSolution S (cutoffPositiveCoefficient model H om (NF n) zcell h3r)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) →
      (∀ p : Fin d → ℝ,
        Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded zcell hr) hP
          (cutoffPositiveCoefficient model H om (NF n) zcell hr) p /
          (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal)
          atTop (𝓝 (p ⬝ᵥ A.mulVec p))) →
      Nonempty (aux_prop_conc_LocalAffineIdentification (centeredCube zcell (3 * rr) h3r)
        (centeredCube zcell rr hr : Set (SpatialCoordinates d)) G A))
    (hGamF : ∀ (GN : ℕ → DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * rr) h3r))
        (G : DomainL2 (centeredCube zcell (3 * rr) h3r) →L[ℝ]
          DomainL2 (centeredCube zcell (3 * rr) h3r)),
      (∀ n f, GN n f =
        (responseSolution (killedResponseSpace hPpad)
          (cutoffPositiveCoefficient model H om (NF n) zcell h3r)
          ((sobolevVolumeLoad f).comp (killedResponseSpace hPpad).space.subtypeL)).val.1) →
      Tendsto GN atTop (𝓝 G) →
      ∃ E : _root_.DirichletForm (volume.restrict
          (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d))),
        (∀ u, E.toClosedForm.energy u = limitFormEnergy G u) ∧
        DirichletForm.HasNormalContractions E ∧
        (∃ C, DirichletForm.IsCoreOn E.toClosedForm
          (centeredCube zcell (3 * rr) h3r : Set (SpatialCoordinates d)) C) ∧
        DirichletForm.IsRegular E.toClosedForm ∧
        DirichletForm.IsStronglyLocal E.toClosedForm ∧
        Nonempty (DirichletForm.EnergyMeasure E.toClosedForm))
    (hTp : 0 < Matrix.trace AEdm) (K KE KF : ℝ)
    (hKa : ∀ (DE : LocalAffineLimitData (killedResponseSpace hPpad)
          (fun n => cutoffPositiveCoefficient model H om (NE n) zcell h3r)
          (centeredCube_isBounded zcell hr) hP
          (fun n => cutoffPositiveCoefficient model H om (NE n) zcell hr)
          (fun i => (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
            AEdm i i))
        (DF : LocalAffineLimitData (killedResponseSpace hPpad)
          (fun n => cutoffPositiveCoefficient model H om (NF n) zcell h3r)
          (centeredCube_isBounded zcell hr) hP
          (fun n => cutoffPositiveCoefficient model H om (NF n) zcell hr)
          (fun i => (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
            AFdm i i)),
        DE.E.domain = DF.E.domain →
        ∀ m' : ℝ, C0⁻¹ ≤ m' →
        ∀ Mo : ℝ, m' ≤ Mo → Mo ≤ C0 →
        (∀ v ∈ DE.E.domain, m' * DE.E.form v v ≤ DF.E.form v v) →
        (∀ v ∈ DE.E.domain, DF.E.form v v ≤ Mo * DE.E.form v v) →
        ∃ (uE : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer zcell rr hr h3r DE.E DE.Gamma
            (Pi.single i 1)
            ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
              AEdm i i) KE t)
          (uF : ∀ i : Fin d, DirichletForm.LocalAffineMinimizer zcell rr hr h3r DF.E DF.Gamma
            (Pi.single i 1)
            ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
              AFdm i i) KF t),
        ∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho → rho ≤ rr →
          ((ENNReal.ofReal ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
              Matrix.trace AEdm)⁻¹ •
            ((∑ i, DE.Gamma.measure (uE i).u) + ∑ i, DE.Gamma.measure (uF i).u))
            (Metric.ball x rho ∩ (centeredCube zcell rr hr : Set (SpatialCoordinates d)))).toReal ≤
          K * (rho / rr) ^ t) :
    ∃ Y : prop_conc_pair_data (centeredCube zcell (3 * rr) h3r) zcell rr hr C0 m M,
      (∀ u, Y.E.toClosedForm.energy u = limitFormEnergy GEo u) ∧
      (∀ u, Y.F.toClosedForm.energy u = limitFormEnergy GFo u) ∧
      (∀ pvec : Fin d → ℝ,
        Y.P.QE pvec = (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
          (pvec ⬝ᵥ AEm.mulVec pvec) ∧
        Y.P.QF pvec = (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
          (pvec ⬝ᵥ AFm.mulVec pvec)) ∧
      aux_prop_conc_pair_data_affine Y ∧
      aux_prop_conc_pair_data_growth Y (aux_prop_conc_pair_data_slopes d) t
        (((2 : ℝ) ^ d * ∑ p ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (p i) ^ 2) * K) := by
  obtain ⟨E, GammaE, hEe, hEc, hEl, hinside, hAE⟩ :=
    aux_prop_conc_typical_pair_side_raw model H om zcell rr hr h3r hPpad hP NE hAffE hGamE GNE GEo
      AEm hGNE hlimE hAEfull
  obtain ⟨F, GammaF, hFe, hFc, hFl, -, hAF⟩ :=
    aux_prop_conc_typical_pair_side_raw model H om zcell rr hr h3r hPpad hP NF hAffF hGamF GNF GFo
      AFm hGNF hlimF hAFfull
  obtain ⟨hdomEF, hlowup⟩ := aux_prop_conc_typical_pair_form_order E F GEo GFo hEe hFe m M
    hdomG horderG
  have hvol : (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal = rr ^ d :=
    centeredCube_volume_real zcell hr
  have hvpos : 0 < (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal := by
    rw [hvol]; exact pow_pos hr d
  have haffE : ∀ i : Fin d, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient model H om (NE n) zcell hr) (Pi.single i 1)) atTop
      (𝓝 ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal * AEdm i i)) := by
    intro i
    have h := hAEfull (Pi.single i 1)
    rw [aux_prop_conc_typical_pair_unit_quadratic, ← hdiagE] at h
    exact aux_prop_conc_typical_pair_raw_tendsto _ _ _ hvpos h
  have haffF : ∀ i : Fin d, Tendsto (fun n => affineDirichletResponse
      (centeredCube_isBounded zcell hr) hP
      (cutoffPositiveCoefficient model H om (NF n) zcell hr) (Pi.single i 1)) atTop
      (𝓝 ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal * AFdm i i)) := by
    intro i
    have h := hAFfull (Pi.single i 1)
    rw [aux_prop_conc_typical_pair_unit_quadratic, ← hdiagF] at h
    exact aux_prop_conc_typical_pair_raw_tendsto _ _ _ hvpos h
  obtain ⟨uE, uF, hgr⟩ := hKa
    (aux_prop_conc_typical_pair_limit_data model H om zcell rr hr h3r (killedResponseSpace hPpad)
      hP NE GNE GEo E GammaE _ hGNE hlimE hEe hEc haffE)
    (aux_prop_conc_typical_pair_limit_data model H om zcell rr hr h3r (killedResponseSpace hPpad)
      hP NF GNF GFo F GammaF _ hGNF hlimF hFe hFc haffF)
    hdomEF m hm M hmM hM (fun v hv => (hlowup v hv).1) (fun v hv => (hlowup v hv).2)
  have htrE : Matrix.trace AEdm = Matrix.trace AEm := by
    simp only [Matrix.trace, Matrix.diag_apply, hdiagE]
  have hTE : 0 < Matrix.trace AEm := by rw [← htrE]; exact hTp
  exact aux_prop_conc_typical_pair_core hd zcell rr hr h3r t C0 m M hC0 hm hmM hM GEo GFo E F hEe
    hFe GammaE GammaF hEc hFc hEl hFl hinside AEm AFm hAE hAF hdomG horderG hTE K KE KF
    (fun i => (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal * AEdm i i)
    (fun i => (volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal * AFdm i i)
    ((volume (centeredCube zcell rr hr : Set (SpatialCoordinates d))).toReal *
      Matrix.trace AEdm)
    (by rw [htrE]) uE uF hgr


/-- Typical pair data with growth (paper `prop-conc`, Step 2 and the identification of `A_E`, `A_F`). -/
theorem prop_conc_typical_pair
    (d : ℕ) (hd : 2 ≤ d)
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (_MeyersMorrey : SubdiffusiveProcess.Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ccamp : SubdiffusiveProcess.Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (t p : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d) (hp : 1 ≤ p)
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ delta0 B : ℝ, 0 < delta0 ∧ 0 ≤ B ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace
          (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ) (m M : ℝ)
        (zcell : SpatialCoordinates d) (k : ℕ) (cellIdx paddedIdx : ℕ)
        (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity))) u‖)
        (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
        (hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M
          zcell k cellIdx paddedIdx hPk AE AF),
      ∃ K : BilateralField d → ℝ,
        AEStronglyMeasurable K (chaosSampleLaw model).toMeasure ∧
        (∀ᵐ eta ∂(chaosSampleLaw model).toMeasure, 0 ≤ K eta) ∧
        eLpNorm K (ENNReal.ofReal p) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal B ∧
        ∀ᵐ omega ∂P, ∃ Y : prop_conc_pair_data
            (centeredCube (z paddedIdx) (r paddedIdx) (hr paddedIdx))
            zcell ((3 : ℝ) ^ (-(k : ℝ))) (by positivity) C0 m M,
          (∀ u, Y.E.toClosedForm.energy u = limitFormEnergy (GE paddedIdx omega) u) ∧
          (∀ u, Y.F.toClosedForm.energy u = limitFormEnergy (GF paddedIdx omega) u) ∧
          (∀ pvec : Fin d → ℝ,
            Y.P.QE pvec = (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                (by positivity) : Set (SpatialCoordinates d))).toReal *
              (pvec ⬝ᵥ (AE omega).mulVec pvec) ∧
            Y.P.QF pvec = (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ)))
                (by positivity) : Set (SpatialCoordinates d))).toReal *
              (pvec ⬝ᵥ (AF omega).mulVec pvec)) ∧
          aux_prop_conc_pair_data_affine Y ∧
          aux_prop_conc_pair_data_growth Y (aux_prop_conc_pair_data_slopes d) t (K (field omega)) := by
  letI : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  letI : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨δ1, B1, hδ1, hB1, hG⟩ := prop_conc_growth_moments_of_form_comparison d hd I Pin _X
    _MeyersMorrey Ccamp _Sob Interp t p C0 ht htd hp hC0
  obtain ⟨δ2, hδ2, hAff⟩ := prop_conc_actual_affine_identification d hd I Pin _X _MeyersMorrey
    Ccamp _Sob Interp
  obtain ⟨δ3, hδ3, hGam⟩ := prop_conc_form_gamma d hd I Pin _X _MeyersMorrey Ccamp _Sob Interp
  refine ⟨min δ1 (min δ2 δ3), ((2 : ℝ) ^ d * ∑ q' ∈ aux_prop_conc_pair_data_slopes d,
    ∑ i : Fin d, (q' i) ^ 2) * B1, lt_min hδ1 (lt_min hδ2 hδ3), by positivity, ?_⟩
  intro mC bC model hδ Rm Sreg It H Ω mΩ P field z r hr Sspace GN GE GF NE NF m M zcell k
    cellIdx paddedIdx hPk AE AF hyps
  have hmC : mC = borel C(SpatialCoordinates d, ℝ) := bC.measurable_eq
  subst hmC
  have hr0 : 0 < (3 : ℝ) ^ (-(k : ℝ)) := Real.rpow_pos_of_pos zero_lt_three _
  obtain ⟨hJoint, ⟨hm, hmM, hM⟩, horderS, ⟨hzc, hrc⟩, ⟨hzp, hrp⟩, hsymE, hsymF, hAEs, hAFs⟩ := hyps
  obtain ⟨hPprob, hfmeas, hfmap, hIR, ⟨hNEmono, hNFmono⟩, hSkilled, hGNdef, hlimJ⟩ := hJoint
  have hkey : ∀ (zP : SpatialCoordinates d) (rP : ℝ) (hrP : 0 < rP)
      (S : ResponseSpace (centeredCube zP rP hrP))
      (GNp : ℕ → Ω → DomainL2 (centeredCube zP rP hrP) →L[ℝ] DomainL2 (centeredCube zP rP hrP))
      (GEp GFp : Ω → DomainL2 (centeredCube zP rP hrP) →L[ℝ] DomainL2 (centeredCube zP rP hrP)),
      zP = zcell → rP = 3 * ((3 : ℝ) ^ (-(k : ℝ))) →
      S.space = killedSobolevGraph (centeredCube zP rP hrP) →
      (∀ N ω f, GNp N ω f = (responseSolution S
        (Lane4.cutoffPositiveCoefficient model H (field ω) N zP hrP)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) →
      (∀ᵐ ω ∂P, Tendsto (fun n => GNp (NE n) ω) atTop (𝓝 (GEp ω)) ∧
        Tendsto (fun n => GNp (NF n) ω) atTop (𝓝 (GFp ω))) →
      (∀ᵐ ω ∂P, limitFormDomain (GEp ω) = limitFormDomain (GFp ω) ∧
        ∀ u : DomainL2 (centeredCube zP rP hrP), u ∈ limitFormDomain (GEp ω) →
          m * (limitFormEnergy (GEp ω) u).toReal ≤ (limitFormEnergy (GFp ω) u).toReal ∧
            (limitFormEnergy (GFp ω) u).toReal ≤ M * (limitFormEnergy (GEp ω) u).toReal) →
      ∃ K : BilateralField d → ℝ,
        AEStronglyMeasurable K (chaosSampleLaw model).toMeasure ∧
        (∀ᵐ eta ∂(chaosSampleLaw model).toMeasure, 0 ≤ K eta) ∧
        eLpNorm K (ENNReal.ofReal p) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal (((2 : ℝ) ^ d * ∑ q' ∈ aux_prop_conc_pair_data_slopes d,
            ∑ i : Fin d, (q' i) ^ 2) * B1) ∧
        ∀ᵐ omega ∂P, ∃ Y : prop_conc_pair_data (centeredCube zP rP hrP)
            zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 C0 m M,
          (∀ u, Y.E.toClosedForm.energy u = limitFormEnergy (GEp omega) u) ∧
          (∀ u, Y.F.toClosedForm.energy u = limitFormEnergy (GFp omega) u) ∧
          (∀ pvec : Fin d → ℝ,
            Y.P.QE pvec = (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 :
              Set (SpatialCoordinates d))).toReal * (pvec ⬝ᵥ (AE omega).mulVec pvec) ∧
            Y.P.QF pvec = (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 :
              Set (SpatialCoordinates d))).toReal * (pvec ⬝ᵥ (AF omega).mulVec pvec)) ∧
          aux_prop_conc_pair_data_affine Y ∧
          aux_prop_conc_pair_data_growth Y (aux_prop_conc_pair_data_slopes d) t
            (K (field omega)) := by
    intro zP rP hrP S GNp GEp GFp hzP hrP3 hS hGNp hlimS horderP
    have hzP' : zcell = zP := hzP.symm
    subst hzP'
    subst hrP3
    have h3r : 0 < 3 * ((3 : ℝ) ^ (-(k : ℝ))) := hrP
    obtain ⟨hPpad⟩ : Nonempty (∃ C : ℝ≥0, ∀ w : killedSobolevGraph
        (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hrP),
        ‖(w : SobolevData (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hrP)).1‖ ≤
          C * ‖subspaceGradient (killedSobolevGraph
            (centeredCube zcell (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hrP)) w‖) :=
      ⟨centeredCube_killedPoincare zcell hrP⟩
    have hSeq := aux_prop_conc_typical_pair_response_space_eq hPpad S hS
    subst hSeq
    have hNEt : Tendsto NE atTop atTop := hNEmono.tendsto_atTop
    have hNFt : Tendsto NF atTop atTop := hNFmono.tendsto_atTop
    have hrr1 : (3 : ℝ) ^ (-(k : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
    have hδ1' : model.delta ≤ δ1 := hδ.trans (min_le_left _ _)
    have hδ2' : model.delta ≤ δ2 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hδ3' : model.delta ≤ δ3 := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hAEd := aux_prop_conc_typical_pair_diag_ae_of_setup model H hIR.1 zcell k hr0 hPk NE P
      field hfmeas hfmap AE hAEs
    have hAFd := aux_prop_conc_typical_pair_diag_ae_of_setup model H hIR.1 zcell k hr0 hPk NF P
      field hfmeas hfmap AF hAFs
    obtain ⟨K, KE, KF, hKm, hK0, hKn, hTpos, hKa⟩ := hG model Rm Sreg It H hIR hδ1' zcell k
      ((3 : ℝ) ^ (-(k : ℝ))) hr0 h3r rfl (killedResponseSpace hPpad) rfl hPk NE NF hNEt hNFt
      (aux_prop_conc_typical_pair_diag model H zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 hPk NE)
      (aux_prop_conc_typical_pair_diag model H zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 hPk NF) hAEd
    have hcs : 0 ≤ (2 : ℝ) ^ d * ∑ q' ∈ aux_prop_conc_pair_data_slopes d,
        ∑ i : Fin d, (q' i) ^ 2 := by positivity
    refine ⟨fun om => ((2 : ℝ) ^ d * ∑ q' ∈ aux_prop_conc_pair_data_slopes d,
      ∑ i : Fin d, (q' i) ^ 2) * K om, hKm.const_mul _, ?_, ?_, ?_⟩
    · filter_upwards [hK0] with om h
      exact mul_nonneg hcs h
    · change eLpNorm (((2 : ℝ) ^ d * ∑ q' ∈ aux_prop_conc_pair_data_slopes d,
        ∑ i : Fin d, (q' i) ^ 2) • K) (ENNReal.ofReal p) (chaosSampleLaw model).toMeasure ≤ _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hcs, ENNReal.ofReal_mul hcs]
      exact mul_le_mul_right hKn _
    · have hTrans : ∀ {Φ : BilateralField d → Prop},
          (∀ᵐ om ∂(chaosSampleLaw model).toMeasure, Φ om) → ∀ᵐ ω ∂P, Φ (field ω) :=
        fun {Φ} h => ae_of_ae_map hfmeas.aemeasurable (by rw [hfmap]; exact h)
      have hKaω := hTrans hKa
      have hTposω := hTrans hTpos
      have hAEdω := hTrans hAEd
      have hAFdω := hTrans hAFd
      have hAffEω := hTrans (hAff model Rm Sreg It H hIR hδ2' zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0
        hrr1 h3r hPk NE)
      have hAffFω := hTrans (hAff model Rm Sreg It H hIR hδ2' zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0
        hrr1 h3r hPk NF)
      have hGamEω := hTrans (hGam model Rm Sreg It H hIR hδ3' zcell
        (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hrP hPpad NE)
      have hGamFω := hTrans (hGam model Rm Sreg It H hIR hδ3' zcell
        (3 * ((3 : ℝ) ^ (-(k : ℝ)))) hrP hPpad NF)
      filter_upwards [hKaω, hTposω, hAEdω, hAFdω, hAffEω, hAffFω, hGamEω, hGamFω, hAEs, hAFs,
        hlimS, horderP] with ω hKa' hTp hAEd' hAFd' hAffE' hAffF' hGamE' hGamF' hAEs' hAFs'
        hlim' hord'
      have hAEfull : ∀ p : Fin d → ℝ, Tendsto (fun n => affineDirichletResponse
          (centeredCube_isBounded zcell hr0) hPk
          (cutoffPositiveCoefficient model H (field ω) (NE n) zcell hr0) p /
            (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 :
              Set (SpatialCoordinates d))).toReal) atTop (𝓝 (p ⬝ᵥ (AE ω).mulVec p)) :=
        fun p => hAEs' p
      have hAFfull : ∀ p : Fin d → ℝ, Tendsto (fun n => affineDirichletResponse
          (centeredCube_isBounded zcell hr0) hPk
          (cutoffPositiveCoefficient model H (field ω) (NF n) zcell hr0) p /
            (volume (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 :
              Set (SpatialCoordinates d))).toReal) atTop (𝓝 (p ⬝ᵥ (AF ω).mulVec p)) :=
        fun p => hAFs' p
      have hdiagE : ∀ i : Fin d,
          aux_prop_conc_typical_pair_diag model H zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 hPk NE
            (field ω) i i = AE ω i i := by
        intro i
        have h2 := hAEfull (Pi.single i 1)
        rw [aux_prop_conc_typical_pair_unit_quadratic] at h2
        exact tendsto_nhds_unique (hAEd' i) h2
      have hdiagF : ∀ i : Fin d,
          aux_prop_conc_typical_pair_diag model H zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 hPk NF
            (field ω) i i = AF ω i i := by
        intro i
        have h2 := hAFfull (Pi.single i 1)
        rw [aux_prop_conc_typical_pair_unit_quadratic] at h2
        exact tendsto_nhds_unique (hAFd' i) h2
      exact aux_prop_conc_typical_pair_omega2 hd model H (field ω) zcell ((3 : ℝ) ^ (-(k : ℝ)))
        hr0 h3r t C0 m M hC0 hm hmM hM hPpad hPk NE NF (fun n => GNp (NE n) ω)
        (fun n => GNp (NF n) ω) (GEp ω) (GFp ω) (fun n f => hGNp (NE n) ω f)
        (fun n f => hGNp (NF n) ω f) hlim'.1 hlim'.2 hord'.1 hord'.2 (AE ω) (AF ω)
        (aux_prop_conc_typical_pair_diag model H zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 hPk NE
          (field ω))
        (aux_prop_conc_typical_pair_diag model H zcell ((3 : ℝ) ^ (-(k : ℝ))) hr0 hPk NF
          (field ω)) hdiagE hdiagF hAEfull hAFfull hAffE' hGamE' hAffF' hGamF' hTp (K (field ω))
        (KE (field ω)) (KF (field ω)) hKa'

  exact hkey (z paddedIdx) (r paddedIdx) (hr paddedIdx) (Sspace paddedIdx) (GN paddedIdx)
    (GE paddedIdx) (GF paddedIdx) hzp hrp (hSkilled paddedIdx) (hGNdef paddedIdx)
    (by filter_upwards [hlimJ] with ω h using h paddedIdx)
    (by filter_upwards [horderS] with ω h using h paddedIdx)

end
end Paper
