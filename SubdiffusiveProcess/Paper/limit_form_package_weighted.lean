module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.ReflectionResponses
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.limit_form_package_controls
public import SubdiffusiveProcess.Paper.cor_energy_measures
public import SubdiffusiveProcess.Paper.lem_weighted_cluster
public import SubdiffusiveProcess.Paper.prop_21_catalog_global_weighted_energy
public import SubdiffusiveProcess.Paper.prop_locality_recovery

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Compactness gives uniform positive bounds for a weight only assumed
continuous and positive on the closed cube. -/
theorem aux_limit_form_package_weight_bounds_on
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        lo ≤ rho x ∧ rho x ≤ hi := by
  have hcompact := isCompact_closure_centeredCube z hr
  have hne : (closure (centeredCube z r hr : Set (SpatialCoordinates d))).Nonempty :=
    ⟨z, subset_closure (Metric.mem_ball_self (half_pos hr))⟩
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hne hcont
  obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hne hcont
  exact ⟨rho xmin, rho xmax, hpos xmin hxmin, hpos xmax hxmax, fun x hx => ⟨hmin hx, hmax hx⟩⟩

/-- Global weighted comparison identifies the real form domains and transfers
the actual core to the weighted limit. -/
theorem aux_limit_form_package_controlled_weight_core
    {d : ℕ} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : aux_limit_form_package_mosco_data (centeredCube z r hr) S a G)
    (hB : aux_limit_form_package_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hbounds : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lo ≤ rho x ∧ rho x ≤ hi) :
    E.domain = EF.domain ∧
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EF (centeredCube z r hr : Set (SpatialCoordinates d)) C) := by
  have hcmp := aux_lem_weighted_cluster_limit_comparison S a b G F lo hi hlo hhi
    (fun n u => aux_lem_weighted_cluster_rho_form_bounds S (a n) (b n) (a n).val rho
      (EventuallyEq.refl _ _) (hweight n) lo hi hlo hbounds u)
    hA.lower hA.recovery hB.lower hB.recovery
  have hforms := aux_lem_weighted_cluster_forms_of_limit E EF G F hE hF lo hi hcmp.1 hcmp.2
  have hm : (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
      (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0 := by
    rw [Measure.restrict_apply' (centeredCube z r hr).isOpen.measurableSet]
    simp
  have hcores := aux_lem_weighted_cluster_core_transfer E EF
    (centeredCube z r hr : Set (SpatialCoordinates d)) (centeredCube z r hr).isOpen hm
    hforms.1 hi (fun u hu => (hforms.2 u hu).2) hcore
  exact ⟨Submodule.ext (fun u => (hforms.1 u).symm), hcores.1⟩

/-- The local coefficient bounds give bounds between the actual energy
measures of the two controlled limits. -/
theorem aux_limit_form_package_controlled_weight_local_bounds
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (B : aux_limit_form_package_analytic_controls d hd z r hr S b)
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : aux_limit_form_package_mosco_data (centeredCube z r hr) S a G)
    (hB : aux_limit_form_package_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hfcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EF.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = EF.domain)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EF.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (hqQ : q ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hb : ∀ x ∈ q, lo ≤ rho x ∧ rho x ≤ hi)
    (u : DomainL2 (centeredCube z r hr)) (hu : E.toClosedForm.MemCore u)
    (T : Set (SpatialCoordinates d)) (hTq : T ⊆ q) :
    lo * (Gamma.measure u T).toReal ≤ (GammaF.measure u T).toReal ∧
      (GammaF.measure u T).toReal ≤ hi * (Gamma.measure u T).toReal := by
  apply aux_limit_form_package_local_measure_bounds (centeredCube z r hr) E EF hcore hfcore
    hdom Gamma GammaF q hq hqQ lo hi hlo hhi _ _ u hu T hTq
  · intro v hv
    exact (aux_limit_form_package_controlled_local_form_le hS A hA hB E.toClosedForm EF.toClosedForm
      hE hF q hq hqQ hi
      (fun n => aux_limit_form_package_coefficient_weight_upper _ _ rho (hweight n) q hi
        (fun x hx => (hb x hx).2)) v hv).2
  · intro v hv
    exact (aux_limit_form_package_controlled_local_form_le hS B hB hA EF.toClosedForm E.toClosedForm
      hF hE q hq hqQ lo⁻¹
      (fun n => aux_limit_form_package_coefficient_weight_lower _ _ rho (hweight n) q lo hlo
        (fun x hx => (hb x hx).1)) v hv).2

/-- The weighted limit energy is identified for every element of the
unweighted domain by the proved catalogue energy-measure theorem. -/
theorem aux_limit_form_package_controlled_weight_energy
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (B : aux_limit_form_package_analytic_controls d hd z r hr S b)
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : aux_limit_form_package_mosco_data (centeredCube z r hr) S a G)
    (hB : aux_limit_form_package_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hfcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EF.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = EF.domain)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EF.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x) :
    ∀ u ∈ limitFormDomain G, limitFormEnergy F u = (∫ x, rho x ∂(Gamma.measure u) : ℝ) := by
  have hdomA := aux_limit_form_package_domain_eq_of_energy E.toClosedForm G hE
  have hdomB := aux_limit_form_package_domain_eq_of_energy EF.toClosedForm F hF
  obtain ⟨lo, hi, hlo, _hhi, hb⟩ := aux_limit_form_package_weight_bounds_on z r hr rho hcont hpos
  have hmeasure : ∀ (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq),
      (∀ i : Fin d, ∃ s : ℚ, zq i = (s : ℝ)) → (∃ k : ℤ, rq = (3 : ℝ) ^ k) →
      (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ u : DomainL2 (centeredCube z r hr), MemFormCore G u →
      ∀ T : Set (SpatialCoordinates d), MeasurableSet T →
        T ⊆ (centeredCube zq rq hrq : Set (SpatialCoordinates d)) →
        sInf (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
            (Gamma.measure u T).toReal ≤ (GammaF.measure u T).toReal ∧
          (GammaF.measure u T).toReal ≤
            sSup (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
              (Gamma.measure u T).toReal := by
    intro zq rq hrq _hRat _hTri hqQ u hu T _hT hTq
    let q : Set (SpatialCoordinates d) := centeredCube zq rq hrq
    have hne : (rho '' q).Nonempty := ⟨rho zq, ⟨zq, Metric.mem_ball_self (half_pos hrq), rfl⟩⟩
    have hbelow : BddBelow (rho '' q) :=
      ⟨lo, fun y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact (hb x (subset_closure (hqQ hx))).1⟩
    have habove : BddAbove (rho '' q) :=
      ⟨hi, fun y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact (hb x (subset_closure (hqQ hx))).2⟩
    have hmin : 0 < sInf (rho '' q) :=
      hlo.trans_le (le_csInf hne (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact (hb x (subset_closure (hqQ hx))).1))
    have hmax : 0 ≤ sSup (rho '' q) :=
      (hpos zq (subset_closure (hqQ (Metric.mem_ball_self (half_pos hrq))))).le.trans
        (le_csSup habove ⟨zq, Metric.mem_ball_self (half_pos hrq), rfl⟩)
    have hucore : E.toClosedForm.MemCore u := by
      obtain ⟨huG, uc, huc, hucs, _hucQ, huae⟩ := hu
      exact ⟨aux_limit_form_package_domain_mem_of_energy E.toClosedForm G hE huG,
        uc, huc, hucs, subset_univ _, huae⟩
    exact aux_limit_form_package_controlled_weight_local_bounds hS A B hA hB E EF hE hF
      hcore hfcore hdom Gamma GammaF rho hweight q (centeredCube zq rq hrq).isOpen hqQ
      _ _ hmin hmax (fun x hx => ⟨csInf_le hbelow ⟨x, hx, rfl⟩,
        le_csSup habove ⟨x, hx, rfl⟩⟩) u hucore T hTq
  have hid := prop_21_catalog_global_weighted_energy z r hr rfl E.toClosedForm
    EF.toClosedForm G F hE hF Gamma GammaF rho hcont hpos
    (by rw [← hdomA, ← hdomB, hdom])
    (fun u hu => hdom ▸ (aux_limit_form_package_domain_mem_of_energy E.toClosedForm G hE hu.1))
    hmeasure (aux_limit_form_package_core_dense_of_isCoreOn (centeredCube z r hr) E.toClosedForm G hE hcore)
  intro u hu
  have h := hid u hu
  obtain ⟨C, hC⟩ := hcore
  have hsupp := aux_limit_form_package_energy_measure_support Gamma
    (centeredCube z r hr).isOpen.measurableSet hC
    (aux_limit_form_package_domain_mem_of_energy E.toClosedForm G hE hu)
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp)] at h

/-- A continuous positive weight on the closed cube gives an actual bounded
positive coefficient when multiplied by any positive coefficient. -/
theorem aux_limit_form_package_positive_weight_coefficient
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x) :
    ∃ b : PositiveCoefficient (centeredCube z r hr),
      b.val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * a.val x := by
  obtain ⟨lo, hi, hlo, _hhi, hb⟩ := aux_limit_form_package_weight_bounds_on z r hr rho hcont hpos
  have hm : MemLp rho ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    apply memLp_top_of_bound
      ((hcont.mono subset_closure).aestronglyMeasurable (centeredCube z r hr).isOpen.measurableSet) hi
    filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (hpos x (subset_closure hx))]
    exact (hb x (subset_closure hx)).2
  have hmprod : MemLp (fun x => rho x * a.val x) ∞
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    by
      simpa only [Pi.mul_apply, mul_comm] using! (Lp.memLp a.val).fun_mul hm
  let bval := hmprod.toLp (fun x => rho x * a.val x)
  have hba : (bval : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * a.val x := hmprod.coeFn_toLp
  have hbpos : ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)), c ≤ bval x := by
    obtain ⟨c, hc, hca⟩ := a.property
    refine ⟨lo * c, mul_pos hlo hc, ?_⟩
    filter_upwards [hba, hca,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hbx hax hx
    rw [hbx]
    exact mul_le_mul (hb x (subset_closure hx)).1 hax hc.le
      (hpos x (subset_closure hx)).le
  exact ⟨⟨bval, hbpos⟩, hba⟩

/-- Pointwise weighting identifies the finite-cutoff integral exactly. -/
theorem aux_limit_form_package_weighted_response_integral
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (a b : PositiveCoefficient Q) (rho : SpatialCoordinates d → ℝ)
    (hweight : b.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => rho x * a.val x) (w : S.space) :
    responseForm S b w w =
      ∫ x in (Q : Set (SpatialCoordinates d)), rho x *
        (a.val x * ∑ i : Fin d, ((w : SobolevData Q).2 i x) ^ 2) := by
  rw [← aux_cor_energy_measures_energy_integral S (fun _ => b) 0 w]
  apply integral_congr_ae
  filter_upwards [hweight] with x hx
  rw [hx, mul_assoc]

/-- A lower bound available on a further subsequence of every subsequence
is a lower bound for the full liminf. -/
theorem aux_limit_form_package_le_liminf_of_subsubsequence (f : ℕ → EReal) (L : EReal)
    (hsub : ∀ tau : ℕ → ℕ, StrictMono tau → ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      L ≤ liminf (fun n => f (tau (sigma n))) atTop) :
    L ≤ liminf f atTop := by
  apply (le_liminf_iff).mpr
  intro y hy
  by_contra hn
  have hf : ∃ᶠ n in atTop, f n ≤ y := by simpa only [Filter.Frequently, not_le] using hn
  obtain ⟨tau, htau, hftau⟩ := extraction_of_frequently_atTop hf
  obtain ⟨sigma, _hsigma, hL⟩ := hsub tau htau
  have hupper : liminf (fun n => f (tau (sigma n))) atTop ≤ y :=
    liminf_le_of_frequently_le (Frequently.of_forall fun n => hftau (sigma n))
  exact (not_le_of_gt hy) (hL.trans hupper)

section Standing

variable {d : ℕ} {hd : 2 ≤ d}
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

include BD BDQ EM hcontract

omit hcontract in
theorem aux_limit_form_package_controlled_weighted_identify (_hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (B : aux_limit_form_package_analytic_controls d hd z r hr S b)
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : aux_limit_form_package_mosco_data (centeredCube z r hr) S a G)
    (hB : aux_limit_form_package_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x) :
    ∀ u ∈ limitFormDomain G, limitFormEnergy F u = (∫ x, rho x ∂(Gamma.measure u) : ℝ) := by
  obtain ⟨lo, hi, hlo, hhi, hb⟩ := aux_limit_form_package_weight_bounds_on z r hr rho hcont hpos
  obtain ⟨hdom, hfcore⟩ := aux_limit_form_package_controlled_weight_core hA hB E.toClosedForm EF.toClosedForm
    hE hF hcore rho hweight lo hi hlo hhi.le (fun x hx => hb x (subset_closure hx))
  have hlocal := aux_limit_form_package_controlled_core_locality hS B hB EF.toClosedForm hF
  have hstrong := (BD z r hr EF).isStronglyLocal_of_onCore
    (aux_limit_form_package_isRegular_of_core (centeredCube z r hr) EF.toClosedForm hfcore)
    (BDQ z r hr EF hfcore hlocal)
  obtain ⟨GammaF, _hsupp⟩ := aux_limit_form_package_energy_measure_of_locality z r hr EF
    (EM z r hr EF) hfcore hstrong
  exact aux_limit_form_package_controlled_weight_energy hS A B hA hB E EF hE hF
    hcore hfcore hdom Gamma GammaF rho hcont hpos hweight

/-- Weighted compactness and the actual local energy identification prove the
weighted weak lower bound on the full sequence. The three stated standing
inputs produce each cluster's energy measure. -/
theorem aux_limit_form_package_controlled_weighted_cluster_lower
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (B : aux_limit_form_package_analytic_controls d hd z r hr S b)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)) (hw : w ∈ limitFormDomain G)
    (hWeak : ∀ f, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      (∫ x, rho x ∂(Gamma.measure w) : ℝ) ≤
        liminf (fun n => (responseForm S (b (sigma n))
          (wN (sigma n)) (wN (sigma n)) : EReal)) atTop := by
  obtain ⟨F⟩ := aux_limit_form_package_form_cluster_exists hS B
    (fun n => hcontract z r hr S hS (b n))
  let A' : aux_limit_form_package_analytic_controls d hd z r hr S (fun n => a (F.sigma n)) :=
    aux_limit_form_package_controls_reindex A F.sigma
  let B' : aux_limit_form_package_analytic_controls d hd z r hr S (fun n => b (F.sigma n)) :=
    aux_limit_form_package_controls_reindex B F.sigma
  have hA' := limit_form_package_controls hS A' (fun n => GN (F.sigma n)) G
    (fun n => hGN (F.sigma n)) (hConv.comp F.sigma_strict.tendsto_atTop)
  have hB' : aux_limit_form_package_mosco_data (centeredCube z r hr) S
      (fun n => b (F.sigma n)) F.operator := ⟨F.symmetric, F.lower, F.recovery⟩
  have hid := aux_limit_form_package_controlled_weighted_identify BD BDQ EM hcontract hS A' B'
    hA' hB' E F.form hE F.energy_eq hcore Gamma rho hcont hpos
    (fun n => hweight (F.sigma n)) w hw
  refine ⟨F.sigma, F.sigma_strict, ?_⟩
  rw [← hid]
  exact F.lower (fun n => wN (F.sigma n)) w
    (fun f => (hWeak f).comp F.sigma_strict.tendsto_atTop)

theorem aux_limit_form_package_controlled_weighted_lower
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)) (hw : w ∈ limitFormDomain G)
    (hWeak : ∀ f, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) :
    (∫ x, rho x ∂(Gamma.measure w) : ℝ) ≤
      liminf (fun n => (responseForm S (b n) (wN n) (wN n) : EReal)) atTop := by
  obtain ⟨lo, hi, hlo, hhi, hb⟩ := aux_limit_form_package_weight_bounds_on z r hr rho hcont hpos
  have hLower : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo * (a n).val x ≤ (b n).val x := by
    intro n
    filter_upwards [hweight n, aux_prop_locality_recovery_coeff_nonneg (a n),
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hax hxQ
    rw [hx]
    exact mul_le_mul_of_nonneg_right (hb x (subset_closure hxQ)).1 hax
  have hUpper : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (b n).val x ≤ hi * (a n).val x := by
    intro n
    have h := aux_limit_form_package_coefficient_weight_upper (a n) (b n) rho (hweight n)
      (centeredCube z r hr : Set (SpatialCoordinates d)) hi
      (fun x hx => (hb x (subset_closure hx)).2)
    filter_upwards [h, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxQ
    exact hx hxQ
  obtain ⟨B⟩ : Nonempty (aux_limit_form_package_analytic_controls d hd z r hr S b) :=
    ⟨aux_limit_form_package_analytic_controls_reindex_weight A b id lo hi hlo hhi.le hLower hUpper⟩
  apply aux_limit_form_package_le_liminf_of_subsubsequence
  intro tau htau
  exact aux_limit_form_package_controlled_weighted_cluster_lower BD BDQ EM hcontract hS
    (aux_limit_form_package_controls_reindex A tau) (aux_limit_form_package_controls_reindex B tau)
    (fun n => GN (tau n)) G (fun n => hGN (tau n)) (hConv.comp htau.tendsto_atTop)
    E hE hcore Gamma rho hcont hpos (fun n => hweight (tau n))
    (fun n => wN (tau n)) w hw (fun f => (hWeak f).comp htau.tendsto_atTop)

/-- The precise weighted lower-cluster input used by cor_energy_measures is
now derived for a controlled operator limit, including arbitrary subsequences. -/
theorem limit_form_package_weighted
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm) :
    ∀ rho : SpatialCoordinates d → ℝ,
      ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
      (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x) →
      ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)), w ∈ limitFormDomain G →
      (∀ f, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      (((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), rho x ∂(Gamma.measure w)) : ℝ) : EReal) ≤
        liminf (fun n =>
          (((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), rho x *
            ((a (sigma n)).val x * ∑ i : Fin d,
              ((wN (sigma n) : SobolevData (centeredCube z r hr)).2 i x) ^ 2)) : ℝ) : EReal)) atTop := by
  intro rho hcont hpos sigma hsigma wN w hw hweak
  choose b hb using fun n => aux_limit_form_package_positive_weight_coefficient z r hr (a n) rho hcont hpos
  have h := aux_limit_form_package_controlled_weighted_lower BD BDQ EM hcontract hS
    (aux_limit_form_package_controls_reindex A sigma) (fun n => GN (sigma n)) G
    (fun n => hGN (sigma n)) (hConv.comp hsigma.tendsto_atTop) E hE hcore Gamma
    rho hcont hpos (fun n => hb (sigma n)) (fun n => wN (sigma n)) w hw
    (fun f => (hweak f).comp hsigma.tendsto_atTop)
  have hfun : (fun n => (responseForm S (b (sigma n)) (wN (sigma n)) (wN (sigma n)) : EReal)) =
      (fun n => (((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), rho x *
        ((a (sigma n)).val x * ∑ i : Fin d,
          ((wN (sigma n) : SobolevData (centeredCube z r hr)).2 i x) ^ 2)) : ℝ) : EReal)) := by
    funext n
    rw [aux_limit_form_package_weighted_response_integral S (a (sigma n)) (b (sigma n)) rho (hb (sigma n))]
  rw [hfun] at h
  obtain ⟨C, hC⟩ := hcore
  have hsupp := aux_limit_form_package_energy_measure_support Gamma
    (centeredCube z r hr).isOpen.measurableSet hC
    (aux_limit_form_package_domain_mem_of_energy E.toClosedForm G hE hw)
  simpa only [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp)] using h

end Standing

end SubdiffusiveProcess.Paper
