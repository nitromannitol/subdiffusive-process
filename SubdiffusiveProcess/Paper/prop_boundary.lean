module

public import SubdiffusiveProcess.Paper.catalog_cutoff_existence
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.MeshError
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Paper.cor_energy_measures
public import SubdiffusiveProcess.Paper.lem_19
public import SubdiffusiveProcess.Paper.lem_truncation
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.prop_locality
public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Paper.cell_boundary_continuity
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.prop_boundary_solution_limit
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Paper.obl_FOT
public import SubdiffusiveProcess.Paper.conv_energy_measure_normalization

public import SubdiffusiveProcess.Paper.chaos_limit_null_frontier
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section PropBoundaryAux

open scoped Distributions

/-! ## Helpers for `prop_boundary`. -/

/-- A form orthogonal to the core of a killed domain is orthogonal to the whole domain. -/
theorem aux_prop_boundary_form_zero_of_core {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] {m : Measure X} {E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m} {U : Set X}
    {D : Submodule ℝ (Lp ℝ 2 m)} (hD : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E U D)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain)
    (hcore : ∀ w : Lp ℝ 2 m, E.MemCoreOn U w → E.form u w = 0) :
    ∀ φ ∈ D, E.form u φ = 0 := by
  intro φ hφ
  obtain ⟨w, hw, hconv⟩ := hD.exists_seq hφ
  have hφd : φ ∈ E.domain := hD.le_domain hφ
  have h2 : Tendsto (fun n => E.energyNormSq (w n - φ)) atTop (𝓝 0) :=
    Tendsto.congr (fun n => E.energyNormSq_sub_comm hφd (hw n).mem_domain) hconv
  have h : Tendsto (fun n => E.form (w n) u) atTop (𝓝 (E.form φ u)) :=
    _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.tendsto_form_of_tendsto_energyNormSq (E := E)
      (u := w) (w := φ) (v := u) (fun n => (hw n).mem_domain) hφd hu h2
  have hzero : E.form φ u = 0 := by
    have hconst : Tendsto (fun n => E.form (w n) u) atTop (𝓝 0) :=
      Tendsto.congr' (Eventually.of_forall (fun n => by
        change (0 : ℝ) = E.form (w n) u
        rw [E.form_symm (w n) (hw n).mem_domain u hu, hcore (w n) (hw n)]))
        tendsto_const_nhds
    exact tendsto_nhds_unique h hconst
  rw [E.form_symm u hu φ hφd, hzero]

/-- The signed integral of the constant `1` over `univ` is the total signed mass. -/
theorem aux_prop_boundary_signedIntegralOn_one {X : Type*} [MeasurableSpace X]
    (ν : SignedMeasure X) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν Set.univ (fun _ => (1 : ℝ)) = ν Set.univ := by
  have hnu := congrArg (fun s : SignedMeasure X => s Set.univ)
    (SignedMeasure.toSignedMeasure_toJordanDecomposition ν)
  have hnu2 : ν.toJordanDecomposition.toSignedMeasure Set.univ = ν Set.univ := hnu
  simp only [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn, integral_const, measureReal_def]
  simp only [Measure.restrict_apply_univ]
  rw [← hnu2]
  rw [JordanDecomposition.toSignedMeasure, sub_apply,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ]
  simp [measureReal_def]

/-- Functions continuous on a closed cube and a.e. equal on the open cube agree on the closed cube. -/
theorem aux_prop_boundary_eqOn_closure_of_ae {d : ℕ} (z : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R) (f g : SpatialCoordinates d → ℝ)
    (hf : ContinuousOn f (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hg : ContinuousOn g (closure (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hfg : f =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] g) :
    Set.EqOn f g (closure (centeredCube z R hR : Set (SpatialCoordinates d))) := by
  have hO : IsOpen ((centeredCube z R hR : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) :=
    (centeredCube z R hR).isOpen
  have h1 : Set.EqOn f g ((centeredCube z R hR : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) :=
    Measure.eqOn_open_of_ae_eq hfg hO (hf.mono subset_closure) (hg.mono subset_closure)
  exact Set.EqOn.of_subset_closure h1 hf hg subset_closure le_rfl

/-- Boundary values pass to a uniform limit. -/
theorem aux_prop_boundary_limit_boundary_value {d : ℕ}
    (F : ℕ → SpatialCoordinates d → ℝ) (Uc beta b : SpatialCoordinates d → ℝ)
    (S T : Set (SpatialCoordinates d)) (hST : S ⊆ T)
    (hunif : TendstoUniformlyOn F Uc atTop T)
    (hFb : ∀ n, ∀ x ∈ S, F n x = beta x) (hbeta : ∀ x ∈ S, beta x = b x) :
    ∀ x ∈ S, Uc x = b x := by
  intro x hx
  have h := hunif.tendsto_at (hST hx)
  have hc : Tendsto (fun n => F n x) atTop (𝓝 (beta x)) :=
    tendsto_const_nhds.congr (fun n => (hFb n x hx).symm)
  rw [tendsto_nhds_unique h hc, hbeta x hx]

/-- The represented `L²` limit lies in the domain of the Mosco limit (lower bound). -/
theorem aux_prop_boundary_limit_mem_domain {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (S : ResponseSpace Ω) (aC : ℕ → PositiveCoefficient Ω)
    (hLower : ∀ (vn : ℕ → S.space) (v : DomainL2 Ω),
      (∀ f : DomainL2 Ω,
        Tendsto (fun n => inner ℝ f (vn n).val.1) atTop (𝓝 (inner ℝ f v))) →
      E.energy v ≤
        Filter.liminf (fun n => (responseForm S (aC n) (vn n) (vn n) : EReal)) atTop)
    (UNS : ℕ → S.space) (uBar : DomainL2 Ω)
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (E0 : ℝ) (hE0 : ∀ n, responseForm S (aC n) (UNS n) (UNS n) ≤ E0) :
    uBar ∈ E.domain := by
  apply aux_cor_energy_measures_domain_of_energy_ne_top E uBar
  have hw : ∀ f : ↥(DomainL2 Ω),
      Tendsto (fun n => inner ℝ f (UNS n).val.1) atTop (𝓝 (inner ℝ f uBar)) :=
    aux_cor_energy_measures_weak_of_space S UNS uBar hUNL2
  have h1 : E.energy uBar ≤
      Filter.liminf (fun n => ((responseForm S (aC n) (UNS n) (UNS n) : ℝ) : EReal)) atTop :=
    hLower UNS uBar hw
  have h2 : Filter.liminf (fun n => ((responseForm S (aC n) (UNS n) (UNS n) : ℝ) : EReal)) atTop
      ≤ (E0 : EReal) :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun n => EReal.coe_le_coe_iff.2 (hE0 n))
  exact ne_top_of_le_ne_top (EReal.coe_ne_top E0) (h1.trans h2)

/-- H-a.  The zero extension of a function vanishing on `frontier s` is continuous and
supported in `closure s` (`w = (V-U) 1_{\bar q}`). -/
theorem aux_prop_boundary_indicator_continuous {d : ℕ}
    (s T : Set (SpatialCoordinates d)) (hsT : closure s ⊆ T)
    (wc : SpatialCoordinates d → ℝ) (hwc : ContinuousOn wc T)
    (h0 : ∀ x ∈ frontier s, wc x = 0) :
    Continuous ((closure s).indicator wc) ∧
      tsupport ((closure s).indicator wc) ⊆ closure s := by
  have h_cont : Continuous ((closure s).indicator wc) := by
    classical
    rw [← Set.piecewise_eq_indicator]
    apply continuous_piecewise
    · intro x hx
      exact h0 x (frontier_closure_subset hx)
    · rw [closure_closure]; exact hwc.mono hsT
    · exact continuousOn_const
  have h_tsupport : tsupport ((closure s).indicator wc) ⊆ closure s :=
    closure_minimal support_indicator_subset isClosed_closure
  exact And.intro h_cont h_tsupport

/-- H-b.  An `L²(Ω)` class for the zero extension `s.indicator wc` of a representative
`wc` of an `L²(Ω)` element. -/
theorem aux_prop_boundary_indicator_toLp {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (s : Set (SpatialCoordinates d)) (hs : MeasurableSet s)
    (w : DomainL2 Ω) (wc : SpatialCoordinates d → ℝ)
    (hw : (w : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] wc) :
    ∃ wq : DomainL2 Ω, (wq : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] s.indicator wc := by
  have hm := (Lp.memLp w).ae_eq hw
  refine ⟨(hm.indicator hs).toLp _, MemLp.coeFn_toLp _⟩

/-- H-c.  On `q`, `V = U + (V - U) 1_{\bar q}` almost everywhere. -/
theorem aux_prop_boundary_ae_eq_add_on {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (q : Set (SpatialCoordinates d)) (hq : MeasurableSet q)
    (U V wq : DomainL2 Ω) (Uc Vc : SpatialCoordinates d → ℝ)
    (hU : (U : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] Uc)
    (hV : (V : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] Vc)
    (hwq : (wq : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        (closure q).indicator (fun x => Vc x - Uc x)) :
    (V : SpatialCoordinates d → ℝ)
      =ᵐ[(volume.restrict (Ω : Set (SpatialCoordinates d))).restrict q]
        ((U + wq : DomainL2 Ω) : SpatialCoordinates d → ℝ) := by
  filter_upwards [ae_restrict_mem hq, ae_restrict_of_ae hU, ae_restrict_of_ae hV,
    ae_restrict_of_ae hwq, ae_restrict_of_ae (Lp.coeFn_add U wq)] with x hx hUc hVc hwqx hsum
  have hx' : x ∈ closure q := subset_closure hx
  have h_ind : ((closure q).indicator (fun x => Vc x - Uc x)) x = Vc x - Uc x :=
    Set.indicator_of_mem hx' (fun x => Vc x - Uc x)
  rw [h_ind] at hwqx
  rw [hVc, hsum, Pi.add_apply, hUc, hwqx]
  ring

/-- H-d.  The cross measure `Γ(u, w)` of `q` vanishes when `w` is carried by `closure q`,
`Γ(u)` gives no mass to `frontier q`, and `E(u, w) = 0`. -/
theorem aux_prop_boundary_cross_zero_open {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] {m : Measure X}
    {E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m} (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (u w : Lp ℝ 2 m) (hu : u ∈ E.domain) (hw : w ∈ E.domain)
    (q : Set X) (hq : IsOpen q)
    (f : X → ℝ) (hf : Continuous f) (hfsupp : tsupport f ⊆ closure q)
    (hwf : (w : X → ℝ) =ᵐ[m] f)
    (hface : Γ.measure u (frontier q) = 0)
    (horth : E.form u w = 0) :
    Γ.cross u w q = 0 := by
  have h_frontier_meas : MeasurableSet (frontier q) := isClosed_frontier.measurableSet
  have h_closure_compl_meas : MeasurableSet ((closure q)ᶜ) :=
    isClosed_closure.isOpen_compl.measurableSet
  have h_disj1 : Disjoint (frontier q) ((closure q)ᶜ) :=
    (disjoint_compl_right (a := closure q)).mono_left frontier_subset_closure
  have h_disj2 : Disjoint q (frontier q ∪ (closure q)ᶜ) :=
    Disjoint.union_right (Set.disjoint_iff_inter_eq_empty.mpr hq.inter_frontier_eq)
      ((disjoint_compl_right (a := closure q)).mono_left subset_closure)
  have huniv_eq : (Set.univ : Set X) = q ∪ (frontier q ∪ (closure q)ᶜ) := by
    rw [← Set.union_assoc, ← closure_eq_self_union_frontier, Set.union_compl_self]
  have hΓw : Γ.measure w (closure q)ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr hfsupp)
      (Γ.measure_compl_tsupport w hw f hf hwf)
  have hcomp : Γ.cross u w (closure q)ᶜ = 0 := by
    have h := Γ.abs_cross_le u hu w hw _ h_closure_compl_meas
    rw [hΓw, ENNReal.toReal_zero, Real.sqrt_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  have hfr : Γ.cross u w (frontier q) = 0 := by
    have h := Γ.abs_cross_le u hu w hw _ h_frontier_meas
    rw [hface, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at h
    exact abs_nonpos_iff.mp h
  have huniv : Γ.cross u w Set.univ = 0 := by rw [Γ.cross_univ u hu w hw, horth]
  have hsplit : Γ.cross u w Set.univ =
      Γ.cross u w q + (Γ.cross u w (frontier q) + Γ.cross u w (closure q)ᶜ) := by
    rw [huniv_eq, VectorMeasure.of_union h_disj2 hq.measurableSet
      (h_frontier_meas.union h_closure_compl_meas),
      VectorMeasure.of_union h_disj1 h_frontier_meas h_closure_compl_meas]
  rw [huniv, hfr, hcomp] at hsplit
  linarith

/-- Conjunct 9 of `prop_boundary` (minimality), given the zero face
mass (conjunct 6), the harmonicity (conjunct 7) and the `hZeroTrace` input at `q`. -/
theorem aux_prop_boundary_minimal
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (Dq : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)))
    (hkilled : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EQ.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) Dq)
    (b : SpatialCoordinates d → ℝ)
    (hZT : ∀ w ∈ EQ.toClosedForm.domain, ∀ wc : SpatialCoordinates d → ℝ,
        ContinuousOn wc
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        (w : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] wc →
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), wc x = 0) →
        ∀ wq : DomainL2 (centeredCube z (3 * r) h3r),
          (wq : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
              (closure (centeredCube z r hr : Set (SpatialCoordinates d))).indicator wc →
          wq ∈ Dq ∧
            EQ.form wq wq =
              (Gamma.measure w (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
    (U : DomainL2 (centeredCube z (3 * r) h3r)) (Uc : SpatialCoordinates d → ℝ)
    (hU : U ∈ EQ.toClosedForm.domain)
    (hUc : ContinuousOn Uc
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hUae : (U : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc)
    (hUb : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Uc x = b x)
    (hface : Gamma.measure U (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0)
    (hharm : ∀ φ : DomainL2 (centeredCube z (3 * r) h3r), φ ∈ Dq → EQ.form U φ = 0) :
    ∀ V : DomainL2 (centeredCube z (3 * r) h3r),
        V ∈ EQ.toClosedForm.domain →
        ∀ Vc : SpatialCoordinates d → ℝ,
        ContinuousOn Vc
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        (V : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Vc →
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Vc x = b x) →
        (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          (Gamma.measure V (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  intro V hV Vc hVc hVae hVb
  have hqopen : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen
  have hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) := by
    show Metric.ball z (r / 2) ⊆ Metric.ball z (3 * r / 2)
    exact Metric.ball_subset_ball (by linarith)
  have hwdom : V - U ∈ EQ.toClosedForm.domain := EQ.toClosedForm.domain.sub_mem hV hU
  have hwc : ContinuousOn (fun x => Vc x - Uc x)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) := hVc.sub hUc
  have hwae : ((V - U : DomainL2 (centeredCube z (3 * r) h3r)) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
        (fun x => Vc x - Uc x) := by
    filter_upwards [Lp.coeFn_sub V U, hVae, hUae] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have h0 : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (fun x => Vc x - Uc x) x = 0 := fun x hx => by
    simp only [hVb x hx, hUb x hx, sub_self]
  obtain ⟨wq, hwq⟩ := aux_prop_boundary_indicator_toLp
    (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
    isClosed_closure.measurableSet (V - U) (fun x => Vc x - Uc x) hwae
  obtain ⟨hwqD, -⟩ := hZT (V - U) hwdom (fun x => Vc x - Uc x) hwc hwae h0 wq hwq
  have hwqdom : wq ∈ EQ.toClosedForm.domain := hkilled.le_domain hwqD
  obtain ⟨hfcont, hfsupp⟩ := aux_prop_boundary_indicator_continuous
    (centeredCube z r hr : Set (SpatialCoordinates d))
    (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (closure_mono hqQ) (fun x => Vc x - Uc x) hwc h0
  have hcross : Gamma.cross U wq (centeredCube z r hr : Set (SpatialCoordinates d)) = 0 :=
    aux_prop_boundary_cross_zero_open Gamma U wq hU hwqdom _ hqopen _ hfcont hfsupp hwq
      hface (hharm wq hwqD)
  have hae := aux_prop_boundary_ae_eq_add_on
    (centeredCube z r hr : Set (SpatialCoordinates d)) hqopen.measurableSet U V wq Uc Vc
    hUae hVae hwq
  have hUw : U + wq ∈ EQ.toClosedForm.domain := EQ.toClosedForm.domain.add_mem hU hwqdom
  have hloc : Gamma.measure V (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Gamma.measure (U + wq) (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    Gamma.locality_apply hV hUw hqopen hae
  have hexp := Gamma.cross_add_self_apply hU hwqdom
    (centeredCube z r hr : Set (SpatialCoordinates d))
  rw [Gamma.cross_self (U + wq) hUw _ hqopen.measurableSet,
    Gamma.cross_self U hU _ hqopen.measurableSet,
    Gamma.cross_self wq hwqdom _ hqopen.measurableSet, hcross] at hexp
  rw [hloc, hexp]
  have hnn : 0 ≤ (Gamma.measure wq (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
    ENNReal.toReal_nonneg
  linarith

/-- FL-a.  The centre cell of the `3 ×... × 3` subdivision of `Q = centeredCube z (3r)`
is `q = centeredCube z r` (proved; same proof as the critic probe). -/
theorem aux_prop_boundary_center_cell {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (h3r : 0 < 3 * r) :
    (oddGridCell z (3 * r) h3r (triadicHalf 1)
        (fun _ => ⟨triadicHalf 1, by simp [triadicHalf]⟩) : Set (SpatialCoordinates d)) =
      centeredCube z r hr := by
  have h1 : triadicHalf 1 = 1 := by decide
  show Metric.ball _ _ = Metric.ball z (r / 2)
  congr 1
  · funext i
    simp [oddGridCenter, h1]
  · simp [h1]; ring

/-- B1 (the energy of `U_N` is a finite sum of per-cell
energies bounded along the represented sequence).  Route: `responseForm_apply`,
`hUNrep` + `sobolevDataOfH1_snd_coeFn` (gradients), `haC` (coefficient), then
`lane2_energy_sum_cells` over the `3^d` cells (faces are Lebesgue-null) and
`hCellEnergy`; `E0 = ∑ k, Bcell k` works. -/
theorem aux_prop_boundary_energy_bound {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hacont : ∀ n : ℕ, ContinuousOn (a n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (Bcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hCellEnergy : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      energy (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)) ≤ Bcell k) :
    ∃ E0 : ℝ, ∀ n : ℕ, responseForm S (aC n) (UNS n) (UNS n) ≤ E0 := by
  classical
  refine ⟨∑ k : OddGridIndex d (triadicHalf 1), Bcell k, fun n => ?_⟩
  have hcompact : IsCompact (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) :=
    lane2_isCompact_closure_centeredCube z h3r
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn (hacont n)
  have hameas : AEStronglyMeasurable (a n)
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) :=
    ((hacont n).mono subset_closure).aestronglyMeasurable
      (centeredCube z (3 * r) h3r).isOpen.measurableSet
  have habd : ∀ᵐ x ∂(volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))),
      ‖a n x‖ ≤ C :=
    ae_restrict_of_forall_mem (centeredCube z (3 * r) h3r).isOpen.measurableSet
      (fun x hx => hC x (subset_closure hx))
  have hameasC : AEStronglyMeasurable ((aC n).val : SpatialCoordinates d → ℝ)
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) :=
    hameas.congr (haC n).symm
  have habdC : ∀ᵐ x ∂(volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))),
      ‖(aC n).val x‖ ≤ C := by
    filter_upwards [haC n, habd] with x hx hb
    rw [hx]; exact hb
  have hcov : (⋃ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)))
        =ᵐ[volume] (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    oddGrid_union_ae_eq z h3r (triadicHalf 1)
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun k : OddGridIndex d (triadicHalf 1) =>
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)))) :=
    oddGridCell_pairwiseDisjoint z h3r (triadicHalf 1)
  have hsum_eq : energy (a n) (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) (UN n)
      = ∑ k : OddGridIndex d (triadicHalf 1),
          energy (a n)
            (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
            ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
              (hcellsub k)) :=
    lane2_energy_sum_cells (oddGridCell z (3 * r) h3r (triadicHalf 1))
      hcellsub hdisj hcov hameas habd (UN n)
      (fun k => (UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))
      (fun _ _ => Filter.EventuallyEq.rfl)
  have hCle : energy (a n) (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) (UN n)
      ≤ ∑ k : OddGridIndex d (triadicHalf 1), Bcell k := by
    rw [hsum_eq]; exact Finset.sum_le_sum (fun k _ => hCellEnergy n k)
  have hint : ∀ i : Fin d, IntegrableOn
      (fun x => (aC n).val x * ((UN n).grad x i * (UN n).grad x i))
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) volume := fun i =>
    lane2_integrableOn_coeff_mul hameasC habdC ((UN n).gradMemL2 i) ((UN n).gradMemL2 i)
  have hresp : responseForm S (aC n) (UNS n) (UNS n)
      = energy (a n) (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) (UN n) := by
    have e1 : responseForm S (aC n) (UNS n) (UNS n)
        = sobolevCoefficientForm (aC n) (sobolevDataOfH1 (UN n)) (sobolevDataOfH1 (UN n)) := by
      rw [responseForm_apply, hUNrep n]
      exact (sobolevCoefficientForm_apply (aC n) (sobolevDataOfH1 (UN n))
        (sobolevDataOfH1 (UN n))).symm
    have e2 := sobolevCoefficientForm_eq_integral_vecDot (aC n) (UN n) (UN n) hint
    have e3 : (∫ x in (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          vecDot ((aC n).val x • (UN n).grad x) ((UN n).grad x))
        = ∫ x in (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          (aC n).val x * vecDot ((UN n).grad x) ((UN n).grad x) := by
      congr 1
      funext x
      simp [vecDot, Finset.mul_sum, mul_assoc]
    have e4 : (∫ x in (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          (aC n).val x * vecDot ((UN n).grad x) ((UN n).grad x))
        = ∫ x in (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          a n x * vecDot ((UN n).grad x) ((UN n).grad x) := by
      apply setIntegral_congr_ae (centeredCube z (3 * r) h3r).isOpen.measurableSet
      filter_upwards [(MeasureTheory.ae_restrict_iff'
          (centeredCube z (3 * r) h3r).isOpen.measurableSet).mp (haC n)] with x hx hxQ
      rw [hx hxQ]
    rw [e1, e2, e3, e4]
    rfl
  rw [hresp]
  exact hCle

/-! ### Generic weak-cluster extraction and portmanteau ("any weak
cluster `ν` of `Γ_N(U_N)`"). -/

/-- D1.  A bounded sequence of measures carried by a compact set has a subsequence
converging against every function continuous on that set; the limit is a finite measure
carried by the set (Arzelà–Ascoli on `C(K, ℝ)` and Riesz–Markov–Kakutani on `K`). -/
theorem aux_prop_boundary_weak_cluster {d : ℕ} (K : Set (SpatialCoordinates d))
    (hK : IsCompact K) (μ : ℕ → Measure (SpatialCoordinates d)) (M : ℝ)
    (hμK : ∀ n, μ n Kᶜ = 0) (hμM : ∀ n, μ n Set.univ ≤ ENNReal.ofReal M) :
    ∃ (ν : Measure (SpatialCoordinates d)) (σ : ℕ → ℕ), StrictMono σ ∧
      ν Set.univ < ⊤ ∧ ν Kᶜ = 0 ∧
      ∀ φ : SpatialCoordinates d → ℝ, ContinuousOn φ K →
        Tendsto (fun n => ∫ x, φ x ∂(μ (σ n))) atTop (𝓝 (∫ x, φ x ∂ν)) := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hemb : MeasurableEmbedding (Subtype.val : K → SpatialCoordinates d) :=
    MeasurableEmbedding.subtype_coe hKm
  let μK : ℕ → Measure K := fun n => (μ n).comap Subtype.val
  have hμKuniv : ∀ n, μK n Set.univ ≤ ENNReal.ofReal (max M 0) := by
    intro n
    change (μ n).comap Subtype.val Set.univ ≤ _
    rw [hemb.comap_apply]
    exact (measure_mono (subset_univ _)).trans
      ((hμM n).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hfin : ∀ n, IsFiniteMeasure (μK n) :=
    fun n => ⟨(hμKuniv n).trans_lt ENNReal.ofReal_lt_top⟩
  have htrans : ∀ n (φ : SpatialCoordinates d → ℝ),
      ∫ x, φ x ∂(μ n) = ∫ y, φ (y : SpatialCoordinates d) ∂(μK n) := by
    intro n φ
    have h1 : (μ n).restrict K = μ n :=
      Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (hμK n))
    have h2 : (μK n).map Subtype.val = (μ n).restrict K := by
      change ((μ n).comap Subtype.val).map Subtype.val = _
      rw [hemb.map_comap, Subtype.range_coe]
    rw [← h1, ← h2, hemb.integral_map]
  have hint : ∀ n (g : C(K, ℝ)), Integrable (fun y => g y) (μK n) := fun n g =>
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let Λ : ℕ → C(K, ℝ) → ℝ := fun n g => ∫ y, g y ∂(μK n)
  have hΛbd : ∀ n (g : C(K, ℝ)), ‖Λ n g‖ ≤ max M 0 * ‖g‖ := by
    intro n g
    have h := norm_integral_le_of_norm_le_const (μ := μK n) (f := fun y => g y) (C := ‖g‖)
      (Eventually.of_forall fun y => g.norm_coe_le_norm y)
    refine h.trans ?_
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) (hμKuniv n)
  have hΛsub : ∀ n (g h : C(K, ℝ)), Λ n g - Λ n h = Λ n (g - h) := by
    intro n g h
    change (∫ y, g y ∂(μK n)) - ∫ y, h y ∂(μK n) = ∫ y, (g - h) y ∂(μK n)
    rw [← integral_sub (hint n g) (hint n h)]
    rfl
  have hlip : ∀ n, LipschitzWith (Real.toNNReal (max M 0)) (Λ n) := by
    intro n
    refine LipschitzWith.of_dist_le_mul fun g h => ?_
    rw [Real.dist_eq, hΛsub, dist_eq_norm, Real.coe_toNNReal _ (le_max_right _ _)]
    exact hΛbd n (g - h)
  have heq : Equicontinuous Λ :=
    (LipschitzWith.uniformEquicontinuous Λ _ hlip).equicontinuous
  have hbd : ∀ g : C(K, ℝ), ∃ C : ℝ, ∀ n, ‖Λ n g‖ ≤ C :=
    fun g => ⟨max M 0 * ‖g‖, fun n => hΛbd n g⟩
  obtain ⟨L, σ, hσ, -, hL⟩ := exists_pointwise_subseq_of_equicontinuous heq hbd
  -- linearity and positivity of the limit functional
  have hadd : ∀ g h : C(K, ℝ), L (g + h) = L g + L h := by
    intro g h
    refine tendsto_nhds_unique (hL (g + h)) ?_
    have hpt : ∀ n, Λ (σ n) (g + h) = Λ (σ n) g + Λ (σ n) h := by
      intro n
      change ∫ y, (g + h) y ∂(μK (σ n)) = (∫ y, g y ∂(μK (σ n))) + ∫ y, h y ∂(μK (σ n))
      rw [← integral_add (hint _ g) (hint _ h)]
      rfl
    simp only [hpt]
    exact (hL g).add (hL h)
  have hsmul : ∀ (c : ℝ) (g : C(K, ℝ)), L (c • g) = c * L g := by
    intro c g
    refine tendsto_nhds_unique (hL (c • g)) ?_
    have hpt : ∀ n, Λ (σ n) (c • g) = c * Λ (σ n) g := by
      intro n
      change ∫ y, (c • g) y ∂(μK (σ n)) = c * ∫ y, g y ∂(μK (σ n))
      rw [← integral_const_mul]
      rfl
    simp only [hpt]
    exact (hL g).const_mul c
  have hmono : ∀ g h : C(K, ℝ), g ≤ h → L g ≤ L h := by
    intro g h hgh
    refine le_of_tendsto_of_tendsto (hL g) (hL h) (Eventually.of_forall fun n => ?_)
    exact integral_mono (hint _ g) (hint _ h) (fun y => hgh y)
  let Lm : CompactlySupportedContinuousMap K ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun f => L f.toContinuousMap
      map_add' := fun f g => hadd _ _
      map_smul' := fun c f => by simpa using! hsmul c f.toContinuousMap }
  let Lp : CompactlySupportedContinuousMap K ℝ →ₚ[ℝ] ℝ :=
    { Lm with monotone' := fun f g hfg => hmono _ _ hfg }
  let νK : Measure K := RealRMK.rieszMeasure Lp
  have hνKfin : νK Set.univ < ⊤ := isCompact_univ.measure_lt_top
  refine ⟨νK.map Subtype.val, σ, hσ, ?_, ?_, ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ]
    exact hνKfin
  · rw [Measure.map_apply measurable_subtype_coe hKm.compl]
    have : (Subtype.val : K → SpatialCoordinates d) ⁻¹' Kᶜ = ∅ := by
      ext y; simp
    rw [this, measure_empty]
  · intro φ hφ
    let gφ : C(K, ℝ) := ⟨K.domRestrict φ, hφ.domRestrict⟩
    let fφ : CompactlySupportedContinuousMap K ℝ := ⟨gφ, HasCompactSupport.of_compactSpace _⟩
    have hν : ∫ x, φ x ∂(νK.map Subtype.val) = L gφ := by
      rw [hemb.integral_map]
      exact RealRMK.integral_rieszMeasure Lp fφ
    rw [hν]
    have hμ : ∀ n, ∫ x, φ x ∂(μ (σ n)) = Λ (σ n) gφ := fun n => htrans (σ n) φ
    simp only [hμ]
    exact hL gφ

/-- D2 (closed sets).  Convergence against all functions continuous on `K` gives the
closed-set half of the portmanteau theorem. -/
theorem aux_prop_boundary_limsup_closed {d : ℕ} (K : Set (SpatialCoordinates d))
    (μ : ℕ → Measure (SpatialCoordinates d)) (ν : Measure (SpatialCoordinates d))
    (hμ : ∀ n, μ n Set.univ < ⊤) (hν : ν Set.univ < ⊤)
    (hconv : ∀ φ : SpatialCoordinates d → ℝ, ContinuousOn φ K →
      Tendsto (fun n => ∫ x, φ x ∂(μ n)) atTop (𝓝 (∫ x, φ x ∂ν)))
    (F : Set (SpatialCoordinates d)) (hF : IsClosed F) :
    limsup (fun n => μ n F) atTop ≤ ν F := by
  have : ∀ n, IsFiniteMeasure (μ n) := fun n => ⟨hμ n⟩
  have : IsFiniteMeasure ν := ⟨hν⟩
  let μF : ℕ → FiniteMeasure (SpatialCoordinates d) := fun n => ⟨μ n, inferInstance⟩
  let νF : FiniteMeasure (SpatialCoordinates d) := ⟨ν, inferInstance⟩
  have hT : Tendsto μF atTop (𝓝 νF) := by
    rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    exact hconv f f.continuous.continuousOn
  exact FiniteMeasure.limsup_measure_closed_le_of_tendsto hT hF

/-- D2 (open sets).  A uniform bound on the masses of an open set passes to the limit. -/
theorem aux_prop_boundary_open_le {d : ℕ} (K : Set (SpatialCoordinates d))
    (μ : ℕ → Measure (SpatialCoordinates d)) (ν : Measure (SpatialCoordinates d))
    (hμ : ∀ n, μ n Set.univ < ⊤) (hν : ν Set.univ < ⊤)
    (hconv : ∀ φ : SpatialCoordinates d → ℝ, ContinuousOn φ K →
      Tendsto (fun n => ∫ x, φ x ∂(μ n)) atTop (𝓝 (∫ x, φ x ∂ν)))
    (O : Set (SpatialCoordinates d)) (hO : IsOpen O) (c : ℝ≥0∞)
    (hc : ∀ n, μ n O ≤ c) : ν O ≤ c := by
  by_contra hlt
  push Not at hlt
  have hνO : ν O < ⊤ := (measure_mono (subset_univ _)).trans_lt hν
  have hc_top : c ≠ ⊤ := (hlt.trans hνO).ne
  have hlt' : c.toReal < (ν O).toReal := (ENNReal.toReal_lt_toReal hc_top hνO.ne).2 hlt
  set η : ℝ := ((ν O).toReal - c.toReal) / 3 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  have hνOc : ν Oᶜ < ⊤ := (measure_mono (subset_univ _)).trans_lt hν
  have hcl := aux_prop_boundary_limsup_closed K μ ν hμ hν hconv Oᶜ hO.isClosed_compl
  have hev1 : ∀ᶠ n in atTop, μ n Oᶜ < ν Oᶜ + ENNReal.ofReal η :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hcl
      (ENNReal.lt_add_right hνOc.ne (by simpa using hηpos)))
  have hmass : Tendsto (fun n => (μ n Set.univ).toReal) atTop (𝓝 (ν Set.univ).toReal) := by
    have h := hconv (fun _ => (1 : ℝ)) continuousOn_const
    simpa [integral_const, measureReal_def] using h
  have hev2 : ∀ᶠ n in atTop, (ν Set.univ).toReal - η < (μ n Set.univ).toReal :=
    hmass.eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, h1, h2⟩ := (hev1.and hev2).exists
  have hsplitμ : (μ n O).toReal + (μ n Oᶜ).toReal = (μ n Set.univ).toReal := by
    rw [← ENNReal.toReal_add ((measure_mono (subset_univ _)).trans_lt (hμ n)).ne
      ((measure_mono (subset_univ _)).trans_lt (hμ n)).ne,
      measure_add_measure_compl hO.measurableSet]
  have hsplitν : (ν O).toReal + (ν Oᶜ).toReal = (ν Set.univ).toReal := by
    rw [← ENNReal.toReal_add hνO.ne hνOc.ne, measure_add_measure_compl hO.measurableSet]
  have h1' : (μ n Oᶜ).toReal < (ν Oᶜ).toReal + η := by
    have := (ENNReal.toReal_lt_toReal (h1.trans (ENNReal.add_lt_top.2
      ⟨hνOc, ENNReal.ofReal_lt_top⟩)).ne (ENNReal.add_lt_top.2
      ⟨hνOc, ENNReal.ofReal_lt_top⟩).ne).2 h1
    rwa [ENNReal.toReal_add hνOc.ne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hηpos.le] at this
  have h3 : (μ n O).toReal ≤ c.toReal := ENNReal.toReal_mono hc_top (hc n)
  linarith



/-! ### Uniform limit. -/

/-- Near a point, every member of a finite family of closed sets that meets the
neighbourhood contains the point. -/
theorem aux_prop_boundary_local_cell {d : ℕ} {ι : Type*} [Fintype ι]
    (C : ι → Set (SpatialCoordinates d)) (hC : ∀ k, IsClosed (C k))
    (x : SpatialCoordinates d) :
    ∃ δ > 0, ∀ y, dist y x < δ → ∀ k, y ∈ C k → x ∈ C k := by
  classical
  let T : Set (SpatialCoordinates d) :=
    ⋃ k ∈ (Finset.univ.filter fun k => x ∉ C k), C k
  have hT : IsClosed T := isClosed_biUnion_finset fun k _ => hC k
  have hxT : x ∈ Tᶜ := by
    simp only [T, mem_compl_iff, mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      not_exists]
    exact fun k hk => hk
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hT.isOpen_compl x hxT
  refine ⟨δ, hδ, fun y hy k hyk => ?_⟩
  by_contra hxk
  have hyT : y ∈ T := by
    simp only [T, mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨k, hxk, hyk⟩
  exact hball (Metric.mem_ball.2 hy) hyT

/-- Uniform equicontinuity at a point of a family that is uniformly Hölder on each set of
a finite closed cover. -/
theorem aux_prop_boundary_equi_holder {d : ℕ} {ι : Type*} [Fintype ι]
    (C : ι → Set (SpatialCoordinates d)) (hC : ∀ k, IsClosed (C k))
    (F : ℕ → SpatialCoordinates d → ℝ) (H : ι → ℝ) (α : ℝ) (hα : 0 < α)
    (hF : ∀ n k, ∀ x ∈ C k, ∀ y ∈ C k, |F n x - F n y| ≤ H k * dist x y ^ α)
    (x : SpatialCoordinates d) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ ⋃ k, C k, dist y x < δ → ∀ n, |F n y - F n x| < ε := by
  obtain ⟨δ0, hδ0, hloc⟩ := aux_prop_boundary_local_cell C hC x
  set Hs : ℝ := ∑ k, |H k| with hHs
  have hHs0 : 0 ≤ Hs := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hHk : ∀ k, H k ≤ Hs := fun k =>
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (H j)) (Finset.mem_univ k))
  set e : ℝ := ε / (Hs + 1) with he
  have he0 : 0 < e := div_pos hε (by linarith)
  set δ1 : ℝ := e ^ α⁻¹ with hδ1
  have hδ1pos : 0 < δ1 := Real.rpow_pos_of_pos he0 _
  refine ⟨min δ0 δ1, lt_min hδ0 hδ1pos, fun y hy hyx n => ?_⟩
  obtain ⟨k, hyk⟩ := mem_iUnion.1 hy
  have hxk : x ∈ C k := hloc y (lt_of_lt_of_le hyx (min_le_left _ _)) k hyk
  have h1 := hF n k y hyk x hxk
  have hd : dist y x ^ α ≤ e := by
    have : dist y x ^ α ≤ δ1 ^ α :=
      Real.rpow_le_rpow dist_nonneg (lt_of_lt_of_le hyx (min_le_right _ _)).le hα.le
    rwa [hδ1, Real.rpow_inv_rpow he0.le hα.ne'] at this
  have hdnn : 0 ≤ dist y x ^ α := Real.rpow_nonneg dist_nonneg _
  have h2 : H k * dist y x ^ α ≤ Hs * e :=
    (mul_le_mul_of_nonneg_right (hHk k) hdnn).trans (mul_le_mul_of_nonneg_left hd hHs0)
  have h3 : Hs * e < ε := by
    rw [he, mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- Pointwise bound from the cellwise sup bound. -/
theorem aux_prop_boundary_cover_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (C : ι → Set (SpatialCoordinates d)) (F : ℕ → SpatialCoordinates d → ℝ) (H : ι → ℝ)
    (hF : ∀ n k, ∀ x ∈ C k, |F n x| ≤ H k) :
    ∀ x ∈ ⋃ k, C k, ∀ n, |F n x| ≤ ∑ k, |H k| := by
  intro x hx n
  obtain ⟨k, hk⟩ := mem_iUnion.1 hx
  exact (hF n k x hk).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (H j)) (Finset.mem_univ k)))

/-- One compactness extraction: along any sequence of indices tending to infinity, a
further subsequence converges pointwise on the compact set to a continuous function
which represents the `L²` limit. -/
theorem aux_prop_boundary_extract {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (hQne : (Q : Set (SpatialCoordinates d)).Nonempty)
    (F : ℕ → SpatialCoordinates d → ℝ) (M : ℝ)
    (hequi : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ ε > 0, ∃ δ > 0,
      ∀ y ∈ closure (Q : Set (SpatialCoordinates d)), dist y x < δ → ∀ n, |F n y - F n x| < ε)
    (hbd : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ n, |F n x| ≤ M)
    (W : ℕ → DomainL2 Q) (hW : ∀ n, (W n : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] F n)
    (u : DomainL2 Q) (hWu : Tendsto W atTop (𝓝 u))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ (ms : ℕ → ℕ) (g : SpatialCoordinates d → ℝ), StrictMono ms ∧
      ContinuousOn g (closure (Q : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
        Tendsto (fun m => F (ns (ms m)) x) atTop (𝓝 (g x))) ∧
      (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] g := by
  classical
  set Kc := closure (Q : Set (SpatialCoordinates d)) with hKc
  have : Nonempty Kc := by
    obtain ⟨z, hz⟩ := hQne
    exact ⟨⟨z, subset_closure hz⟩⟩
  let f : ℕ → Kc → ℝ := fun m x => F (ns m) x
  have heq : Equicontinuous f := by
    intro x0
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hequi x0.1 x0.2 ε hε
    refine ⟨δ, hδ, fun y hy m => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact h y.1 y.2 (by simpa [Subtype.dist_eq] using hy) (ns m)
  have hbd' : ∀ x : Kc, ∃ C : ℝ, ∀ m, ‖f m x‖ ≤ C :=
    fun x => ⟨M, fun m => by rw [Real.norm_eq_abs]; exact hbd x.1 x.2 (ns m)⟩
  obtain ⟨g, ms, hms, hg, hconv⟩ := exists_pointwise_subseq_of_equicontinuous heq hbd'
  let gext : SpatialCoordinates d → ℝ := fun x => if h : x ∈ Kc then g ⟨x, h⟩ else 0
  have hgext : ∀ x (h : x ∈ Kc), gext x = g ⟨x, h⟩ := fun x h => by simp [gext, h]
  refine ⟨ms, gext, hms, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : Kc.domRestrict gext = g := by
      funext x
      simp only [Set.domRestrict_apply, hgext x.1 x.2]
    rw [this]
    exact hg
  · intro x hx
    rw [hgext x hx]
    exact hconv ⟨x, hx⟩
  · have hsub : Tendsto (fun m => W (ns (ms m))) atTop (𝓝 u) :=
      hWu.comp (hns.comp hms.tendsto_atTop)
    have hmeas := tendstoInMeasure_of_tendsto_Lp hsub
    obtain ⟨ls, hls, hae⟩ := hmeas.exists_seq_tendsto_ae
    have hrep : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        ∀ n, (W n : SpatialCoordinates d → ℝ) x = F n x := ae_all_iff.2 hW
    filter_upwards [hae, hrep, ae_restrict_mem Q.isOpen.measurableSet] with x hx hr hxQ
    have hxK : x ∈ Kc := subset_closure hxQ
    have h1 : Tendsto (fun i => F (ns (ms (ls i))) x) atTop (𝓝 (u x)) := by
      refine hx.congr fun i => ?_
      exact hr _
    have h2 : Tendsto (fun i => F (ns (ms (ls i))) x) atTop (𝓝 (gext x)) := by
      rw [hgext x hxK]
      exact (hconv ⟨x, hxK⟩).comp hls.tendsto_atTop
    exact tendsto_nhds_unique h1 h2

/-- C1/C2 : equi-Hölder on each closed cell
plus the represented `L²` limit gives full-sequence uniform convergence on the
closed cube to a continuous representative of `uBar`.  Every uniform cluster equals
the represented `L²` limit almost everywhere, hence everywhere on the closed cube. -/
theorem aux_prop_boundary_uniform_limit {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (uBar : DomainL2 (centeredCube z (3 * r) h3r))
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (alpha : ℝ) (halpha : 0 < alpha)
    (Hcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hCellHolder : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        ∀ y ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
          |(UN n).toFun x - (UN n).toFun y| ≤ Hcell k * dist x y ^ alpha) ∧
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        |(UN n).toFun x| ≤ Hcell k)) :
    ∃ Uc : SpatialCoordinates d → ℝ,
      ContinuousOn Uc
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (uBar : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc ∧
      TendstoUniformlyOn (fun n => (UN n).toFun) Uc atTop
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) := by
  classical
  set Kc := closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) with hKc
  let C : OddGridIndex d (triadicHalf 1) → Set (SpatialCoordinates d) := fun k =>
    closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
  have hcover : (⋃ k, C k) = Kc :=
    oddGridCell_closure_iUnion_eq_closure_centeredCube z h3r (triadicHalf 1)
  let F : ℕ → SpatialCoordinates d → ℝ := fun n => (UN n).toFun
  have hequi : ∀ x ∈ Kc, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Kc, dist y x < δ →
      ∀ n, |F n y - F n x| < ε := by
    intro x _ ε hε
    obtain ⟨δ, hδ, h⟩ := aux_prop_boundary_equi_holder C (fun k => isClosed_closure) F Hcell
      alpha halpha (fun n k => (hCellHolder n k).1) x ε hε
    exact ⟨δ, hδ, fun y hy => h y (hcover ▸ hy)⟩
  have hbd : ∀ x ∈ Kc, ∀ n, |F n x| ≤ ∑ k, |Hcell k| := by
    intro x hx n
    exact aux_prop_boundary_cover_bound C F Hcell (fun n k => (hCellHolder n k).2) x
      (hcover ▸ hx) n
  have hQc : IsCompact Kc := lane2_isCompact_closure_centeredCube z h3r
  have hQne : (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)).Nonempty :=
    ⟨z, by rw [centeredCube_coe_eq_ball]; exact Metric.mem_ball_self (by linarith)⟩
  have hW : ∀ n, ((UNS n).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] F n := by
    intro n
    have h := congrArg Prod.fst (hUNrep n)
    change (UNS n).val.1 = (sobolevDataOfH1 (UN n)).1 at h
    rw [h]
    exact sobolevDataOfH1_fst_coeFn (UN n)
  obtain ⟨ms0, Uc, -, hUc, -, hUae⟩ := aux_prop_boundary_extract _ hQne F _ hequi hbd
    (fun n => (UNS n).val.1) hW uBar hUNL2 id tendsto_id
  have hpt : ∀ x ∈ Kc, Tendsto (fun n => F n x) atTop (𝓝 (Uc x)) := by
    intro x hx
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, g, -, hg, hgconv, hgae⟩ := aux_prop_boundary_extract _ hQne F _ hequi hbd
      (fun n => (UNS n).val.1) hW uBar hUNL2 ns hns
    have hEq : Set.EqOn g Uc Kc :=
      aux_prop_boundary_eqOn_closure_of_ae z (3 * r) h3r g Uc hg hUc (hgae.symm.trans hUae)
    exact ⟨ms, (hEq hx) ▸ hgconv x hx⟩
  refine ⟨Uc, hUc, hUae, ?_⟩
  refine tendstoUniformlyOn_of_compact_moving_points hQc hUc ?_
  intro u x φ hu hx hφ hux
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδh⟩ := hequi x hx (ε / 2) (half_pos hε)
  have h1 : ∀ᶠ n in atTop, dist (u n) x < δ := (Metric.tendsto_nhds.1 hux) δ hδ
  have h2 : ∀ᶠ n in atTop, dist (F (φ n) x) (Uc x) < ε / 2 :=
    (Metric.tendsto_nhds.1 ((hpt x hx).comp hφ.tendsto_atTop)) (ε / 2) (half_pos hε)
  filter_upwards [h1, h2] with n hn1 hn2
  have h3 := hδh (u n) (hu n) hn1 (φ n)
  rw [Real.dist_eq] at hn2 ⊢
  calc |F (φ n) (u n) - Uc x| ≤ |F (φ n) (u n) - F (φ n) x| + |F (φ n) x - Uc x| :=
        abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h3 hn2
    _ = ε := add_halves ε



/-! ### Weak clusters of the energy measures. -/

/-- Every subsequence of a bounded family of energy measures with small-ball growth has
a further weak cluster `ν`; the cluster dominates any measure supplied by the lower-bound
clause, has the same growth, and charges no cube face. -/
theorem aux_prop_boundary_cluster_generic {d : ℕ} (hd : 2 ≤ d)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (μN : ℕ → Measure (SpatialCoordinates d)) (E0 Kg t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ)) (hKg : 0 ≤ Kg)
    (hmass : ∀ n, μN n Set.univ ≤ ENNReal.ofReal E0) (hsupp : ∀ n, μN n Kᶜ = 0)
    (hgrowth : ∀ n (x : SpatialCoordinates d) (s : ℝ), 0 < s → s ≤ 1 / 2 →
      μN n (Metric.ball x s) ≤ ENNReal.ofReal (Kg * s ^ t))
    (Γm : Measure (SpatialCoordinates d))
    (hclause : ∀ (ν : Measure (SpatialCoordinates d)) (σ : ℕ → ℕ), ν Set.univ < ⊤ →
      ν Kᶜ = 0 → StrictMono σ →
      (∀ φ : SpatialCoordinates d → ℝ, ContinuousOn φ K →
        Tendsto (fun n => ∫ x, φ x ∂(μN (σ n))) atTop (𝓝 (∫ x, φ x ∂ν))) →
      ∀ B : Set (SpatialCoordinates d), MeasurableSet B → Γm B ≤ ν B)
    (σ0 : ℕ → ℕ) (hσ0 : StrictMono σ0) :
    ∃ (ν : Measure (SpatialCoordinates d)) (σ : ℕ → ℕ), StrictMono σ ∧
      ν Set.univ < ⊤ ∧ ν Kᶜ = 0 ∧
      (∀ φ : SpatialCoordinates d → ℝ, ContinuousOn φ K →
        Tendsto (fun n => ∫ x, φ x ∂(μN (σ0 (σ n)))) atTop (𝓝 (∫ x, φ x ∂ν))) ∧
      (∀ B : Set (SpatialCoordinates d), MeasurableSet B → Γm B ≤ ν B) ∧
      (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        ν (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0) := by
  obtain ⟨ν, σ, hσ, hνfin, hνK, hconv⟩ := aux_prop_boundary_weak_cluster K hK
    (fun n => μN (σ0 n)) E0 (fun n => hsupp _) (fun n => hmass _)
  have hΓ := hclause ν (σ0 ∘ σ) hνfin hνK (hσ0.comp hσ) hconv
  have hμfin : ∀ n, μN (σ0 (σ n)) Set.univ < ⊤ :=
    fun n => (hmass _).trans_lt ENNReal.ofReal_lt_top
  have hνball : ∀ (x : SpatialCoordinates d) (s : ℝ), 0 < s → s ≤ 1 / 2 →
      ν (Metric.ball x s) ≤ ENNReal.ofReal (Kg * s ^ t) := fun x s hs hs2 =>
    aux_prop_boundary_open_le K (fun n => μN (σ0 (σ n))) ν hμfin hνfin hconv _
      Metric.isOpen_ball _ (fun n => hgrowth _ x s hs hs2)
  have hνuniv : ν Set.univ ≤ ENNReal.ofReal E0 :=
    aux_prop_boundary_open_le K (fun n => μN (σ0 (σ n))) ν hμfin hνfin hconv _
      isOpen_univ _ (fun n => hmass _)
  refine ⟨ν, σ, hσ, hνfin, hνK, hconv, hΓ, fun z r hr => ?_⟩
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have ht0 : 0 ≤ t := by linarith
  have h2t : (1 : ℝ) ≤ 2 ^ t := Real.one_le_rpow (by norm_num) ht0
  set Kb : ℝ := 2 ^ t * (Kg + max E0 0) with hKb
  have hKb0 : 0 ≤ Kb := by positivity
  refine _root_.SubdiffusiveProcess.Paper.chaos_limit_null_frontier hd ((d : ℝ) - t) ⟨by linarith, by linarith⟩ ν
    (fun _ _ => ⟨Kb, hKb0, fun x _ s hs hs1 => ?_⟩) z r hr
  rw [sub_sub_cancel]
  have hst : 0 ≤ s ^ t := Real.rpow_nonneg hs.le _
  by_cases hs2 : s ≤ 1 / 2
  · refine (hνball x s hs hs2).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_right _ hst
    rw [hKb]
    nlinarith [le_max_right E0 0]
  · push Not at hs2
    refine (measure_mono (subset_univ _)).trans (hνuniv.trans (ENNReal.ofReal_le_ofReal ?_))
    have h2s : (1 : ℝ) ≤ (2 * s) ^ t := Real.one_le_rpow (by linarith) ht0
    have heq : Kb * s ^ t = (Kg + max E0 0) * (2 * s) ^ t := by
      rw [hKb, Real.mul_rpow (by norm_num) hs.le]; ring
    rw [heq]
    have hm : 0 ≤ Kg + max E0 0 := by positivity
    nlinarith [le_max_left E0 0, le_max_right E0 0]

/-- Small-ball growth of one cell's energy measure from the per-cell growth bound. -/
theorem aux_prop_boundary_cell_small_growth {d : ℕ} (cell : Set (SpatialCoordinates d))
    (hcell : IsOpen cell) (g : SpatialCoordinates d → ENNReal) (B t : ℝ)
    (hbound : ∀ y ∈ closure cell, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
      ((volume.restrict cell).withDensity g) (Metric.ball y rr) ≤ ENNReal.ofReal (B * rr ^ t))
    (x : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (hs2 : 2 * s ≤ 1) :
    ((volume.restrict cell).withDensity g) (Metric.ball x s) ≤
      ENNReal.ofReal (B * (2 * s) ^ t) := by
  by_cases hne : (Metric.ball x s ∩ cell).Nonempty
  · obtain ⟨y, hyball, hycell⟩ := hne
    have hsub : Metric.ball x s ∩ cell ⊆ Metric.ball y (2 * s) ∩ cell := by
      intro w hw
      refine ⟨?_, hw.2⟩
      have := Metric.mem_ball.1 hw.1
      rw [Metric.mem_ball] at hyball ⊢
      calc dist w y ≤ dist w x + dist x y := dist_triangle _ _ _
        _ < s + s := add_lt_add this (by rw [dist_comm]; exact hyball)
        _ = 2 * s := by ring
    exact (aux_catalog_cutoff_existence_cell_measure_mono cell hcell g _ _
      Metric.isOpen_ball.measurableSet Metric.isOpen_ball.measurableSet hsub).trans
      (hbound y (subset_closure hycell) (2 * s) (by linarith) hs2)
  · have hsub : Metric.ball x s ∩ cell ⊆ (∅ : Set (SpatialCoordinates d)) ∩ cell := by
      intro w hw
      exact absurd ⟨w, hw⟩ hne
    refine (aux_catalog_cutoff_existence_cell_measure_mono cell hcell g _ _
      Metric.isOpen_ball.measurableSet MeasurableSet.empty hsub).trans ?_
    simp

/-- B2: global small-ball growth of the energy measure of `U_N` on `Q` from the per-cell
growth bounds ("sums over finitely many cells"). -/
theorem aux_prop_boundary_global_growth {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (g : SpatialCoordinates d → ENNReal) (t : ℝ) (ht0 : 0 ≤ t)
    (Bcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hBcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Bcell k)
    (hCellGrowth : ∀ k : OddGridIndex d (triadicHalf 1),
      ∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
          g) (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t))
    (x : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (hs2 : s ≤ 1 / 2) :
    ((volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity g)
        (Metric.ball x s) ≤
      ENNReal.ofReal ((2 : ℝ) ^ t * (∑ k, Bcell k) * s ^ t) := by
  rw [aux_catalog_cutoff_existence_partition_measure z (3 * r) h3r (triadicHalf 1) g x s,
    ← aux_catalog_cutoff_existence_sum_power Bcell t s hBcell ht0 hs.le]
  exact Finset.sum_le_sum fun k _ =>
    aux_prop_boundary_cell_small_growth _ (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
      g (Bcell k) t (hCellGrowth k) x s hs (by linarith)

/-- Total mass of an energy measure is the response energy. -/
theorem aux_prop_boundary_mass_univ {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : PositiveCoefficient Q) (w : S.space) :
    ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (a.val y * ∑ i : Fin d, ((w : SobolevData Q).2 i y) ^ 2)))
        Set.univ = ENNReal.ofReal (responseForm S a w w) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact aux_prop_locality_recovery_mass_eq S a w

/-- An energy measure on `Q` is carried by `closure Q`. -/
theorem aux_prop_boundary_supp {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (g : SpatialCoordinates d → ENNReal) :
    ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity g)
      (closure (Q : Set (SpatialCoordinates d)))ᶜ = 0 := by
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
  have : (closure (Q : Set (SpatialCoordinates d)))ᶜ ∩ (Q : Set (SpatialCoordinates d)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    exact hx1 (subset_closure hx2)
  rw [this, measure_empty]

/-- The cluster lemma in the setting of `prop_boundary`: along every subsequence there is a
weak cluster `ν` of `Γ_N(U_N)` with `Γ(Ū) ≤ ν` and `ν(∂q) = 0`
(Corollary `cor_energy_measures`(b) and the face covering). -/
theorem aux_prop_boundary_cluster {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (UNS : ℕ → S.space)
    (uBar : DomainL2 (centeredCube z (3 * r) h3r))
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (Bcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hBcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Bcell k)
    (hCellGrowth : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y *
            ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t))
    (E0 : ℝ) (hE0 : ∀ n : ℕ, responseForm S (aC n) (UNS n) (UNS n) ≤ E0)
    (hB : ∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
          (uN : ℕ → S.space) (E0 : ℝ)
          (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
        nu Set.univ < (⊤ : ENNReal) →
        nu ((closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))ᶜ) = 0 →
        StrictMono sigma →
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        (∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC (sigma n)).val y *
                ∑ i : Fin d, ((uN (sigma n) : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂nu))) →
        u ∈ EQ.toClosedForm.domain ∧
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            Gamma.measure u B ≤ nu B)
    (σ0 : ℕ → ℕ) (hσ0 : StrictMono σ0) :
    ∃ (ν : Measure (SpatialCoordinates d)) (σ : ℕ → ℕ), StrictMono σ ∧
      ν Set.univ < ⊤ ∧
      ν (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))ᶜ = 0 ∧
      (∀ φ : SpatialCoordinates d → ℝ,
        ContinuousOn φ (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        Tendsto (fun n => ∫ x, φ x ∂(((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC (σ0 (σ n))).val y *
                ∑ i : Fin d, ((UNS (σ0 (σ n)) : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
          (𝓝 (∫ x, φ x ∂ν))) ∧
      (∀ B : Set (SpatialCoordinates d), MeasurableSet B → Gamma.measure uBar B ≤ ν B) ∧
      (∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
        ν (frontier (centeredCube zc rc hrc : Set (SpatialCoordinates d))) = 0) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have ht0 : 0 ≤ t := by linarith
  have hKg : 0 ≤ (2 : ℝ) ^ t * (∑ k, Bcell k) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Finset.sum_nonneg fun k _ => hBcell k)
  refine aux_prop_boundary_cluster_generic hd _ (lane2_isCompact_closure_centeredCube z h3r)
    (fun n => ((volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
        (fun y => ENNReal.ofReal ((aC n).val y *
          ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
    E0 ((2 : ℝ) ^ t * (∑ k, Bcell k)) t ht htd hKg ?_ ?_ ?_ (Gamma.measure uBar) ?_ σ0 hσ0
  · intro n
    rw [aux_prop_boundary_mass_univ S (aC n) (UNS n)]
    exact ENNReal.ofReal_le_ofReal (hE0 n)
  · intro n
    exact aux_prop_boundary_supp _ _
  · intro n x s hs hs2
    exact aux_prop_boundary_global_growth z r h3r _ t ht0 Bcell hBcell (hCellGrowth n) x s hs hs2
  · intro ν σ hνfin hνK hσ hconv
    exact (hB uBar UNS E0 ν σ hνfin hνK hσ hUNL2 hE0 hconv).2




/-! ### Harmonicity on the centre cell. -/

/-- The represented coefficient is measurable and bounded on `Q`. -/
theorem aux_prop_boundary_coeff_ae {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (hQc : IsCompact (closure (Q : Set (SpatialCoordinates d))))
    (a : SpatialCoordinates d → ℝ) (aC : PositiveCoefficient Q)
    (hacont : ContinuousOn a (closure (Q : Set (SpatialCoordinates d))))
    (haC : ((aC).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] a) :
    AEStronglyMeasurable ((aC).val : SpatialCoordinates d → ℝ)
        (volume.restrict (Q : Set (SpatialCoordinates d))) ∧
      ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        ‖(aC).val x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hQc.exists_bound_of_continuousOn hacont
  refine ⟨Lp.aestronglyMeasurable _, C, ?_⟩
  filter_upwards [haC, ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
  rw [hx]; exact hC x (subset_closure hxQ)

/-- E1: `U_N` is orthogonal to smooth tests supported in a cell where it is harmonic. -/
theorem aux_prop_boundary_orth_smooth {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hacont : ∀ n : ℕ, ContinuousOn (a n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (W : Set (SpatialCoordinates d)) (hWo : IsOpen W)
    (hWQ : W ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (n : ℕ)
    (hharm : IsWeaklyHarmonicOn (a n) W ((UN n).restrict hWo hWQ))
    (ζ : 𝓓(centeredCube z (3 * r) h3r, ℝ)) (hζ : tsupport (ζ : SpatialCoordinates d → ℝ) ⊆ W)
    (hζS : smoothSobolevData ζ ∈ S.space) :
    responseForm S (aC n) (UNS n) ⟨smoothSobolevData ζ, hζS⟩ = 0 := by
  have hQo := (centeredCube z (3 * r) h3r).isOpen
  have hζc : ContDiff ℝ ∞ (ζ : SpatialCoordinates d → ℝ) := ζ.contDiff
  let ζQ : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiff hQo (hζc.of_le (by simp)) ζ.hasCompactSupport
  have hsd : sobolevDataOfH1 ζQ = smoothSobolevData ζ := by
    refine Prod.ext ?_ ?_
    · apply Lp.ext
      filter_upwards [sobolevDataOfH1_fst_coeFn ζQ, testL2_coeFn ζ] with x h1 h2
      change _ = (testL2 ζ : SpatialCoordinates d → ℝ) x
      rw [h1, h2]; rfl
    · funext i
      apply Lp.ext
      filter_upwards [sobolevDataOfH1_snd_coeFn ζQ i, testPartialL2_coeFn ζ i] with x h1 h2
      change _ = (testPartialL2 ζ i : SpatialCoordinates d → ℝ) x
      rw [h1, h2]; rfl
  obtain ⟨hameas, C, habd⟩ := aux_prop_boundary_coeff_ae _
    (lane2_isCompact_closure_centeredCube z h3r) (a n) (aC n) (hacont n) (haC n)
  have hint : ∀ i : Fin d, IntegrableOn
      (fun x => (aC n).val x * ((UN n).grad x i * ζQ.grad x i))
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) volume := fun i =>
    lane2_integrableOn_coeff_mul hameas habd ((UN n).gradMemL2 i) (ζQ.gradMemL2 i)
  have e1a : responseForm S (aC n) (UNS n) ⟨smoothSobolevData ζ, hζS⟩ =
      sobolevCoefficientForm (aC n) (UNS n : SobolevData (centeredCube z (3 * r) h3r))
        (smoothSobolevData ζ) := rfl
  have e1 : responseForm S (aC n) (UNS n) ⟨smoothSobolevData ζ, hζS⟩ =
      sobolevCoefficientForm (aC n) (sobolevDataOfH1 (UN n)) (sobolevDataOfH1 ζQ) :=
    e1a.trans (congrArg₂ (fun u v => sobolevCoefficientForm (aC n) u v) (hUNrep n) hsd.symm)
  rw [e1, sobolevCoefficientForm_eq_integral_vecDot (aC n) (UN n) ζQ hint]
  have e3 : (∫ x in (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        vecDot ((aC n).val x • (UN n).grad x) (ζQ.grad x))
      = ∫ x in (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        vecDot (a n x • (UN n).grad x) (ζQ.grad x) := by
    apply setIntegral_congr_ae hQo.measurableSet
    filter_upwards [(MeasureTheory.ae_restrict_iff' hQo.measurableSet).mp (haC n)] with x hx hxQ
    rw [hx hxQ]
  rw [e3, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQo.measurableSet hWQ]
  · have h := hharm (H10Function.ofContDiff hWo hζc ζ.hasCompactSupport hζ)
    have hgU : ((UN n).restrict hWo hWQ).grad = (UN n).grad := rfl
    have hgζ : (H10Function.ofContDiff hWo hζc ζ.hasCompactSupport hζ).toH1Function.grad =
        ζQ.grad := rfl
    rw [hgU, hgζ] at h
    exact h
  · intro x hx
    have hxt : x ∉ tsupport (ζ : SpatialCoordinates d → ℝ) := fun h => hx.2 (hζ h)
    have h0 : fderiv ℝ (ζ : SpatialCoordinates d → ℝ) x = 0 := fderiv_of_notMem_tsupport ℝ hxt
    have hg : ζQ.grad x = 0 := by
      funext i
      change fderiv ℝ (ζ : SpatialCoordinates d → ℝ) x (basisVec i) = 0
      rw [h0]; rfl
    rw [hg]
    simp [vecDot]




/-- A smooth bump: equal to one near a compact set, supported in a given open set. -/
theorem aux_prop_boundary_bump {d : ℕ} (Ω : Opens (SpatialCoordinates d))
    (Kc W : Set (SpatialCoordinates d)) (hKc : IsCompact Kc) (hW : IsOpen W) (hKW : Kc ⊆ W)
    (hKΩ : Kc ⊆ (Ω : Set (SpatialCoordinates d))) :
    ∃ (η : 𝓓(Ω, ℝ)) (O1 : Set (SpatialCoordinates d)), IsOpen O1 ∧ Kc ⊆ O1 ∧
      tsupport (η : SpatialCoordinates d → ℝ) ⊆ W ∧
      ∀ x ∈ O1, (η : SpatialCoordinates d → ℝ) x = 1 ∧
        fderiv ℝ (η : SpatialCoordinates d → ℝ) x = 0 := by
  obtain ⟨O2, hO2, hKO2, hO2cl, hO2c⟩ :=
    exists_open_between_and_isCompact_closure hKc (hW.inter Ω.isOpen) (subset_inter hKW hKΩ)
  obtain ⟨O1, hO1, hKO1, hO1cl, -⟩ := exists_open_between_and_isCompact_closure hKc hO2 hKO2
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (modelWithCornersSelf ℝ (SpatialCoordinates d)) hO2.isClosed_compl
    (isClosed_closure (s := O1))
    (Set.disjoint_left.2 fun x hx hx' => hx (hO1cl hx'))
  have hfc : ContDiff ℝ ∞ (f : SpatialCoordinates d → ℝ) := contMDiff_iff_contDiff.1 f.contMDiff
  have hsupp : Function.support (f : SpatialCoordinates d → ℝ) ⊆ O2 := by
    intro x hx
    by_contra hxO
    exact hx (hf0 hxO)
  have hts : tsupport (f : SpatialCoordinates d → ℝ) ⊆ closure O2 := closure_mono hsupp
  refine ⟨⟨f, hfc, hO2c.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans (fun x hx => (hO2cl hx).2)⟩, O1, hO1, hKO1,
    hts.trans (fun x hx => (hO2cl hx).1), fun x hx => ⟨hf1 (subset_closure hx), ?_⟩⟩
  have hev : (f : SpatialCoordinates d → ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem (hO1.mem_nhds hx) (fun y hy => hf1 (subset_closure hy))
  change fderiv ℝ (f : SpatialCoordinates d → ℝ) x = 0
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 1

/-- Density step of E2: orthogonality to smooth tests supported in `W` passes to every
response element fixed by multiplication with a test function supported in `W`. -/
theorem aux_prop_boundary_orth_of_mulTest {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω) (A : PositiveCoefficient Ω)
    (X : S.space) (W : Set (SpatialCoordinates d))
    (horth : ∀ (ζ : 𝓓(Ω, ℝ)) (hζS : smoothSobolevData ζ ∈ S.space),
      tsupport (ζ : SpatialCoordinates d → ℝ) ⊆ W → responseForm S A X ⟨_, hζS⟩ = 0)
    (η : 𝓓(Ω, ℝ)) (hηW : tsupport (η : SpatialCoordinates d → ℝ) ⊆ W)
    (Y : S.space) (hfix : aux_prop_locality_recovery_mulTest η (Y : SobolevData Ω) = Y) :
    responseForm S A X Y = 0 := by
  let F : SobolevData Ω →L[ℝ] ℝ :=
    ((weightedGradientForm A.val) (sobolevGradient (X : SobolevData Ω))).comp
      (sobolevGradient.comp (aux_prop_locality_recovery_mulTest η))
  have hFapp : ∀ Z : SobolevData Ω, F Z = weightedGradientForm A.val
      (sobolevGradient (X : SobolevData Ω))
      (sobolevGradient (aux_prop_locality_recovery_mulTest η Z)) := fun Z => rfl
  have hFsmooth : LinearMap.range (smoothSobolevDataLinear (Ω := Ω)) ≤ LinearMap.ker F.toLinearMap := by
    rintro _ ⟨ψ, rfl⟩
    rw [LinearMap.mem_ker]
    have hψ : smoothSobolevDataLinear ψ = smoothSobolevData ψ := rfl
    rw [hψ]
    change F (smoothSobolevData ψ) = 0
    rw [hFapp, aux_prop_locality_recovery_mulTest_smooth]
    have hmem : smoothSobolevData (aux_prop_locality_recovery_testMul ψ η) ∈ S.space :=
      aux_prop_locality_recovery_mem_space S hS (smoothSobolevData_mem_killed _)
    have hfun : ((aux_prop_locality_recovery_testMul ψ η : 𝓓(Ω, ℝ)) :
        SpatialCoordinates d → ℝ) = fun x => ψ x * η x := rfl
    have hsub : tsupport ((aux_prop_locality_recovery_testMul ψ η : 𝓓(Ω, ℝ)) :
        SpatialCoordinates d → ℝ) ⊆ W := by
      rw [hfun]
      exact tsupport_mul_subset_right.trans hηW
    exact horth _ hmem hsub
  have hker : killedSobolevGraph Ω ≤ LinearMap.ker F.toLinearMap :=
    Submodule.topologicalClosure_minimal _ hFsmooth (ContinuousLinearMap.isClosed_ker F)
  have hY : F (Y : SobolevData Ω) = 0 :=
    LinearMap.mem_ker.1 (hker (aux_prop_locality_recovery_mem_killed S hS Y))
  rw [hFapp, hfix] at hY
  exact hY

/-- E2: orthogonality to smooth tests supported in an open set `W` extends to response
elements vanishing, with their gradients, outside a compact subset of `W`. -/
theorem aux_prop_boundary_orth_supported {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω) (A : PositiveCoefficient Ω)
    (X : S.space) (W : Set (SpatialCoordinates d)) (hW : IsOpen W)
    (horth : ∀ (ζ : 𝓓(Ω, ℝ)) (hζS : smoothSobolevData ζ ∈ S.space),
      tsupport (ζ : SpatialCoordinates d → ℝ) ⊆ W → responseForm S A X ⟨_, hζS⟩ = 0)
    (Kc : Set (SpatialCoordinates d)) (hKc : IsCompact Kc) (hKW : Kc ⊆ W)
    (hKΩ : Kc ⊆ (Ω : Set (SpatialCoordinates d)))
    (Y : S.space)
    (hY1 : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      x ∉ Kc → (Y : SobolevData Ω).1 x = 0)
    (hY2 : ∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      x ∉ Kc → (Y : SobolevData Ω).2 i x = 0) :
    responseForm S A X Y = 0 := by
  obtain ⟨η, O1, -, hKO1, hηW, hη⟩ := aux_prop_boundary_bump Ω Kc W hKc hW hKW hKΩ
  refine aux_prop_boundary_orth_of_mulTest S hS A X W horth η hηW Y ?_
  refine Prod.ext ?_ ?_
  · apply Lp.ext
    rw [aux_prop_locality_recovery_mulTest_fst]
    filter_upwards [aux_prop_locality_recovery_mulL_coeFn
        (aux_prop_locality_recovery_testLinf η) (Y : SobolevData Ω).1,
      aux_prop_locality_recovery_testLinf_coeFn η, hY1] with x h1 h2 h3
    rw [h1, h2]
    by_cases hx : x ∈ Kc
    · rw [(hη x (hKO1 hx)).1, one_mul]
    · rw [h3 hx, mul_zero]
  · funext i
    apply Lp.ext
    rw [aux_prop_locality_recovery_mulTest_snd]
    filter_upwards [Lp.coeFn_add
        (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf η i)
          (Y : SobolevData Ω).1)
        (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf η)
          ((Y : SobolevData Ω).2 i)),
      aux_prop_locality_recovery_modV_P_ae η (Y : SobolevData Ω) i,
      aux_prop_locality_recovery_modV_R_ae η (Y : SobolevData Ω) i, hY1, hY2 i]
      with x h0 h1 h2 h3 h4
    rw [h0, Pi.add_apply, h1, h2]
    by_cases hx : x ∈ Kc
    · rw [(hη x (hKO1 hx)).2, (hη x (hKO1 hx)).1]
      simp
    · rw [h3 hx, h4 hx]
      simp




/-! ### Localized recovery (proof of Proposition `prop_locality`). -/

/-- The inner modification `φ ψ` vanishes, with its gradient, outside `closure O` when the
cutoff representative vanishes outside `O`. -/
theorem aux_prop_boundary_modV_vanish {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω) (φ : 𝓓(Ω, ℝ)) (ψ : S.space)
    (psic : SpatialCoordinates d → ℝ)
    (hψc : ((ψ : SobolevData Ω).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] psic)
    (O : Set (SpatialCoordinates d))
    (hvan : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), x ∉ O → psic x = 0) :
    (∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      x ∉ closure O → (aux_prop_locality_recovery_modV S hS φ ψ : SobolevData Ω).1 x = 0) ∧
    (∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      x ∉ closure O → (aux_prop_locality_recovery_modV S hS φ ψ : SobolevData Ω).2 i x = 0) := by
  have hΩ := ae_restrict_mem (μ := volume) Ω.isOpen.measurableSet
  have hzero : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      x ∈ (closure O)ᶜ → (ψ : SobolevData Ω).1 x = 0 := by
    filter_upwards [hψc, hΩ] with x h1 h2 hx
    rw [h1]
    exact hvan x h2 (fun h => hx (subset_closure h))
  refine ⟨?_, fun i => ?_⟩
  · filter_upwards [aux_prop_locality_recovery_modV_fst_ae S hS φ ψ, hzero] with x h1 h2 hx
    rw [h1, h2 hx, mul_zero]
  · have hg := aux_prop_locality_recovery_grad_ae_zero_of_const (ψ : SobolevData Ω)
      (S.le_weak ψ.2) (closure O)ᶜ isClosed_closure.isOpen_compl 0 hzero i
    rw [aux_prop_locality_recovery_modV_grad]
    filter_upwards [Lp.coeFn_add
        (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ i)
          (ψ : SobolevData Ω).1)
        (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ)
          ((ψ : SobolevData Ω).2 i)),
      aux_prop_locality_recovery_modV_P_ae φ (ψ : SobolevData Ω) i,
      aux_prop_locality_recovery_modV_R_ae φ (ψ : SobolevData Ω) i, hzero, hg]
      with x h0 h1 h2 h3 h4 hx
    rw [h0, Pi.add_apply, h1, h2, h3 hx, h4 hx]
    ring

/-- `aux_prop_locality_recovery_side` for an arbitrary lower-semicontinuous limit energy
(here the Mosco limit `E^Q` of `prop_killed_inverse`). -/
theorem aux_prop_boundary_side {d : ℕ} (hd : 2 ≤ d) (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (Efun : DomainL2 (centeredCube z r hr) → EReal)
    (hLower : ∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      Efun w ≤ liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n) (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (cut : ℕ → S.space) (B : ℝ) (hB : 0 ≤ B)
    (hcutE : ∀ n, responseForm S (a n) (cut n) (cut n) ≤ B)
    (hgrowth : ∀ n, ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((cut n).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))
    (w : DomainL2 (centeredCube z r hr)) (hw0 : 0 ≤ Efun w) (hw : Efun w < ⊤)
    (Φ : ℕ → S.space) (hΦ1 : Tendsto (fun n => (Φ n).val.1) atTop (𝓝 w))
    (hΦE : Tendsto (fun n => responseForm S (a n) (Φ n) (Φ n)) atTop (𝓝 (Efun w).toReal))
    (Y : ℕ → S.space) (P R : ℕ → Fin d → DomainL2 (centeredCube z r hr))
    (hY : ∀ n i, (Y n).val.2 i = P n i + R n i)
    (hP : ∀ n i, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      |P n i x| ≤ |(Φ n).val.2 i x|)
    (hR : ∀ n i, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (R n i x) ^ 2 = ((Φ n).val.1 x - w x) ^ 2 * ((cut n).val.2 i x) ^ 2)
    (hL2 : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      |(Y n).val.1 x - w x| ≤ |(Φ n).val.1 x - w x|) :
    Tendsto (fun n => ((Y n).val.1,
      ((responseForm S (a n) (Y n) (Y n) : ℝ) : EReal))) atTop (𝓝 (w, Efun w)) := by
  obtain ⟨Eb, hEb⟩ := hΦE.bddAbove_range
  have hEb' : ∀ n, responseForm S (a n) (Φ n) (Φ n) ≤ Eb := fun n => hEb ⟨n, rfl⟩
  have hT := aux_prop_locality_recovery_trace_tendsto hd hInterp z r hr t ht S a KN hKN Kstar
    hKstar hfrac hcoercive cut B hB hcutE hgrowth Φ w hΦ1 Eb hEb'
  refine aux_prop_locality_recovery_recovery_abstract (fun n => (Y n).val.1)
    (fun n => (Φ n).val.1) w (Efun w) hw0 hw
    (fun n => responseForm S (a n) (Y n) (Y n)) (fun n => responseForm S (a n) (Φ n) (Φ n))
    (fun n => (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((a n).val x * ∑ i : Fin d, ((cut n).val.2 i x) ^ 2) *
        ENNReal.ofReal (((Φ n).val.1 x - w x) ^ 2)).toReal)
    (fun h => hLower Y w (fun f => tendsto_const_nhds.inner h)) hΦ1 hΦE
    (fun n => ?_) (fun n ε hε => ?_) hT
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (Y n).val.1 w, Lp.coeFn_sub (Φ n).val.1 w, hL2 n]
      with x h1 h2 h3
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
    exact h3
  · exact aux_prop_locality_recovery_energy_split S (a n) (Y n) (Φ n) (P n) (R n)
      (fun i => (cut n).val.2 i) (fun x => (Φ n).val.1 x - w x) (hY n) (hP n) (hR n) hε

/-- E4: a recovery sequence of a core function supported in an open set `W` can be chosen
with all its terms carried by one compact subset of `W` (localization by catalog cutoffs,
as in the proof of Proposition `prop_locality`). -/
theorem aux_prop_boundary_local_recovery {d : ℕ} (hd : 2 ≤ d)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (Efun : DomainL2 (centeredCube z r hr) → EReal)
    (hLower : ∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      Efun w ≤ liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n) (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n)
            (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))]
              chic n ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
            x ∉ O → chic n x = 0) ∧
          responseForm S (a n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a n).val y *
                ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (W : Set (SpatialCoordinates d)) (hW : IsOpen W)
    (w : DomainL2 (centeredCube z r hr)) (hw0 : 0 ≤ Efun w) (hwE : Efun w < ⊤)
    (wN : ℕ → S.space)
    (hwN : Tendsto (fun n => ((wN n).val.1,
      ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop (𝓝 (w, Efun w)))
    (f : SpatialCoordinates d → ℝ) (hfcs : HasCompactSupport f) (hfW : tsupport f ⊆ W)
    (hfQ : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hwf : (w : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f) :
    ∃ (vN : ℕ → S.space) (Kc : Set (SpatialCoordinates d)), IsCompact Kc ∧ Kc ⊆ W ∧
      Kc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      Tendsto (fun n => ((vN n).val.1,
        ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop (𝓝 (w, Efun w)) ∧
      ∀ n, (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
          x ∉ Kc → (vN n).val.1 x = 0) ∧
        ∀ i, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
          x ∉ Kc → (vN n).val.2 i x = 0 := by
  have hob1 := aux_prop_locality_recovery_nested_sets (tsupport f) W
    (centeredCube z r hr : Set (SpatialCoordinates d)) hfcs.isCompact hW
    (centeredCube z r hr).isOpen hfW hfQ
  obtain ⟨O₁, O₂, hO₁, hO₂, hKO₁, hO₁c, hO₁O₂, hO₂WQ⟩ := hob1
  have hO₁WQ : closure O₁ ⊆ W ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    fun x hx => hO₂WQ (subset_closure (hO₁O₂ hx))
  have hob2 := hcutoffs (tsupport f) O₁ hfcs.isCompact hO₁ hKO₁ (fun x hx => (hO₁WQ hx).2)
  obtain ⟨V₁, psi, psic, B₁, hV₁, hKV₁, -, hB₁, hpsi⟩ := hob2
  have hob6 := aux_prop_locality_recovery_recovery_parts _ _ _ _ hw0 hwE hwN
  obtain ⟨hwN1, hwNE⟩ := hob6
  have hob9 := aux_prop_locality_recovery_smooth_seq S hS a wN w _ hwN1 hwNE
  obtain ⟨φ', Φ', hΦ'v, hΦ'1, hΦ'E⟩ := hob9
  have hin := fun n => aux_prop_locality_recovery_inner_ae (psi n).val (S.le_weak (psi n).2)
    (psic n) (hpsi n).2.1 (hpsi n).2.2.1 V₁ hV₁ (hpsi n).2.2.2.1 w f hwf hKV₁
  refine ⟨fun n => aux_prop_locality_recovery_modV S hS (φ' n) (psi n), closure O₁, hO₁c,
    fun x hx => (hO₁WQ hx).1, fun x hx => (hO₁WQ hx).2, ?_, fun n => ?_⟩
  · have hprops := fun n => aux_prop_locality_recovery_modV_props S hS (φ' n) (Φ' n) (hΦ'v n)
      (psi n) w (hin n).1 (hin n).2.1 (hin n).2.2
    exact aux_prop_boundary_side hd hInterp z r hr t ht S a Efun hLower KN hKN Kstar hKstar
      hfrac hcoercive psi B₁ hB₁ (fun n => (hpsi n).2.2.2.2.2.1) (fun n => (hpsi n).2.2.2.2.2.2)
      w hw0 hwE Φ' hΦ'1 hΦ'E (fun n => aux_prop_locality_recovery_modV S hS (φ' n) (psi n))
      (fun n i => aux_prop_locality_recovery_mulL
        (aux_prop_locality_recovery_testPartialLinf (φ' n) i) (psi n).val.1)
      (fun n i => aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf (φ' n))
        ((psi n).val.2 i))
      (fun n i => aux_prop_locality_recovery_modV_grad S hS (φ' n) (psi n) i)
      (fun n => (hprops n).1) (fun n => (hprops n).2.1) (fun n => (hprops n).2.2)
  · exact aux_prop_boundary_modV_vanish S hS (φ' n) (psi n) (psic n) (hpsi n).2.1 O₁
      (hpsi n).2.2.2.2.1




/-! ### The Dirichlet identity `Λ_{N,q}(b) = Γ_N(U_N)(q)`. -/

theorem aux_prop_boundary_harm_transport {d : ℕ} (a : SpatialCoordinates d → ℝ)
    (U V V' : Set (SpatialCoordinates d)) (u : H1Function U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hV' : IsOpen V') (hV'U : V' ⊆ U) (h : V = V')
    (hh : IsWeaklyHarmonicOn a V (u.restrict hV hVU)) :
    IsWeaklyHarmonicOn a V' (u.restrict hV' hV'U) := by
  subst h; exact hh

theorem aux_prop_boundary_trace_transport {d : ℕ}
    (U V V' : Set (SpatialCoordinates d)) (u b : H1Function U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hV' : IsOpen V') (hV'U : V' ⊆ U) (h : V = V')
    (hh : HasZeroTraceDifferenceOn V (u.restrict hV hVU) (b.restrict hV hVU)) :
    HasZeroTraceDifferenceOn V' (u.restrict hV' hV'U) (b.restrict hV' hV'U) := by
  subst h; exact hh

/-- Rebasing a zero-trace difference to a datum carrier with the same function values. -/
theorem aux_prop_boundary_trace_rebase {d : ℕ} (W : Set (SpatialCoordinates d)) (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) (w b b' : H1Function W) (hbb' : b.toFun = b'.toFun)
    (h : HasZeroTraceDifferenceOn W w b) : HasZeroTraceDifferenceOn W w b' := by
  obtain ⟨w10, hfun, hgrad⟩ := h
  have hgae : b.grad =ᵐ[volume.restrict W] b'.grad :=
    lane2_grad_ae_eq_of_ae_eq' hW hWb b b' (Filter.EventuallyEq.of_eq hbb')
  have hv : (fun x => w.toFun x - b'.toFun x) =ᵐ[volume.restrict W] w10.toH1Function.toFun :=
    Filter.Eventually.of_forall fun x => by
      simp only
      rw [hfun x, hbb']; ring
  have hg : ∀ i : Fin d, (fun x => (fun y => w.grad y - b'.grad y) x i)
      =ᵐ[volume.restrict W] fun x => w10.toH1Function.grad x i := by
    intro i
    filter_upwards [hgae] with x hx
    simp only [Pi.sub_apply]
    rw [hgrad x, ← hx, Pi.add_apply]; ring
  refine ⟨lane2_H10ofAEEq2 w10 _ _ hv hg, fun x => ?_, fun x => ?_⟩
  · show w.toFun x = b'.toFun x + (w.toFun x - b'.toFun x)
    ring
  · show w.grad x = b'.grad x + (w.grad x - b'.grad x)
    abel

/-- Ellipticity on a sub-box of the continuous coefficient. -/
theorem aux_prop_boundary_elliptic {d : ℕ} (W K : Set (SpatialCoordinates d))
    (hW : MeasurableSet W) (hWK : W ⊆ K) (a : SpatialCoordinates d → ℝ) (ha : ContinuousOn a K)
    (lam Lam : ℝ) (hlam : 0 < lam) (hb : ∀ x ∈ K, lam ≤ a x ∧ a x ≤ Lam) :
    IsEllipticFieldOn lam Lam W (scalarCoeffField a) := by
  classical
  refine ⟨?_, fun x hx =>
    (isEllipticMatrix_scalarMatrix
      (lt_of_lt_of_le hlam (hb x (hWK hx)).1)).mono hlam (hb x (hWK hx)).1 (hb x (hWK hx)).2⟩
  have hm : Measurable (W.piecewise a (fun _ => (0 : ℝ))) :=
    (ha.mono hWK).measurable_piecewise continuousOn_const hW
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  by_cases hij : i = j
  · subst hij
    have he : (fun x => if x ∈ W then scalarCoeffField a x i i else 0)
        = W.piecewise a (fun _ => (0 : ℝ)) := by
      funext x
      by_cases hx : x ∈ W <;> simp [hx, scalarCoeffField, scalarMatrix, Set.piecewise]
    rw [he]
    exact hm
  · have he : (fun x => if x ∈ W then scalarCoeffField a x i j else 0)
        = fun _ => (0 : ℝ) := by
      funext x
      by_cases hx : x ∈ W <;> simp [hx, scalarCoeffField, scalarMatrix, hij]
    rw [he]
    exact measurable_const

/-- F1 (energy side): the cell energy of `U_N` is the mass its energy measure gives the cell. -/
theorem aux_prop_boundary_energy_eq_mass {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (W : Set (SpatialCoordinates d)) (hW : IsOpen W) (hWQ : W ⊆ (Q : Set (SpatialCoordinates d)))
    (S : ResponseSpace Q) (a : SpatialCoordinates d → ℝ) (aC : PositiveCoefficient Q)
    (haC : ((aC).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] a)
    (ha0 : ∀ x ∈ W, 0 ≤ a x)
    (U : H1Function (Q : Set (SpatialCoordinates d))) (US : S.space)
    (hrep : (US : SobolevData Q) = sobolevDataOfH1 U) :
    energy a W (U.restrict hW hWQ) =
      (((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((aC).val y *
          ∑ i : Fin d, ((US : SobolevData Q).2 i y) ^ 2))) W).toReal := by
  have hWm : MeasurableSet W := hW.measurableSet
  have hsub : volume.restrict W ≤ volume.restrict (Q : Set (SpatialCoordinates d)) :=
    Measure.restrict_mono hWQ le_rfl
  have hgrad : ∀ i, ((US : SobolevData Q).2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fun x => U.grad x i := by
    intro i
    rw [hrep]
    exact sobolevDataOfH1_snd_coeFn U i
  have hall : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ∀ i, ((US : SobolevData Q).2 i : SpatialCoordinates d → ℝ) x = U.grad x i :=
    ae_all_iff.2 hgrad
  have heq : (fun x => a x * vecDot ((U.restrict hW hWQ).grad x) ((U.restrict hW hWQ).grad x))
      =ᵐ[volume.restrict W] fun x => (aC).val x *
        ∑ i : Fin d, ((US : SobolevData Q).2 i x) ^ 2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hWQ haC, ae_restrict_of_ae_restrict_of_subset hWQ hall] with x h1 h2
    rw [h1]
    change a x * vecDot (U.grad x) (U.grad x) = _
    simp only [vecDot, h2, sq]
  have hmeas : AEStronglyMeasurable (fun x => (aC).val x *
      ∑ i : Fin d, ((US : SobolevData Q).2 i x) ^ 2) (volume.restrict W) :=
    ((Lp.stronglyMeasurable (aC).val).measurable.mul (Finset.measurable_sum _ fun i _ =>
      (Lp.stronglyMeasurable ((US : SobolevData Q).2 i)).measurable.pow_const 2)).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume.restrict W] fun x => a x * vecDot ((U.restrict hW hWQ).grad x)
      ((U.restrict hW hWQ).grad x) := by
    filter_upwards [ae_restrict_mem hWm] with x hx
    refine mul_nonneg (ha0 x hx) ?_
    simp only [vecDot]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  unfold energy
  rw [integral_eq_lintegral_of_nonneg_ae hnn (hmeas.congr heq.symm),
    withDensity_apply _ hWm, Measure.restrict_restrict hWm, inter_eq_left.2 hWQ]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [heq] with x hx
  rw [hx]

/-- F1: the cell Dirichlet infimum of the datum is the mass of the cell under the energy
measure of `U_N` (Dirichlet principle for the harmonic `U_N` on the centre cell). -/
theorem aux_prop_boundary_dirichlet_identity {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hacont : ∀ n : ℕ, ContinuousOn (a n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ a n x ∧ a n x ≤ Lam)
    (beta : SpatialCoordinates d → ℝ)
    (betaQ : H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hbetaQfun : betaQ.toFun = beta)
    (betaq : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hbetaqfun : betaq.toFun = beta)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNharm : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      IsWeaklyHarmonicOn (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (hUNtrace : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      HasZeroTraceDifferenceOn
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k))
        (betaQ.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (n : ℕ) :
    cellDirichletInfimum (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) betaq =
      (((volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((aC n).val y *
          ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  have : NeZero d := ⟨by omega⟩
  let k0 : OddGridIndex d (triadicHalf 1) := fun _ => ⟨triadicHalf 1, by simp [triadicHalf]⟩
  have hcell : (oddGridCell z (3 * r) h3r (triadicHalf 1) k0 : Set (SpatialCoordinates d)) =
      centeredCube z r hr := aux_prop_boundary_center_cell z r hr h3r
  have hqo : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen
  have hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) := by
    show Metric.ball z (r / 2) ⊆ Metric.ball z (3 * r / 2)
    exact Metric.ball_subset_ball (by linarith)
  have hharm := aux_prop_boundary_harm_transport (a n) _ _ _ (UN n) _ (hcellsub k0) hqo hqQ hcell
    (hUNharm n k0)
  have htr0 := aux_prop_boundary_trace_transport _ _ _ (UN n) betaQ _ (hcellsub k0) hqo hqQ hcell
    (hUNtrace n k0)
  have htr := aux_prop_boundary_trace_rebase _ hqo (centeredCube_isBounded z hr) _ _ betaq
    (by change betaQ.toFun = betaq.toFun; rw [hbetaQfun, hbetaqfun]) htr0
  obtain ⟨lam, Lam, hlam, hb⟩ := hell n
  have hEll : IsEllipticFieldOn lam Lam (centeredCube z r hr : Set (SpatialCoordinates d))
      (scalarCoeffField (a n)) :=
    aux_prop_boundary_elliptic _ _ hqo.measurableSet (hqQ.trans subset_closure) (a n) (hacont n)
      lam Lam hlam hb
  have hne : (centeredCube z r hr : Set (SpatialCoordinates d)).Nonempty :=
    ⟨z, by rw [centeredCube_coe_eq_ball]; exact Metric.mem_ball_self (by linarith)⟩
  have hDP := energy_eq_sInf_sameTrace_of_isWeaklyHarmonicOn
    (lane2_isOpenBoundedConvexDomain_centeredCube z hr) hne hEll hharm htr
  have hid : cellDirichletInfimum (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) betaq =
      energy (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) ((UN n).restrict hqo hqQ) :=
    hDP.symm
  rw [hid]
  exact aux_prop_boundary_energy_eq_mass _ _ hqo hqQ S (a n) (aC n) (haC n)
    (fun x hx => hlam.le.trans (hb x (subset_closure (hqQ hx))).1) (UN n) (UNS n) (hUNrep n)




/-- The response form as one integral (the left side of `cor_energy_measures`(c) at `φ ≡ 1`). -/
theorem aux_prop_boundary_resp_integral {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (A : PositiveCoefficient Ω) (u v : S.space) :
    (∫ x in (Ω : Set (SpatialCoordinates d)),
      (fun _ : SpatialCoordinates d => (1 : ℝ)) x * (A.val x *
        ∑ i : Fin d, ((u : SobolevData Ω).2 i x) * ((v : SobolevData Ω).2 i x))) =
      responseForm S A u v := by
  rw [responseForm_apply, ← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards with x
    simp only [one_mul, Finset.mul_sum]
  · intro i _
    refine (integrable_weighted_inner A.val ((u : SobolevData Ω).2 i)
      ((v : SobolevData Ω).2 i)).congr ?_
    filter_upwards with x
    simp only [RCLike.inner_apply, conj_trivial]
    ring

/-- E (conjunct 7 on the core): `E^Q(U, φ) = 0` for every core
function `φ` supported in `q`.  A localized recovery `φ_N` of `φ` is carried by a compact
subset of `q`, where `U_N` is harmonic, so `E_N(U_N, φ_N) = 0`; Corollary
`cor_energy_measures`(c) tested with `1` passes this to the limit. -/
theorem aux_prop_boundary_harmonic_core {d : ℕ} (hd : 2 ≤ d)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hacont : ∀ n : ℕ, ContinuousOn (a n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (uBar : DomainL2 (centeredCube z (3 * r) h3r))
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNharm : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      IsWeaklyHarmonicOn (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (hLower : ∀ (vn : ℕ → S.space)
      (v : DomainL2 (centeredCube z (3 * r) h3r)),
      (∀ f : DomainL2 (centeredCube z (3 * r) h3r),
        Tendsto (fun n => inner ℝ f (vn n).val.1) atTop
          (𝓝 (inner ℝ f v))) →
      EQ.toClosedForm.energy v ≤
        Filter.liminf (fun n =>
          (responseForm S (aC n) (vn n) (vn n) : EReal)) atTop)
    (hRecovery : ∀ v ∈ EQ.toClosedForm.domain, ∃ vn : ℕ → S.space,
      Tendsto (fun n => ((vn n).val.1,
        (responseForm S (aC n) (vn n) (vn n) : EReal))) atTop
        (𝓝 (v, EQ.toClosedForm.energy v)))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 +
          volume.real (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) *
            ((cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
              (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        KN n * responseForm S (aC n) w w)
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n)
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
              chic n ∧
          (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            x ∉ O → chic n x = 0) ∧
          responseForm S (aC n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y *
                ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (hC : ∀ (u v : DomainL2 (centeredCube z (3 * r) h3r))
          (uN vN : ℕ → S.space) (E0 : ℝ),
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        v ∈ EQ.toClosedForm.domain →
        Tendsto (fun n => ((vN n).val.1,
          (responseForm S (aC n) (vN n) (vN n) : EReal))) atTop
          (𝓝 (v, EQ.toClosedForm.energy v)) →
        ∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x in (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
              φ x * ((aC n).val x *
                ∑ i : Fin d,
                  ((uN n : SobolevData (centeredCube z (3 * r) h3r)).2 i x) *
                  ((vN n : SobolevData (centeredCube z (3 * r) h3r)).2 i x))) atTop
            (𝓝 (_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ)))
    (E0 : ℝ) (hE0 : ∀ n : ℕ, responseForm S (aC n) (UNS n) (UNS n) ≤ E0)
    (hdom : uBar ∈ EQ.toClosedForm.domain) :
    ∀ w : DomainL2 (centeredCube z (3 * r) h3r),
      EQ.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) w →
        EQ.form uBar w = 0 := by
  intro w hw
  have hw' := hw.2
  obtain ⟨f, -, hfcs, hfq, hwf⟩ := hw'
  have hqo : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen
  have hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) := by
    show Metric.ball z (r / 2) ⊆ Metric.ball z (3 * r / 2)
    exact Metric.ball_subset_ball (by linarith)
  have hwE : EQ.toClosedForm.energy w < ⊤ := by
    rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_mem _ hw.1]
    exact EReal.coe_lt_top _
  have hrec := hRecovery w hw.1
  obtain ⟨wN, hwN⟩ := hrec
  have hloc := aux_prop_boundary_local_recovery hd hInterp z (3 * r) h3r t ht S hS aC
    EQ.toClosedForm.energy hLower KN hKN Kstar hKstar hfrac hcoercive hcutoffs _ hqo w
    (_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_nonneg _ w) hwE wN hwN f hfcs hfq (hfq.trans hqQ) hwf
  obtain ⟨vN, Kc, hKc, hKq, hKQ, hvN, hvan⟩ := hloc
  let k0 : OddGridIndex d (triadicHalf 1) := fun _ => ⟨triadicHalf 1, by simp [triadicHalf]⟩
  have hcell : (oddGridCell z (3 * r) h3r (triadicHalf 1) k0 : Set (SpatialCoordinates d)) =
      centeredCube z r hr := aux_prop_boundary_center_cell z r hr h3r
  have hzero : ∀ n, responseForm S (aC n) (UNS n) (vN n) = 0 := by
    intro n
    refine aux_prop_boundary_orth_supported S hS (aC n) (UNS n) _ hqo ?_ Kc hKc hKq hKQ (vN n)
      (hvan n).1 (hvan n).2
    intro ζ hζS hζ
    exact aux_prop_boundary_orth_smooth z r h3r S a aC hacont haC UN UNS hUNrep _
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k0).isOpen (hcellsub k0) n (hUNharm n k0) ζ
      (hcell ▸ hζ) hζS
  have hlim := hC uBar w UNS vN E0 hUNL2 hE0 hw.1 hvN (fun _ => 1) continuousOn_const
  have hlim' : Tendsto (fun n => responseForm S (aC n) (UNS n) (vN n)) atTop
      (𝓝 (_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross uBar w) Set.univ (fun _ => 1))) :=
    hlim.congr fun n => aux_prop_boundary_resp_integral S (aC n) (UNS n) (vN n)
  have hlim0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (𝓝 (_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross uBar w) Set.univ (fun _ => 1))) :=
    hlim'.congr hzero
  have hval := tendsto_nhds_unique hlim0 tendsto_const_nhds
  rw [aux_prop_boundary_signedIntegralOn_one, Gamma.cross_univ uBar hdom w hw.1] at hval
  exact hval




/-- Conjunct 6 (zero face mass): any weak cluster `ν` of the
energy measures of `U_N` dominates `Γ(Ū)` and, by the ball growth, charges no face. -/
theorem aux_prop_boundary_face_zero {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (UNS : ℕ → S.space)
    (uBar : DomainL2 (centeredCube z (3 * r) h3r))
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (Bcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hBcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Bcell k)
    (hCellGrowth : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y *
            ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t))
    (E0 : ℝ) (hE0 : ∀ n : ℕ, responseForm S (aC n) (UNS n) (UNS n) ≤ E0)
    (hB : ∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
          (uN : ℕ → S.space) (E0 : ℝ)
          (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
        nu Set.univ < (⊤ : ENNReal) →
        nu ((closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))ᶜ) = 0 →
        StrictMono sigma →
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        (∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC (sigma n)).val y *
                ∑ i : Fin d, ((uN (sigma n) : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂nu))) →
        u ∈ EQ.toClosedForm.domain ∧
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            Gamma.measure u B ≤ nu B)
    (hr : 0 < r) :
    Gamma.measure uBar (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 := by
  have hcl := aux_prop_boundary_cluster hd z r h3r EQ Gamma S aC UNS uBar hUNL2 t ht htd Bcell
    hBcell hCellGrowth E0 hE0 hB id strictMono_id
  obtain ⟨ν, σ, -, -, -, -, hΓν, hνf⟩ := hcl
  exact le_antisymm ((hΓν _ isClosed_frontier.measurableSet).trans (hνf z r hr).le) (zero_le)

/-- F2 (lower bound): `liminf Λ_{N,q}(b) ≥ Γ(Ū)(q)`, since every
subsequence has a weak cluster `ν ≥ Γ(Ū)` and `q` is open. -/
theorem aux_prop_boundary_lower {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (UNS : ℕ → S.space)
    (uBar : DomainL2 (centeredCube z (3 * r) h3r))
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (Bcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hBcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Bcell k)
    (hCellGrowth : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y *
            ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t))
    (E0 : ℝ) (hE0 : ∀ n : ℕ, responseForm S (aC n) (UNS n) (UNS n) ≤ E0)
    (hB : ∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
          (uN : ℕ → S.space) (E0 : ℝ)
          (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
        nu Set.univ < (⊤ : ENNReal) →
        nu ((closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))ᶜ) = 0 →
        StrictMono sigma →
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        (∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC (sigma n)).val y *
                ∑ i : Fin d, ((uN (sigma n) : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂nu))) →
        u ∈ EQ.toClosedForm.domain ∧
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            Gamma.measure u B ≤ nu B)
    (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, (Gamma.measure uBar (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
      - δ < (((volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((aC n).val y *
          ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hcon' := hcon.mono fun n hn => not_lt.1 hn
  obtain ⟨σ0, hσ0, hle⟩ := extraction_of_frequently_atTop hcon'
  have hcl := aux_prop_boundary_cluster hd z r h3r EQ Gamma S aC UNS uBar hUNL2 t ht htd Bcell
    hBcell hCellGrowth E0 hE0 hB σ0 hσ0
  obtain ⟨ν, σ, -, hνfin, -, hconv, hΓν, -⟩ := hcl
  have hG : 0 ≤ (Gamma.measure uBar (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
      - δ := ENNReal.toReal_nonneg.trans (hle 0)
  have hmass : ∀ n, ((volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((aC n).val y *
          ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
        Set.univ < ⊤ := fun n => by
    rw [aux_prop_boundary_mass_univ S (aC n) (UNS n)]
    exact ENNReal.ofReal_lt_top
  have hνq := aux_prop_boundary_open_le _ _ ν (fun n => hmass (σ0 (σ n))) hνfin hconv _
    (centeredCube z r hr).isOpen _
    (fun n => (ENNReal.le_ofReal_iff_toReal_le
      ((measure_mono (subset_univ _)).trans_lt (hmass _)).ne hG).2 (hle (σ n)))
  have hΓq := hΓν _ (centeredCube z r hr).isOpen.measurableSet
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hΓq.trans hνq)
  rw [ENNReal.toReal_ofReal hG] at h
  linarith

theorem aux_prop_boundary_grad_add {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (U Y : S.space) (i : Fin d) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ((U + Y : S.space) : SobolevData Q).2 i x =
        (U : SobolevData Q).2 i x + (Y : SobolevData Q).2 i x := by
  have h : ((U + Y : S.space) : SobolevData Q).2 i =
      (U : SobolevData Q).2 i + (Y : SobolevData Q).2 i := rfl
  rw [h]
  exact Lp.coeFn_add _ _

theorem aux_prop_boundary_grad_sub {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (U Y : S.space) (i : Fin d) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ((U - Y : S.space) : SobolevData Q).2 i x =
        (U : SobolevData Q).2 i x - (Y : SobolevData Q).2 i x := by
  have h : ((U - Y : S.space) : SobolevData Q).2 i =
      (U : SobolevData Q).2 i - (Y : SobolevData Q).2 i := rfl
  rw [h]
  exact Lp.coeFn_sub _ _

theorem aux_prop_boundary_fst_sub {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (U Y : S.space) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ((U - Y : S.space) : SobolevData Q).1 x =
        (U : SobolevData Q).1 x - (Y : SobolevData Q).1 x := by
  have h : ((U - Y : S.space) : SobolevData Q).1 =
      (U : SobolevData Q).1 - (Y : SobolevData Q).1 := rfl
  rw [h]
  exact Lp.coeFn_sub _ _

/-- Upper-bound competitor : adding a perturbation carried by `q` and
orthogonal to `U` does not decrease the energy `U` places on `q`. -/
theorem aux_prop_boundary_competitor {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (A : PositiveCoefficient Q) (U Y : S.space)
    (q : Set (SpatialCoordinates d)) (hq : MeasurableSet q)
    (horth : responseForm S A U Y = 0)
    (hYoff : ∀ i, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ q → (Y : SobolevData Q).2 i x = 0) :
    ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((U : SobolevData Q).2 i y) ^ 2))) q ≤
    ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y *
        ∑ i : Fin d, (((U + Y : S.space) : SobolevData Q).2 i y) ^ 2))) q := by
  have hE : responseForm S A U U ≤ responseForm S A (U + Y) (U + Y) := by
    have h1 := responseForm_nonneg S A Y
    have h2 := responseForm_symm S A Y U
    simp only [map_add, add_apply]
    linarith
  have hU := aux_prop_boundary_mass_univ S A U
  have hV := aux_prop_boundary_mass_univ S A (U + Y)
  have hcomp : ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((U : SobolevData Q).2 i y) ^ 2))) qᶜ =
    ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y *
        ∑ i : Fin d, (((U + Y : S.space) : SobolevData Q).2 i y) ^ 2))) qᶜ := by
    rw [withDensity_apply _ hq.compl, withDensity_apply _ hq.compl]
    apply lintegral_congr_ae
    have hall : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), ∀ i,
        (x ∉ q → (Y : SobolevData Q).2 i x = 0) ∧
        ((U + Y : S.space) : SobolevData Q).2 i x =
          (U : SobolevData Q).2 i x + (Y : SobolevData Q).2 i x :=
      ae_all_iff.2 fun i => (hYoff i).and (aux_prop_boundary_grad_add S U Y i)
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem hq.compl] with x hx hxq
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hx i).2, (hx i).1 hxq, add_zero]
  have hfin : ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((U : SobolevData Q).2 i y) ^ 2))) qᶜ
        ≠ ⊤ := by
    refine ((measure_mono (subset_univ _)).trans_lt ?_).ne
    rw [hU]; exact ENNReal.ofReal_lt_top
  refine ENNReal.le_of_add_le_add_right hfin ?_
  calc _ = ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((U : SobolevData Q).2 i y) ^ 2)))
        Set.univ := measure_add_measure_compl hq
    _ ≤ ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y *
        ∑ i : Fin d, (((U + Y : S.space) : SobolevData Q).2 i y) ^ 2))) Set.univ := by
      rw [hU, hV]; exact ENNReal.ofReal_le_ofReal hE
    _ = _ := by rw [hcomp]; exact (measure_add_measure_compl hq).symm

/-- Young and convexity for one coordinate of the competitor gradient. -/
theorem aux_prop_boundary_young_real (c χ C P ε u φ θd e g : ℝ) (hc : 0 ≤ c)
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hC : 1 - χ ≤ C) (hP : χ ≤ P) (hε : 0 < ε) :
    c * ((1 - χ) * u + χ * φ + (χ * θd + e * g)) ^ 2 ≤
      (1 + ε) * (C * (c * u ^ 2) + P * (c * φ ^ 2)) +
        2 * (1 + ε⁻¹) * (c * θd ^ 2 + c * g ^ 2 * e ^ 2) := by
  set A := (1 - χ) * u + χ * φ with hAdef
  set B := χ * θd + e * g with hBdef
  have hy : 0 ≤ ε⁻¹ * (ε * A - B) ^ 2 := by positivity
  have key : ε⁻¹ * (ε * A - B) ^ 2 = ε * A ^ 2 - 2 * A * B + ε⁻¹ * B ^ 2 := by
    field_simp
    ring
  have h1 : (A + B) ^ 2 ≤ (1 + ε) * A ^ 2 + (1 + ε⁻¹) * B ^ 2 := by nlinarith [key, hy]
  have hconv : (1 - χ) * u ^ 2 + χ * φ ^ 2 - A ^ 2 = χ * (1 - χ) * (u - φ) ^ 2 := by
    rw [hAdef]; ring
  have hcv : 0 ≤ χ * (1 - χ) * (u - φ) ^ 2 :=
    mul_nonneg (mul_nonneg hχ0 (by linarith)) (sq_nonneg _)
  have h3 : (1 - χ) * u ^ 2 ≤ C * u ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg u)
  have h4 : χ * φ ^ 2 ≤ P * φ ^ 2 := mul_le_mul_of_nonneg_right hP (sq_nonneg φ)
  have hA : A ^ 2 ≤ C * u ^ 2 + P * φ ^ 2 := by linarith
  have hχsq : χ ^ 2 ≤ 1 := by nlinarith
  have h5 : (χ * θd) ^ 2 ≤ θd ^ 2 := by
    rw [mul_pow]; exact mul_le_of_le_one_left (sq_nonneg _) hχsq
  have hB : B ^ 2 ≤ 2 * θd ^ 2 + 2 * (g ^ 2 * e ^ 2) := by
    have := sq_nonneg (χ * θd - e * g)
    rw [hBdef]
    nlinarith [h5]
  have hε1 : 0 ≤ 1 + ε := by linarith
  have hε2 : 0 ≤ 1 + ε⁻¹ := by positivity
  calc c * (A + B) ^ 2 ≤ c * ((1 + ε) * A ^ 2 + (1 + ε⁻¹) * B ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ ≤ c * ((1 + ε) * (C * u ^ 2 + P * φ ^ 2) +
          (1 + ε⁻¹) * (2 * θd ^ 2 + 2 * (g ^ 2 * e ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact add_le_add (mul_le_mul_of_nonneg_left hA hε1) (mul_le_mul_of_nonneg_left hB hε2)
    _ = _ := by ring

/-- The summed pointwise bound, in the extended form used under the integral. -/
theorem aux_prop_boundary_young_enn {d : ℕ} (c χ C P ε e : ℝ) (u φ θd g : Fin d → ℝ)
    (hc : 0 ≤ c) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hC : 1 - χ ≤ C) (hC0 : 0 ≤ C) (hP : χ ≤ P)
    (hP0 : 0 ≤ P) (hε : 0 < ε) :
    ENNReal.ofReal (c * ∑ i, ((1 - χ) * u i + χ * φ i + (χ * θd i + e * g i)) ^ 2) ≤
      ENNReal.ofReal (1 + ε) * (ENNReal.ofReal (C * (c * ∑ i, u i ^ 2)) +
          ENNReal.ofReal P * ENNReal.ofReal (c * ∑ i, φ i ^ 2)) +
        ENNReal.ofReal (2 * (1 + ε⁻¹)) * (ENNReal.ofReal (c * ∑ i, θd i ^ 2) +
          ENNReal.ofReal (c * ∑ i, g i ^ 2) * ENNReal.ofReal (e ^ 2)) := by
  have hs : ∀ f : Fin d → ℝ, 0 ≤ c * ∑ i, f i ^ 2 :=
    fun f => mul_nonneg hc (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [← ENNReal.ofReal_mul hP0, ← ENNReal.ofReal_add (mul_nonneg hC0 (hs u))
      (mul_nonneg hP0 (hs φ)), ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_mul (hs g), ← ENNReal.ofReal_add (hs θd) (mul_nonneg (hs g) (sq_nonneg _)),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg (by linarith) (add_nonneg (mul_nonneg hC0 (hs u))
      (mul_nonneg hP0 (hs φ)))) (mul_nonneg (by positivity)
        (add_nonneg (hs θd) (mul_nonneg (hs g) (sq_nonneg _))))]
  apply ENNReal.ofReal_le_ofReal
  have hsum : c * ∑ i, ((1 - χ) * u i + χ * φ i + (χ * θd i + e * g i)) ^ 2 ≤
      ∑ i, ((1 + ε) * (C * (c * u i ^ 2) + P * (c * φ i ^ 2)) +
        2 * (1 + ε⁻¹) * (c * θd i ^ 2 + c * g i ^ 2 * e ^ 2)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      aux_prop_boundary_young_real c χ C P ε (u i) (φ i) (θd i) e (g i) hc hχ0 hχ1 hC hP hε
  refine hsum.trans (le_of_eq ?_)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

theorem aux_prop_boundary_rf_sub_le {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (A : PositiveCoefficient Q) (u v : S.space) :
    responseForm S A (u - v) (u - v) ≤ 2 * responseForm S A u u + 2 * responseForm S A v v := by
  have h1 := responseForm_nonneg S A (u + v)
  simp only [map_sub, map_add, sub_apply, add_apply]
    at h1 ⊢
  linarith

/-- Test-function data approximating a killed element in `L²` and in the energy of the
difference. -/
theorem aux_prop_boundary_smooth_approx_diff {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (a : PositiveCoefficient Ω) (w : S.space) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓓(Ω, ℝ), ∃ hφ : smoothSobolevData φ ∈ S.space,
      ‖(smoothSobolevData φ).1 - (w : SobolevData Ω).1‖ < ε ∧
      responseForm S a (w - ⟨_, hφ⟩) (w - ⟨_, hφ⟩) < ε := by
  have hwk : (w : SobolevData Ω) ∈ killedSobolevGraph Ω :=
    aux_prop_locality_recovery_mem_killed S hS w
  have hw : (w : SobolevData Ω) ∈ closure
      ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω)) : Submodule ℝ (SobolevData Ω)) :
        Set (SobolevData Ω)) :=
    (Submodule.topologicalClosure_coe _).subst (motive := fun X => (w : SobolevData Ω) ∈ X) hwk
  let F : SobolevData Ω → ℝ := fun y =>
    weightedGradientForm a.val (sobolevGradient ((w : SobolevData Ω) - y))
      (sobolevGradient ((w : SobolevData Ω) - y))
  have hF : Continuous F :=
    ((weightedGradientForm a.val).continuous.comp
      (sobolevGradient.continuous.comp (continuous_const.sub continuous_id))).clm_apply
      (sobolevGradient.continuous.comp (continuous_const.sub continuous_id))
  have hFw : F w = 0 := by simp [F]
  let t : Set (SobolevData Ω) :=
    {y | ‖y.1 - (w : SobolevData Ω).1‖ < ε} ∩ {y | F y < ε}
  have ht : t ∈ 𝓝 (w : SobolevData Ω) := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt ((continuous_fst.sub continuous_const).norm) continuous_const).inter
        (isOpen_lt hF continuous_const)
    · refine ⟨?_, ?_⟩
      · change ‖(w : SobolevData Ω).1 - (w : SobolevData Ω).1‖ < ε
        simpa using hε
      · change F w < ε
        rw [hFw]; exact hε
  obtain ⟨b, hb⟩ := mem_closure_iff_nhds.1 hw t ht
  obtain ⟨φ, hφb⟩ := LinearMap.mem_range.1 hb.2
  have hmem : smoothSobolevData φ ∈ S.space :=
    aux_prop_locality_recovery_mem_space S hS (smoothSobolevData_mem_killed φ)
  have hbφ : smoothSobolevData φ = b := hφb
  refine ⟨φ, hmem, ?_, ?_⟩
  · rw [hbφ]; exact hb.1.1
  · have hFb : responseForm S a (w - ⟨_, hmem⟩) (w - ⟨_, hmem⟩) = F (smoothSobolevData φ) := rfl
    rw [hFb, hbφ]
    exact hb.1.2

/-- Choice of the collar width ("then `ρ ↓ 0`"): a finite measure giving no
mass to the sphere gives small mass to thin closed shells inside it. -/
theorem aux_prop_boundary_collar_choice {d : ℕ} (ν : Measure (SpatialCoordinates d))
    (hν : ν Set.univ < ⊤) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hfr : ν (Metric.sphere z R) = 0) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ 4 * ρ < R ∧
      ν (Metric.closedBall z R \ Metric.ball z (R - 3 * ρ)) < η := by
  let ρk : ℕ → ℝ := fun k => R / (8 * ((k : ℝ) + 1))
  have hρk : ∀ k, 0 < ρk k := fun k => by positivity
  let s : ℕ → Set (SpatialCoordinates d) :=
    fun k => Metric.closedBall z R \ Metric.ball z (R - 3 * ρk k)
  have hanti : Antitone s := by
    intro k l hkl x hx
    refine ⟨hx.1, fun hxb => hx.2 ?_⟩
    rw [Metric.mem_ball] at hxb ⊢
    have : ρk l ≤ ρk k := by
      apply div_le_div_of_nonneg_left hR.le (by positivity)
      have : (k : ℝ) ≤ l := by exact_mod_cast hkl
      linarith
    linarith
  have hmeas : ∀ k, NullMeasurableSet (s k) ν := fun k =>
    (Metric.isClosed_closedBall.measurableSet.diff Metric.isOpen_ball.measurableSet).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop (μ := ν) hmeas hanti
    ⟨0, ((measure_mono (subset_univ _)).trans_lt hν).ne⟩
  have hinter : ν (⋂ k, s k) = 0 := by
    refine measure_mono_null (fun x hx => ?_) hfr
    rw [mem_iInter] at hx
    have h0 := (hx 0).1
    rw [Metric.mem_closedBall] at h0
    rw [Metric.mem_sphere]
    by_contra hne
    have hlt : dist x z < R := lt_of_le_of_ne h0 hne
    obtain ⟨k, hk⟩ := exists_nat_gt (3 * R / (8 * (R - dist x z)))
    have hpos : 0 < R - dist x z := by linarith
    have hk' : 3 * ρk k < R - dist x z := by
      show 3 * (R / (8 * ((k : ℝ) + 1))) < R - dist x z
      rw [div_lt_iff₀ (by positivity)] at hk
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    exact (hx k).2 (Metric.mem_ball.2 (by linarith))
  rw [hinter] at hlim
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  refine ⟨ρk k, hρk k, ?_, hk⟩
  show 4 * (R / (8 * ((k : ℝ) + 1))) < R
  rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith




theorem aux_prop_boundary_dens_meas {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (A : PositiveCoefficient Q) (W : SobolevData Q) :
    Measurable (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, (W.2 i y) ^ 2)) :=
  ((Lp.stronglyMeasurable A.val).measurable.mul (Finset.measurable_sum _ fun i _ =>
    (Lp.stronglyMeasurable (W.2 i)).measurable.pow_const 2)).ennreal_ofReal

theorem aux_prop_boundary_modV_grad_ae {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω) (φ : 𝓓(Ω, ℝ)) (ψ : S.space)
    (i : Fin d) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (aux_prop_locality_recovery_modV S hS φ ψ : SobolevData Ω).2 i x =
        (ψ : SobolevData Ω).1 x * fderiv ℝ φ x (Pi.single i 1) +
          φ x * (ψ : SobolevData Ω).2 i x := by
  rw [aux_prop_locality_recovery_modV_grad]
  filter_upwards [Lp.coeFn_add
      (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ i)
        (ψ : SobolevData Ω).1)
      (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ)
        ((ψ : SobolevData Ω).2 i)),
    aux_prop_locality_recovery_modV_P_ae φ (ψ : SobolevData Ω) i,
    aux_prop_locality_recovery_modV_R_ae φ (ψ : SobolevData Ω) i] with x h0 h1 h2
  rw [h0, Pi.add_apply, h1, h2]


theorem aux_prop_boundary_lintegral_split {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (c1 c2 : ℝ≥0∞) (f1 f2 g1 g2 : X → ℝ≥0∞) (hf1 : Measurable f1) (hf2 : Measurable f2)
    (hg1 : Measurable g1) (hg2 : Measurable g2) :
    ∫⁻ x, (c1 * (f1 x + f2 x) + c2 * (g1 x + g2 x)) ∂μ =
      c1 * (∫⁻ x, f1 x ∂μ + ∫⁻ x, f2 x ∂μ) + c2 * (∫⁻ x, g1 x ∂μ + ∫⁻ x, g2 x ∂μ) := by
  rw [lintegral_add_left (show Measurable (fun x => c1 * (f1 x + f2 x)) by fun_prop), lintegral_const_mul c1 (show Measurable (fun x => f1 x + f2 x) by fun_prop),
    lintegral_const_mul c2 (show Measurable (fun x => g1 x + g2 x) by fun_prop), lintegral_add_left hf1, lintegral_add_left hg1]

/-- The competitor integrand bound at one point, with the gradients given coordinatewise. -/
theorem aux_prop_boundary_upper_pointwise {d : ℕ} (c χv Cind P ε e : ℝ)
    (uU dΦ dθ gχ vUY vΦ vUΘ : Fin d → ℝ)
    (hc : 0 ≤ c) (hχ0 : 0 ≤ χv) (hχ1 : χv ≤ 1) (hC : 1 - χv ≤ Cind) (hC0 : 0 ≤ Cind)
    (hP : χv ≤ P) (hP0 : 0 ≤ P) (hε : 0 < ε)
    (h1 : ∀ i, vUY i = (1 - χv) * uU i + χv * dΦ i + (χv * (uU i - dθ i) + e * gχ i))
    (h2 : ∀ i, vΦ i = dΦ i) (h3 : ∀ i, vUΘ i = uU i - dθ i) :
    ENNReal.ofReal (c * ∑ i, vUY i ^ 2) ≤
      ENNReal.ofReal (1 + ε) * (ENNReal.ofReal (Cind * (c * ∑ i, uU i ^ 2)) +
          ENNReal.ofReal (c * ∑ i, vΦ i ^ 2) * ENNReal.ofReal P) +
        ENNReal.ofReal (2 * (1 + ε⁻¹)) * (ENNReal.ofReal (c * ∑ i, vUΘ i ^ 2) +
          ENNReal.ofReal (c * ∑ i, gχ i ^ 2) * ENNReal.ofReal (e ^ 2)) := by
  simp only [h1, h2, h3]
  rw [mul_comm (ENNReal.ofReal (c * ∑ i, dΦ i ^ 2)) (ENNReal.ofReal P)]
  exact aux_prop_boundary_young_enn c χv Cind P ε e uU dΦ (fun i => uU i - dθ i) gχ hc hχ0 hχ1
    hC hC0 hP hP0 hε

theorem aux_prop_boundary_alg (uY u y mφ mθ c1 dφ φv dθ θv g χ : ℝ) (h1 : uY = u + y)
    (h2 : y = mφ - mθ) (h3 : mφ = c1 * dφ + φv * g) (h4 : mθ = c1 * dθ + θv * g) (h5 : c1 = χ) :
    uY = (1 - χ) * u + χ * dφ + (χ * (u - dθ) + (φv - θv) * g) := by
  subst h1 h2 h3 h4 h5
  ring

/-- The pointwise a.e. bound behind F3, for abstract coordinates. -/
theorem aux_prop_boundary_ae_generic {X : Type*} [MeasurableSpace X] (μ : Measure X) {d : ℕ}
    (Qs q V O Cset : Set X) (a chic c1 φW θ φρ e z : X → ℝ)
    (u uY vΦ vUΘ g dφ dθ : Fin d → X → ℝ)
    (h01 : ∀ x ∈ Qs, 0 ≤ chic x ∧ chic x ≤ 1) (hone : ∀ x ∈ V, chic x = 1)
    (hvan : ∀ x ∈ Qs, x ∉ O → chic x = 0) (hcollar : ∀ x ∈ q, x ∉ V → x ∈ Cset)
    (hφρ0 : ∀ x, 0 ≤ φρ x) (hφρ1 : ∀ x ∈ O, φρ x = 1) (ε : ℝ) (hε : 0 < ε)
    (H : ∀ᵐ x ∂μ, (∀ i, uY i x = u i x + ((c1 x * dφ i x + φW x * g i x) -
        (c1 x * dθ i x + θ x * g i x))) ∧ (∀ i, vΦ i x = dφ i x) ∧
      (∀ i, vUΘ i x = u i x - dθ i x) ∧ e x - z x = φW x - θ x ∧ c1 x = chic x ∧
      0 ≤ a x ∧ x ∈ Qs) :
    ∀ᵐ x ∂μ, q.indicator (fun y => ENNReal.ofReal (a y * ∑ i, uY i y ^ 2)) x ≤
      ENNReal.ofReal (1 + ε) *
        (Cset.indicator (fun y => ENNReal.ofReal (a y * ∑ i, u i y ^ 2)) x +
          ENNReal.ofReal (a x * ∑ i, vΦ i x ^ 2) * ENNReal.ofReal (φρ x)) +
      ENNReal.ofReal (2 * (1 + ε⁻¹)) *
        (ENNReal.ofReal (a x * ∑ i, vUΘ i x ^ 2) +
          ENNReal.ofReal (a x * ∑ i, g i x ^ 2) * ENNReal.ofReal ((e x - z x) ^ 2)) := by
  filter_upwards [H] with x ⟨h1, h2, h3, h4, h5, hA0, hxQ⟩
  by_cases hxq : x ∈ q
  · rw [Set.indicator_of_mem hxq]
    have hc01 := h01 x hxQ
    obtain ⟨Cind, hCdef⟩ : ∃ Cind : ℝ, Cind = Cset.indicator (fun _ => (1 : ℝ)) x := ⟨_, rfl⟩
    have hCind0 : 0 ≤ Cind := hCdef ▸ Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have hCind : Cset.indicator (fun y => ENNReal.ofReal (a y * ∑ i, u i y ^ 2)) x =
        ENNReal.ofReal (Cind * (a x * ∑ i, u i x ^ 2)) := by
      by_cases hxc : x ∈ Cset
      · rw [hCdef, Set.indicator_of_mem hxc, Set.indicator_of_mem hxc, one_mul]
      · rw [hCdef, Set.indicator_of_notMem hxc, Set.indicator_of_notMem hxc, zero_mul,
          ENNReal.ofReal_zero]
    rw [hCind, h4]
    refine aux_prop_boundary_upper_pointwise (a x) (chic x) Cind (φρ x) ε (φW x - θ x)
      (fun i => u i x) (fun i => dφ i x) (fun i => dθ i x) (fun i => g i x) (fun i => uY i x)
      (fun i => vΦ i x) (fun i => vUΘ i x) hA0 hc01.1 hc01.2 ?_ hCind0 ?_ (hφρ0 x) hε ?_ h2 h3
    · by_cases hxV : x ∈ V
      · rw [hone x hxV, sub_self]; exact hCind0
      · have hxc : x ∈ Cset := hcollar x hxq hxV
        have : Cind = 1 := by rw [hCdef, Set.indicator_of_mem hxc]
        rw [this]; exact sub_le_self 1 hc01.1
    · by_cases hxO : x ∈ O
      · rw [hφρ1 x hxO]; exact hc01.2
      · rw [hvan x hxQ hxO]; exact hφρ0 x
    · intro i
      rw [h1 i, h5]
      ring
  · rw [Set.indicator_of_notMem hxq]
    exact zero_le

/-- The a.e. gradient of `U + (φ_W χ - θ χ)`. -/
theorem aux_prop_boundary_fact_grad {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (U : S.space) (φW θ : 𝓓(Q, ℝ)) (χ : S.space) (i : Fin d) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ((U + (aux_prop_locality_recovery_modV S hS φW χ -
          aux_prop_locality_recovery_modV S hS θ χ) : S.space) : SobolevData Q).2 i x =
        (U : SobolevData Q).2 i x +
          (((χ : SobolevData Q).1 x * fderiv ℝ φW x (Pi.single i 1) +
              φW x * (χ : SobolevData Q).2 i x) -
            ((χ : SobolevData Q).1 x * fderiv ℝ θ x (Pi.single i 1) +
              θ x * (χ : SobolevData Q).2 i x)) := by
  filter_upwards [aux_prop_boundary_grad_add S U (aux_prop_locality_recovery_modV S hS φW χ -
      aux_prop_locality_recovery_modV S hS θ χ) i,
    aux_prop_boundary_grad_sub S (aux_prop_locality_recovery_modV S hS φW χ)
      (aux_prop_locality_recovery_modV S hS θ χ) i,
    aux_prop_boundary_modV_grad_ae S hS φW χ i, aux_prop_boundary_modV_grad_ae S hS θ χ i]
    with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

theorem aux_prop_boundary_fact_smooth_grad {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (φ : 𝓓(Q, ℝ)) (Φ : S.space)
    (hΦ : (Φ : SobolevData Q) = smoothSobolevData φ) (i : Fin d) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      (Φ : SobolevData Q).2 i x = fderiv ℝ φ x (Pi.single i 1) := by
  have h : (Φ : SobolevData Q).2 i = testPartialL2 φ i := by rw [hΦ]; rfl
  rw [h]; exact testPartialL2_coeFn φ i

theorem aux_prop_boundary_fact_sub_grad {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (U : S.space) (θ : 𝓓(Q, ℝ)) (Θ : S.space)
    (hΘ : (Θ : SobolevData Q) = smoothSobolevData θ) (i : Fin d) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ((U - Θ : S.space) : SobolevData Q).2 i x =
        (U : SobolevData Q).2 i x - fderiv ℝ θ x (Pi.single i 1) := by
  filter_upwards [aux_prop_boundary_grad_sub S U Θ i,
    aux_prop_boundary_fact_smooth_grad S θ Θ hΘ i] with x h1 h2
  rw [h1, h2]

theorem aux_prop_boundary_fact_fst {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (φW θ : 𝓓(Q, ℝ)) (Φ Θ : S.space)
    (hΦ : (Φ : SobolevData Q) = smoothSobolevData φW)
    (hΘ : (Θ : SobolevData Q) = smoothSobolevData θ) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ((Φ - Θ : S.space) : SobolevData Q).1 x - (0 : DomainL2 Q) x = φW x - θ x := by
  have hΦ1 : (Φ : SobolevData Q).1 = testL2 φW := by rw [hΦ]; rfl
  have hΘ1 : (Θ : SobolevData Q).1 = testL2 θ := by rw [hΘ]; rfl
  filter_upwards [aux_prop_boundary_fst_sub S Φ Θ, hΦ1 ▸ testL2_coeFn φW,
    hΘ1 ▸ testL2_coeFn θ,
    Lp.coeFn_zero ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, Pi.zero_apply, sub_zero]

/-- The pointwise a.e. bound behind F3 at a fixed index. -/
theorem aux_prop_boundary_upper_ae {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q) (A : PositiveCoefficient Q)
    (U : S.space) (φW θ : 𝓓(Q, ℝ)) (Φ Θ : S.space)
    (hΦ : (Φ : SobolevData Q) = smoothSobolevData φW)
    (hΘ : (Θ : SobolevData Q) = smoothSobolevData θ)
    (χ : S.space) (chic : SpatialCoordinates d → ℝ)
    (hχc : ((χ : SobolevData Q).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic)
    (h01 : ∀ x ∈ (Q : Set (SpatialCoordinates d)), 0 ≤ chic x ∧ chic x ≤ 1)
    (V O q Cset : Set (SpatialCoordinates d))
    (hone : ∀ x ∈ V, chic x = 1)
    (hvan : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ O → chic x = 0)
    (hcollar : ∀ x ∈ q, x ∉ V → x ∈ Cset)
    (φρ : SpatialCoordinates d → ℝ) (hφρ0 : ∀ x, 0 ≤ φρ x)
    (hφρ1 : ∀ x ∈ O, φρ x = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      q.indicator (fun y => ENNReal.ofReal (A.val y *
        ∑ i : Fin d, (((U + (aux_prop_locality_recovery_modV S hS φW χ -
          aux_prop_locality_recovery_modV S hS θ χ) : S.space) : SobolevData Q).2 i y) ^ 2)) x ≤
      ENNReal.ofReal (1 + ε) *
        (Cset.indicator (fun y => ENNReal.ofReal (A.val y *
          ∑ i : Fin d, ((U : SobolevData Q).2 i y) ^ 2)) x +
        ENNReal.ofReal (A.val x * ∑ i : Fin d, ((Φ : SobolevData Q).2 i x) ^ 2) *
          ENNReal.ofReal (φρ x)) +
      ENNReal.ofReal (2 * (1 + ε⁻¹)) * (ENNReal.ofReal (A.val x *
          ∑ i : Fin d, (((U - Θ : S.space) : SobolevData Q).2 i x) ^ 2) +
        ENNReal.ofReal (A.val x * ∑ i : Fin d, ((χ : SobolevData Q).2 i x) ^ 2) *
          ENNReal.ofReal ((((Φ - Θ : S.space) : SobolevData Q).1 x - (0 : DomainL2 Q) x) ^ 2)) := by
  have H1 := ae_all_iff.2 (aux_prop_boundary_fact_grad S hS U φW θ χ)
  have H2 := ae_all_iff.2 (aux_prop_boundary_fact_smooth_grad S φW Φ hΦ)
  have H3 := ae_all_iff.2 (aux_prop_boundary_fact_sub_grad S U θ Θ hΘ)
  have H4 := aux_prop_boundary_fact_fst S φW θ Φ Θ hΦ hΘ
  have H6 := aux_prop_locality_recovery_coeff_nonneg A
  have H7 := ae_restrict_mem (μ := volume) (Q.isOpen.measurableSet)
  exact aux_prop_boundary_ae_generic _ _ q V O Cset _ chic _ (fun x => φW x) (fun x => θ x) φρ
    _ _ _ _ _ _ _ (fun i x => fderiv ℝ φW x (Pi.single i 1))
    (fun i x => fderiv ℝ θ x (Pi.single i 1)) h01 hone hvan hcollar hφρ0 hφρ1 ε hε
    (((((H1.and H2).and H3).and H4).and hχc).and H6 |>.and H7 |>.mono fun x hx =>
      ⟨hx.1.1.1.1.1.1, hx.1.1.1.1.1.2, hx.1.1.1.1.2, hx.1.1.1.2, hx.1.1.2, hx.1.2, hx.2⟩)

/-- The integration step behind F3, for abstract densities. -/
theorem aux_prop_boundary_step_generic {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (q Cset : Set X) (hq : MeasurableSet q) (hCset : MeasurableSet Cset)
    (dUY dU dΦ dUΘ dχ tr ρ : X → ℝ≥0∞) (hmU : Measurable dU) (hmΦ : Measurable dΦ)
    (hmUΘ : Measurable dUΘ) (hmχ : Measurable dχ) (hmtr : Measurable tr) (hmρ : Measurable ρ)
    (c1 c2 : ℝ≥0∞)
    (hae : ∀ᵐ x ∂μ, q.indicator dUY x ≤
      c1 * (Cset.indicator dU x + dΦ x * ρ x) + c2 * (dUΘ x + dχ x * tr x)) :
    (μ.withDensity dUY) q ≤
      c1 * ((μ.withDensity dU) Cset + ∫⁻ x, ρ x ∂(μ.withDensity dΦ)) +
        c2 * (∫⁻ x, dUΘ x ∂μ + ∫⁻ x, dχ x * tr x ∂μ) := by
  rw [withDensity_apply _ hq, ← lintegral_indicator hq, withDensity_apply _ hCset,
    ← lintegral_indicator hCset, lintegral_withDensity_eq_lintegral_mul _ hmΦ hmρ]
  refine (lintegral_mono_ae hae).trans (le_of_eq ?_)
  exact aux_prop_boundary_lintegral_split μ c1 c2 _ _ _ _ (hmU.indicator hCset) (hmΦ.mul hmρ)
    hmUΘ (hmχ.mul hmtr)

/-- F3 at a fixed index : the energy `U` places on `q` is bounded by the
collar mass, the bulk of the recovery `Φ` against a continuous majorant of the cutoff, the
smoothing error and the cutoff trace term. -/
theorem aux_prop_boundary_upper_step {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q) (A : PositiveCoefficient Q)
    (U : S.space) (φW θ : 𝓓(Q, ℝ)) (Φ Θ : S.space)
    (hΦ : (Φ : SobolevData Q) = smoothSobolevData φW)
    (hΘ : (Θ : SobolevData Q) = smoothSobolevData θ)
    (χ : S.space) (chic : SpatialCoordinates d → ℝ)
    (hχc : ((χ : SobolevData Q).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic)
    (h01 : ∀ x ∈ (Q : Set (SpatialCoordinates d)), 0 ≤ chic x ∧ chic x ≤ 1)
    (V O q Cset : Set (SpatialCoordinates d)) (hq : MeasurableSet q)
    (hCset : MeasurableSet Cset)
    (hone : ∀ x ∈ V, chic x = 1)
    (hvan : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ O → chic x = 0)
    (hOq : closure O ⊆ q) (hcollar : ∀ x ∈ q, x ∉ V → x ∈ Cset)
    (φρ : SpatialCoordinates d → ℝ) (hφρm : Measurable φρ) (hφρ0 : ∀ x, 0 ≤ φρ x)
    (hφρ1 : ∀ x ∈ O, φρ x = 1)
    (horth : responseForm S A U (aux_prop_locality_recovery_modV S hS φW χ -
      aux_prop_locality_recovery_modV S hS θ χ) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((U : SobolevData Q).2 i y) ^ 2))) q ≤
    ENNReal.ofReal (1 + ε) *
      (((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((U : SobolevData Q).2 i y) ^ 2))) Cset +
      ∫⁻ x, ENNReal.ofReal (φρ x) ∂((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((Φ : SobolevData Q).2 i y) ^ 2)))) +
    ENNReal.ofReal (2 * (1 + ε⁻¹)) *
      (ENNReal.ofReal (responseForm S A (U - Θ) (U - Θ)) +
      ∫⁻ x in (Q : Set (SpatialCoordinates d)),
        ENNReal.ofReal (A.val x * ∑ i : Fin d, ((χ : SobolevData Q).2 i x) ^ 2) *
          ENNReal.ofReal ((((Φ - Θ : S.space) : SobolevData Q).1 x - (0 : DomainL2 Q) x) ^ 2)) := by
  have hvφ := aux_prop_boundary_modV_vanish S hS φW χ chic hχc O hvan
  have hvθ := aux_prop_boundary_modV_vanish S hS θ χ chic hχc O hvan
  have hYoff : ∀ i, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ q → ((aux_prop_locality_recovery_modV S hS φW χ -
        aux_prop_locality_recovery_modV S hS θ χ : S.space) : SobolevData Q).2 i x = 0 := by
    intro i
    filter_upwards [aux_prop_boundary_grad_sub S (aux_prop_locality_recovery_modV S hS φW χ)
      (aux_prop_locality_recovery_modV S hS θ χ) i, hvφ.2 i, hvθ.2 i] with x h0 h1 h2 hx
    have hxO : x ∉ closure O := fun h => hx (hOq h)
    rw [h0, h1 hxO, h2 hxO, sub_zero]
  have hstep1 := aux_prop_boundary_competitor S A U _ q hq horth hYoff
  refine hstep1.trans ?_
  rw [← aux_prop_locality_recovery_mass_eq S A (U - Θ)]
  exact aux_prop_boundary_step_generic _ q Cset hq hCset _ _ _ _ _ _ _
    (aux_prop_boundary_dens_meas A (U : SobolevData Q))
    (aux_prop_boundary_dens_meas A (Φ : SobolevData Q))
    (aux_prop_boundary_dens_meas A ((U - Θ : S.space) : SobolevData Q))
    (aux_prop_boundary_dens_meas A (χ : SobolevData Q))
    (((Lp.stronglyMeasurable _).measurable.sub
      (Lp.stronglyMeasurable _).measurable).pow_const 2).ennreal_ofReal
    hφρm.ennreal_ofReal _ _
    (aux_prop_boundary_upper_ae S hS A U φW θ Φ Θ hΦ hΘ χ chic hχc h01 V O q Cset hone hvan
      hcollar φρ hφρ0 hφρ1 ε hε)


theorem aux_prop_boundary_toReal_bound (X b c f g : ℝ≥0∞) (a e : ℝ) (ha : 0 ≤ a) (he : 0 ≤ e)
    (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hf : f ≠ ⊤) (hg : g ≠ ⊤)
    (h : X ≤ ENNReal.ofReal a * (b + c) + ENNReal.ofReal e * (f + g)) :
    X.toReal ≤ a * (b.toReal + c.toReal) + e * (f.toReal + g.toReal) := by
  have h1 : ENNReal.ofReal a * (b + c) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hb, hc⟩)
  have h2 : ENNReal.ofReal e * (f + g) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hf, hg⟩)
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h1, h2⟩) h
  rwa [ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal he, ENNReal.toReal_add hb hc,
    ENNReal.toReal_add hf hg] at this

/-- F3 at a fixed index, in real form. -/
theorem aux_prop_boundary_upper_step_real {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q) (A : PositiveCoefficient Q)
    (U : S.space) (φW θ : 𝓓(Q, ℝ)) (Φ Θ : S.space)
    (hΦ : (Φ : SobolevData Q) = smoothSobolevData φW)
    (hΘ : (Θ : SobolevData Q) = smoothSobolevData θ)
    (χ : S.space) (chic : SpatialCoordinates d → ℝ)
    (hχc : ((χ : SobolevData Q).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic)
    (h01 : ∀ x ∈ (Q : Set (SpatialCoordinates d)), 0 ≤ chic x ∧ chic x ≤ 1)
    (V O q Cset : Set (SpatialCoordinates d)) (hq : MeasurableSet q)
    (hCset : MeasurableSet Cset)
    (hone : ∀ x ∈ V, chic x = 1)
    (hvan : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ O → chic x = 0)
    (hOq : closure O ⊆ q) (hcollar : ∀ x ∈ q, x ∉ V → x ∈ Cset)
    (φρ : SpatialCoordinates d → ℝ) (hφρm : Measurable φρ) (hφρ0 : ∀ x, 0 ≤ φρ x)
    (hφρ1 : ∀ x ∈ O, φρ x = 1) (hφρle : ∀ x, φρ x ≤ 1)
    (horth : responseForm S A U (aux_prop_locality_recovery_modV S hS φW χ -
      aux_prop_locality_recovery_modV S hS θ χ) = 0)
    (ε : ℝ) (hε : 0 < ε) (M : ℝ) (hM : ∀ x, |φW x - θ x| ≤ M) :
    (((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((U : SobolevData Q).2 i y) ^ 2))) q).toReal ≤
    (1 + ε) *
      ((((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((U : SobolevData Q).2 i y) ^ 2))) Cset).toReal +
      ∫ x, φρ x ∂((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((Φ : SobolevData Q).2 i y) ^ 2)))) +
    2 * (1 + ε⁻¹) *
      (responseForm S A (U - Θ) (U - Θ) +
      (∫⁻ x in (Q : Set (SpatialCoordinates d)),
        ENNReal.ofReal (A.val x * ∑ i : Fin d, ((χ : SobolevData Q).2 i x) ^ 2) *
          ENNReal.ofReal ((((Φ - Θ : S.space) : SobolevData Q).1 x -
            (0 : DomainL2 Q) x) ^ 2)).toReal) := by
  have h := aux_prop_boundary_upper_step S hS A U φW θ Φ Θ hΦ hΘ χ chic hχc h01 V O q Cset hq
    hCset hone hvan hOq hcollar φρ hφρm hφρ0 hφρ1 horth ε hε
  have hCfin : ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((U : SobolevData Q).2 i y) ^ 2))) Cset
        ≠ ⊤ := by
    refine ((measure_mono (subset_univ _)).trans_lt ?_).ne
    rw [aux_prop_boundary_mass_univ S A U]; exact ENNReal.ofReal_lt_top
  have hIfin : ∫⁻ x, ENNReal.ofReal (φρ x) ∂((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((Φ : SobolevData Q).2 i y) ^ 2))) ≠ ⊤ := by
    refine ((lintegral_mono fun x => ENNReal.ofReal_le_one.2 (hφρle x)).trans_lt ?_).ne
    rw [lintegral_one, aux_prop_boundary_mass_univ S A Φ]
    exact ENNReal.ofReal_lt_top
  have hbd : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((((Φ - Θ : S.space) : SobolevData Q).1 x - (0 : DomainL2 Q) x) ^ 2) ≤
        ENNReal.ofReal (M ^ 2) := by
    have hΦ1 : (Φ : SobolevData Q).1 = testL2 φW := by rw [hΦ]; rfl
    have hΘ1 : (Θ : SobolevData Q).1 = testL2 θ := by rw [hΘ]; rfl
    filter_upwards [aux_prop_boundary_fst_sub S Φ Θ, hΦ1 ▸ testL2_coeFn φW,
      hΘ1 ▸ testL2_coeFn θ,
      Lp.coeFn_zero ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))] with x h1 h2 h3 h4
    apply ENNReal.ofReal_le_ofReal
    rw [h1, h2, h3, h4, Pi.zero_apply, sub_zero, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  have htrfin : (∫⁻ x in (Q : Set (SpatialCoordinates d)),
      ENNReal.ofReal (A.val x * ∑ i : Fin d, ((χ : SobolevData Q).2 i x) ^ 2) *
        ENNReal.ofReal ((((Φ - Θ : S.space) : SobolevData Q).1 x -
          (0 : DomainL2 Q) x) ^ 2)) ≠ ⊤ := by
    have hle : (∫⁻ x in (Q : Set (SpatialCoordinates d)),
        ENNReal.ofReal (A.val x * ∑ i : Fin d, ((χ : SobolevData Q).2 i x) ^ 2) *
          ENNReal.ofReal ((((Φ - Θ : S.space) : SobolevData Q).1 x -
            (0 : DomainL2 Q) x) ^ 2)) ≤
        ∫⁻ x in (Q : Set (SpatialCoordinates d)),
          ENNReal.ofReal (A.val x * ∑ i : Fin d, ((χ : SobolevData Q).2 i x) ^ 2) *
            ENNReal.ofReal (M ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [hbd] with x hx
      exact mul_le_mul_of_nonneg_left hx (zero_le)
    refine (hle.trans_lt ?_).ne
    rw [lintegral_mul_const _ (aux_prop_boundary_dens_meas A (χ : SobolevData Q)),
      aux_prop_locality_recovery_mass_eq S A χ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hint : ∫ x, φρ x ∂((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((Φ : SobolevData Q).2 i y) ^ 2))) =
      (∫⁻ x, ENNReal.ofReal (φρ x) ∂((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (A.val y * ∑ i : Fin d, ((Φ : SobolevData Q).2 i y) ^ 2)))).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hφρ0) hφρm.aestronglyMeasurable
  have h2 := aux_prop_boundary_toReal_bound _ _ _ _ _ (1 + ε) (2 * (1 + ε⁻¹)) (by linarith)
    (by positivity) hCfin hIfin ENNReal.ofReal_ne_top htrfin h
  rw [hint]
  rwa [ENNReal.toReal_ofReal (responseForm_nonneg S A (U - Θ))] at h2


/-- `U_N` is orthogonal to response elements carried by a compact subset of the centre cell
(E1 on the centre cell, then E2). -/
theorem aux_prop_boundary_orth_q {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hacont : ∀ n : ℕ, ContinuousOn (a n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNharm : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      IsWeaklyHarmonicOn (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (n : ℕ) (Kc : Set (SpatialCoordinates d)) (hKc : IsCompact Kc)
    (hKq : Kc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hKQ : Kc ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (Y : S.space)
    (hY1 : ∀ᵐ x ∂volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
      x ∉ Kc → (Y : SobolevData (centeredCube z (3 * r) h3r)).1 x = 0)
    (hY2 : ∀ i, ∀ᵐ x ∂volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
      x ∉ Kc → (Y : SobolevData (centeredCube z (3 * r) h3r)).2 i x = 0) :
    responseForm S (aC n) (UNS n) Y = 0 := by
  let k0 : OddGridIndex d (triadicHalf 1) := fun _ => ⟨triadicHalf 1, by simp [triadicHalf]⟩
  have hcell : (oddGridCell z (3 * r) h3r (triadicHalf 1) k0 : Set (SpatialCoordinates d)) =
      centeredCube z r hr := aux_prop_boundary_center_cell z r hr h3r
  refine aux_prop_boundary_orth_supported S hS (aC n) (UNS n) _ (centeredCube z r hr).isOpen ?_
    Kc hKc hKq hKQ Y hY1 hY2
  intro ζ hζS hζ
  exact aux_prop_boundary_orth_smooth z r h3r S a aC hacont haC UN UNS hUNrep _
    (oddGridCell z (3 * r) h3r (triadicHalf 1) k0).isOpen (hcellsub k0) n (hUNharm n k0) ζ
    (hcell ▸ hζ) hζS

/-- The perturbation `χ_N (φ_W - θ)` is orthogonal to `U_N`. -/
theorem aux_prop_boundary_orth_perturb {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hacont : ∀ n : ℕ, ContinuousOn (a n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNharm : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      IsWeaklyHarmonicOn (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (n : ℕ) (O : Set (SpatialCoordinates d)) (hOc : IsCompact (closure O))
    (hOq : closure O ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hOQ : closure O ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (chi : S.space) (chic : SpatialCoordinates d → ℝ)
    (hchic : ((chi : SobolevData (centeredCube z (3 * r) h3r)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] chic)
    (hvan : ∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), x ∉ O → chic x = 0)
    (φW θ : 𝓓(centeredCube z (3 * r) h3r, ℝ)) :
    responseForm S (aC n) (UNS n) (aux_prop_locality_recovery_modV S hS φW chi -
      aux_prop_locality_recovery_modV S hS θ chi) = 0 := by
  have hv1 := aux_prop_boundary_modV_vanish S hS φW chi chic hchic O hvan
  have hv2 := aux_prop_boundary_modV_vanish S hS θ chi chic hchic O hvan
  refine aux_prop_boundary_orth_q z r hr h3r S hS a aC hacont haC UN UNS hUNrep hcellsub hUNharm
    n _ hOc hOq hOQ _ ?_ ?_
  · filter_upwards [aux_prop_boundary_fst_sub S
      (aux_prop_locality_recovery_modV S hS φW chi)
      (aux_prop_locality_recovery_modV S hS θ chi), hv1.1, hv2.1] with x h0 h1 h2 hx
    rw [h0, h1 hx, h2 hx, sub_zero]
  · intro i
    filter_upwards [aux_prop_boundary_grad_sub S
      (aux_prop_locality_recovery_modV S hS φW chi)
      (aux_prop_locality_recovery_modV S hS θ chi) i, hv1.2 i, hv2.2 i] with x h0 h1 h2 hx
    rw [h0, h1 hx, h2 hx, sub_zero]

/-- A recovery sequence of `Ū` by test-function data. -/
theorem aux_prop_boundary_smooth_recovery {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (aC : ℕ → PositiveCoefficient Q)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (uBar : DomainL2 Q) (hdom : uBar ∈ E.domain)
    (hRecovery : ∀ v ∈ E.domain, ∃ vn : ℕ → S.space,
      Tendsto (fun n => ((vn n).val.1,
        (responseForm S (aC n) (vn n) (vn n) : EReal))) atTop (𝓝 (v, E.energy v))) :
    ∃ (φW : ℕ → 𝓓(Q, ℝ)) (Φ : ℕ → S.space),
      (∀ n, (Φ n : SobolevData Q) = smoothSobolevData (φW n)) ∧
      Tendsto (fun n => (Φ n).val.1) atTop (𝓝 uBar) ∧
      (∃ Eb : ℝ, ∀ n, responseForm S (aC n) (Φ n) (Φ n) ≤ Eb) ∧
      Tendsto (fun n => ((Φ n).val.1, (responseForm S (aC n) (Φ n) (Φ n) : EReal))) atTop
        (𝓝 (uBar, E.energy uBar)) := by
  have hEnn : 0 ≤ E.energy uBar := _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_nonneg _ _
  have hEtop : E.energy uBar < ⊤ := by
    rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_mem _ hdom]; exact EReal.coe_lt_top _
  have hrec := hRecovery uBar hdom
  obtain ⟨wN, hwN⟩ := hrec
  have hparts := aux_prop_locality_recovery_recovery_parts _ _ _ _ hEnn hEtop hwN
  obtain ⟨hwN1, hwNE⟩ := hparts
  have hsm := aux_prop_locality_recovery_smooth_seq S hS aC wN uBar _ hwN1 hwNE
  obtain ⟨φW, Φ, hΦv, hΦ1, hΦE⟩ := hsm
  have hEL : E.energy uBar = ((E.energy uBar).toReal : EReal) :=
    (EReal.coe_toReal hEtop.ne (ne_bot_of_le_ne_bot (by simp) hEnn)).symm
  obtain ⟨Eb, hEb⟩ := hΦE.bddAbove_range
  refine ⟨φW, Φ, hΦv, hΦ1, ⟨Eb, fun n => hEb ⟨n, rfl⟩⟩, hΦ1.prodMk_nhds ?_⟩
  rw [hEL]
  exact EReal.tendsto_coe.2 hΦE

theorem aux_prop_boundary_diff_energy {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (aC : ℕ → PositiveCoefficient Q) (UNS Φ Θ : ℕ → S.space)
    (E0 : ℝ) (hE0 : ∀ n, responseForm S (aC n) (UNS n) (UNS n) ≤ E0)
    (EbΦ : ℝ) (hEbΦ : ∀ n, responseForm S (aC n) (Φ n) (Φ n) ≤ EbΦ)
    (hθE : ∀ n, responseForm S (aC n) (UNS n - Θ n) (UNS n - Θ n) < 1 / ((n : ℝ) + 1)) :
    ∀ n, responseForm S (aC n) (Φ n - Θ n) (Φ n - Θ n) ≤ 2 * EbΦ + 2 * (2 * E0 + 2) := by
  intro n
  have h := aux_prop_boundary_rf_sub_le S (aC n) (UNS n) (UNS n - Θ n)
  rw [sub_sub_cancel] at h
  have h2 := (hθE n).le
  have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h4 := aux_prop_boundary_rf_sub_le S (aC n) (Φ n) (Θ n)
  linarith [hE0 n, hEbΦ n]

theorem aux_prop_boundary_diff_tendsto {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (UNS Φ Θ : ℕ → S.space) (uBar : DomainL2 Q)
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (hΦ1 : Tendsto (fun n => (Φ n).val.1) atTop (𝓝 uBar))
    (hθ1 : ∀ n, ‖(Θ n : SobolevData Q).1 - (UNS n).val.1‖ < 1 / ((n : ℝ) + 1)) :
    Tendsto (fun n => (Φ n - Θ n).val.1) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => (Θ n : SobolevData Q).1 - (UNS n).val.1) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hθ1 n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := hΦ1.sub (h1.add hUNL2)
  rw [zero_add, sub_self] at h2
  refine h2.congr fun n => ?_
  change (Φ n).val.1 - ((Θ n).val.1 - (UNS n).val.1 + (UNS n).val.1) =
    (Φ n).val.1 - (Θ n).val.1
  rw [sub_add_cancel]

/-- The smoothing errors and the cutoff trace terms vanish in the limit (trace step via
`lem_19`). -/
theorem aux_prop_boundary_errors {d : ℕ} (hd : 2 ≤ d)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (S : ResponseSpace (centeredCube z R hR))
    (aC : ℕ → PositiveCoefficient (centeredCube z R hR))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n) (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z R hR _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z R hR _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (aC n) w w)
    (chi : ℕ → S.space) (B : ℝ) (hB : 0 ≤ B)
    (hcutE : ∀ n, responseForm S (aC n) (chi n) (chi n) ≤ B)
    (hgrowth : ∀ n, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))
    (UNS Φ Θ : ℕ → S.space)
    (hΦΘ : Tendsto (fun n => (Φ n - Θ n).val.1) atTop (𝓝 0))
    (Eb : ℝ) (hEb : ∀ n, responseForm S (aC n) (Φ n - Θ n) (Φ n - Θ n) ≤ Eb)
    (hθE : ∀ n, responseForm S (aC n) (UNS n - Θ n) (UNS n - Θ n) < 1 / ((n : ℝ) + 1)) :
    Tendsto (fun n => responseForm S (aC n) (UNS n - Θ n) (UNS n - Θ n) +
      (∫⁻ x in (centeredCube z R hR : Set (SpatialCoordinates d)),
        ENNReal.ofReal ((aC n).val x * ∑ i : Fin d, ((chi n).val.2 i x) ^ 2) *
          ENNReal.ofReal (((Φ n - Θ n).val.1 x -
            (0 : DomainL2 (centeredCube z R hR)) x) ^ 2)).toReal) atTop (𝓝 0) := by
  have hE : Tendsto (fun n => responseForm S (aC n) (UNS n - Θ n) (UNS n - Θ n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => responseForm_nonneg S (aC n) _) (fun n => (hθE n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hT := aux_prop_locality_recovery_trace_tendsto hd hInterp z R hR t ht S aC KN hKN
    Kstar hKstar hfrac hcoercive chi B hB hcutE hgrowth (fun n => Φ n - Θ n) 0 hΦΘ Eb hEb
  simpa using hE.add hT

/-- A continuous majorant of the collar cutoffs, carried by the centre cell. -/
theorem aux_prop_boundary_majorant {d : ℕ} (z : SpatialCoordinates d) (s ρ : ℝ) (hρ : 0 < ρ) :
    ∃ f : C(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
      (∀ x ∈ Metric.ball z (s - ρ), f x = 1) ∧
      (∀ x, f x ≤ (Metric.ball z s).indicator 1 x) := by
  have hdisj : Disjoint (Metric.ball z (s - ρ / 2))ᶜ (Metric.closedBall z (s - ρ)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx (Metric.closedBall_subset_ball (by linarith) hx')
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed
    Metric.isOpen_ball.isClosed_compl Metric.isClosed_closedBall hdisj
  refine ⟨f, fun x => (hf01 x).1, fun x => (hf01 x).2,
    fun x hx => hf1 (Metric.ball_subset_closedBall hx), fun x => ?_⟩
  by_cases hx : x ∈ Metric.ball z s
  · rw [Set.indicator_of_mem hx]; exact (hf01 x).2
  · have hx' : x ∈ (Metric.ball z (s - ρ / 2))ᶜ := fun hb =>
      hx (Metric.ball_subset_ball (by linarith) hb)
    rw [hf0 hx', Set.indicator_of_notMem hx]
    rfl

/-- The bulk limit is at most the energy of the cell. -/
theorem aux_prop_boundary_bulk_le {d : ℕ} (Γm : Measure (SpatialCoordinates d))
    [IsFiniteMeasure Γm] (q : Set (SpatialCoordinates d)) (hq : MeasurableSet q)
    (f : C(SpatialCoordinates d, ℝ)) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hfq : ∀ x, f x ≤ q.indicator 1 x) :
    ∫ x, f x ∂Γm ≤ (Γm q).toReal := by
  rw [← measureReal_def, ← integral_indicator_one hq]
  refine integral_mono ?_ ((integrable_const (1 : ℝ)).indicator hq) hfq
  exact Integrable.mono' (integrable_const (1 : ℝ)) f.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]; exact hf1 x)

/-- Final arithmetic of the upper bound. -/
theorem aux_prop_boundary_upper_numbers (X C c2 E : ℝ) (G δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hεG : ε * G ≤ δ / 8)
    (hstep : X ≤ (1 + ε) * (C + c2) + E) (hC : C < δ / 8) (hc2 : c2 < G + δ / 8)
    (hE : E < δ / 8) : X < G + δ := by
  have hεδ : ε * δ ≤ δ := mul_le_of_le_one_left hδ.le hε1
  nlinarith [mul_le_mul_of_nonneg_left hC.le hε.le, mul_le_mul_of_nonneg_left hc2.le hε.le]

/-- Choice of `ε` for the upper bound. -/
theorem aux_prop_boundary_eps (G δ : ℝ) (hG : 0 ≤ G) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε * G ≤ δ / 8 := by
  refine ⟨min 1 (δ / (8 * (G + 1))), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  have h1 : min 1 (δ / (8 * (G + 1))) ≤ δ / (8 * (G + 1)) := min_le_right _ _
  have h2 := mul_le_mul_of_nonneg_right h1 hG
  have h3 : δ / (8 * (G + 1)) * G ≤ δ / 8 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith


/-- The collar geometry of the centre cell `q = B(z, r/2)` at width `ρ`. -/
theorem aux_prop_boundary_collar_geom {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h3r : 0 < 3 * r) (ρ : ℝ) (hρ : 0 < ρ) (h4ρ : 4 * ρ < r / 2) :
    IsCompact (Metric.closedBall z (r / 2 - 3 * ρ)) ∧
    Metric.closedBall z (r / 2 - 3 * ρ) ⊆ Metric.ball z (r / 2 - ρ) ∧
    IsCompact (closure (Metric.ball z (r / 2 - ρ))) ∧
    closure (Metric.ball z (r / 2 - ρ)) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
    closure (Metric.ball z (r / 2 - ρ)) ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ∧
    IsClosed (Metric.closedBall z (r / 2) \ Metric.ball z (r / 2 - 3 * ρ)) ∧
    ∀ V : Set (SpatialCoordinates d), Metric.closedBall z (r / 2 - 3 * ρ) ⊆ V →
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), x ∉ V →
        x ∈ Metric.closedBall z (r / 2) \ Metric.ball z (r / 2 - 3 * ρ) := by
  have hqball : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) :=
    centeredCube_coe_eq_ball z r hr
  have hQball : (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) =
      Metric.ball z (3 * r / 2) := centeredCube_coe_eq_ball z (3 * r) h3r
  have hclO : closure (Metric.ball z (r / 2 - ρ)) ⊆ Metric.closedBall z (r / 2 - ρ) :=
    Metric.closure_ball_subset_closedBall
  have hOq : closure (Metric.ball z (r / 2 - ρ)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [hqball]; exact hclO.trans (Metric.closedBall_subset_ball (by linarith))
  refine ⟨isCompact_closedBall _ _, Metric.closedBall_subset_ball (by linarith),
    (isCompact_closedBall z (r / 2 - ρ)).of_isClosed_subset isClosed_closure hclO, hOq, ?_,
    Metric.isClosed_closedBall.sdiff Metric.isOpen_ball, ?_⟩
  · refine hOq.trans ?_
    rw [hqball, hQball]; exact Metric.ball_subset_ball (by linarith)
  · intro V hKV x hx hxV
    rw [hqball] at hx
    refine ⟨Metric.ball_subset_closedBall hx, fun hb => hxV (hKV ?_)⟩
    exact Metric.ball_subset_closedBall hb



/-- Test-function approximations `θ_N` of `U_N` whose smoothing error and cutoff trace
term vanish in the limit. -/
theorem aux_prop_boundary_theta {d : ℕ} (hd : 2 ≤ d)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (aC : ℕ → PositiveCoefficient (centeredCube z R hR))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n) (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z R hR _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z R hR _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (aC n) w w)
    (chi : ℕ → S.space) (B : ℝ) (hB : 0 ≤ B)
    (hcutE : ∀ n, responseForm S (aC n) (chi n) (chi n) ≤ B)
    (hgrowth : ∀ n, ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))
    (UNS : ℕ → S.space) (uBar : DomainL2 (centeredCube z R hR))
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (E0 : ℝ) (hE0 : ∀ n, responseForm S (aC n) (UNS n) (UNS n) ≤ E0)
    (Φ : ℕ → S.space) (hΦ1 : Tendsto (fun n => (Φ n).val.1) atTop (𝓝 uBar))
    (EbΦ : ℝ) (hEbΦ : ∀ n, responseForm S (aC n) (Φ n) (Φ n) ≤ EbΦ) :
    ∃ (θ : ℕ → 𝓓(centeredCube z R hR, ℝ)) (Θ : ℕ → S.space),
      (∀ n, (Θ n : SobolevData (centeredCube z R hR)) = smoothSobolevData (θ n)) ∧
      Tendsto (fun n => responseForm S (aC n) (UNS n - Θ n) (UNS n - Θ n) +
        (∫⁻ x in (centeredCube z R hR : Set (SpatialCoordinates d)),
          ENNReal.ofReal ((aC n).val x * ∑ i : Fin d, ((chi n).val.2 i x) ^ 2) *
            ENNReal.ofReal (((Φ n - Θ n).val.1 x -
              (0 : DomainL2 (centeredCube z R hR)) x) ^ 2)).toReal) atTop (𝓝 0) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose θ hθS hθ1 hθE using fun n =>
    aux_prop_boundary_smooth_approx_diff S hS (aC n) (UNS n) (hpos n)
  have hΘex : ∃ Θ : ℕ → S.space, ∀ n, Θ n = ⟨smoothSobolevData (θ n), hθS n⟩ :=
    ⟨fun n => ⟨smoothSobolevData (θ n), hθS n⟩, fun n => rfl⟩
  obtain ⟨Θ, hΘdef⟩ := hΘex
  have hΘv : ∀ n, (Θ n : SobolevData (centeredCube z R hR)) = smoothSobolevData (θ n) :=
    fun n => by rw [hΘdef n]
  have hΘ1 : ∀ n, ‖(Θ n : SobolevData (centeredCube z R hR)).1 - (UNS n).val.1‖ <
      1 / ((n : ℝ) + 1) := fun n => by rw [hΘv n]; exact hθ1 n
  have hΘE : ∀ n, responseForm S (aC n) (UNS n - Θ n) (UNS n - Θ n) < 1 / ((n : ℝ) + 1) :=
    fun n => by rw [hΘdef n]; exact hθE n
  have hdt := aux_prop_boundary_diff_tendsto S UNS Φ Θ uBar hUNL2 hΦ1 hΘ1
  have hde := aux_prop_boundary_diff_energy S aC UNS Φ Θ E0 hE0 EbΦ hEbΦ hΘE
  exact ⟨θ, Θ, hΘv, aux_prop_boundary_errors hd hInterp z R hR t ht S aC KN hKN Kstar hKstar
    hfrac hcoercive chi B hB hcutE hgrowth UNS Φ Θ hdt _ hde hΘE⟩


/-- F3 data at a fixed collar width `ρ` and Young parameter `ε`.  Along a bad
subsequence take a weak cluster `ν` (so `ν(∂q) = 0`), a collar width `ρ` with small
`ν`-mass, the catalog cutoff of the collar, the competitor `U_N + χ_N(Φ_N - θ_N)`, and let
`N → ∞` with `ε` fixed. -/
theorem aux_prop_boundary_upper_data {d : ℕ} (hd : 2 ≤ d)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (hr : 0 < r)
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (UNS : ℕ → S.space)
    (uBar : DomainL2 (centeredCube z (3 * r) h3r))
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (Bcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (_hBcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Bcell k)
    (_hCellGrowth : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y *
            ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t))
    (E0 : ℝ) (hE0 : ∀ n : ℕ, responseForm S (aC n) (UNS n) (UNS n) ≤ E0)
    (_hB : ∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
          (uN : ℕ → S.space) (E0 : ℝ)
          (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
        nu Set.univ < (⊤ : ENNReal) →
        nu ((closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))ᶜ) = 0 →
        StrictMono sigma →
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        (∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC (sigma n)).val y *
                ∑ i : Fin d, ((uN (sigma n) : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂nu))) →
        u ∈ EQ.toClosedForm.domain ∧
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            Gamma.measure u B ≤ nu B)
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (hacont : ∀ n : ℕ, ContinuousOn (a n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNharm : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      IsWeaklyHarmonicOn (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (hRecovery : ∀ v ∈ EQ.toClosedForm.domain, ∃ vn : ℕ → S.space,
      Tendsto (fun n => ((vn n).val.1,
        (responseForm S (aC n) (vn n) (vn n) : EReal))) atTop
        (𝓝 (v, EQ.toClosedForm.energy v)))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 +
          volume.real (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) *
            ((cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
              (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        KN n * responseForm S (aC n) w w)
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n)
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
              chic n ∧
          (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            x ∉ O → chic n x = 0) ∧
          responseForm S (aC n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y *
                ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (hA : ∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
          (uN : ℕ → S.space),
        u ∈ EQ.toClosedForm.domain →
        Tendsto (fun n => ((uN n).val.1,
          (responseForm S (aC n) (uN n) (uN n) : EReal))) atTop
          (𝓝 (u, EQ.toClosedForm.energy u)) →
        ∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y *
                ∑ i : Fin d, ((uN n : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂(Gamma.measure u))))
    (hdom : uBar ∈ EQ.toClosedForm.domain)
    (ρ : ℝ) (hρ : 0 < ρ) (h4ρ : 4 * ρ < r / 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ (c2 E : ℕ → ℝ),
      (∀ n, (((volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((aC n).val y *
          ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2))) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (1 + ε) * ((((volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((aC n).val y *
          ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
          (Metric.closedBall z (r / 2) \ Metric.ball z (r / 2 - 3 * ρ))).toReal + c2 n) + E n) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
        c2 n < (Gamma.measure uBar (centeredCube z r hr : Set (SpatialCoordinates d))).toReal + η) ∧
      Tendsto E atTop (𝓝 0) := by
  have hqo : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen
  have hqball : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) :=
    centeredCube_coe_eq_ball z r hr
  have hgeom := aux_prop_boundary_collar_geom z r hr h3r ρ hρ h4ρ
  obtain ⟨hKc, hKO, hOc, hOq, hOQ, hCcl, hcollar⟩ := hgeom
  have hcut := hcutoffs _ _ hKc Metric.isOpen_ball hKO hOQ
  obtain ⟨V, chi, chic, B, -, hKV, -, hB0, hchi⟩ := hcut
  obtain ⟨f, hf0, hf1, hfO, hfq⟩ := aux_prop_boundary_majorant z (r / 2) ρ hρ
  have hrec := aux_prop_boundary_smooth_recovery S hS aC EQ.toClosedForm uBar hdom hRecovery
  obtain ⟨φW, Φ, hΦv, hΦ1, ⟨EbΦ, hEbΦ⟩, hΦrec⟩ := hrec
  have hth := aux_prop_boundary_theta hd hInterp z (3 * r) h3r t ht S hS aC KN hKN Kstar hKstar
    hfrac hcoercive chi B hB0 (fun n => (hchi n).2.2.2.2.2.1) (fun n => (hchi n).2.2.2.2.2.2)
    UNS uBar hUNL2 E0 hE0 Φ hΦ1 EbΦ hEbΦ
  obtain ⟨θ, Θ, hΘv, herr⟩ := hth
  have hM : ∀ n, ∃ M : ℝ, ∀ x, |φW n x - θ n x| ≤ M := by
    intro n
    obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support
      ((φW n).contDiff.continuous.sub (θ n).contDiff.continuous)
      ((φW n).hasCompactSupport.sub (θ n).hasCompactSupport)
    exact ⟨M, fun x => by simpa [Real.norm_eq_abs] using hM x⟩
  choose M hMb using hM
  have hstep := fun n => aux_prop_boundary_upper_step_real S hS (aC n) (UNS n) (φW n) (θ n)
    (Φ n) (Θ n) (hΦv n) (hΘv n) (chi n) (chic n) (hchi n).2.1
    (hchi n).2.2.1 V _ _ _ hqo.measurableSet hCcl.measurableSet (hchi n).2.2.2.1
    (hchi n).2.2.2.2.1 hOq (hcollar V hKV) f f.continuous.measurable hf0 hfO hf1
    (aux_prop_boundary_orth_perturb z r hr h3r S hS a aC hacont haC UN UNS hUNrep hcellsub
      hUNharm n _ hOc hOq hOQ (chi n) (chic n) (hchi n).2.1 (hchi n).2.2.2.2.1 (φW n) (θ n))
    ε hε (M n) (hMb n)
  have hET := herr.const_mul (2 * (1 + ε⁻¹))
  simp only [mul_zero] at hET
  refine ⟨_, _, hstep, fun η hη => ?_, hET⟩
  have : IsFiniteMeasure (Gamma.measure uBar) := ⟨Gamma.measure_univ_lt_top uBar hdom⟩
  have hbulk := hA uBar Φ hdom hΦrec f f.continuous.continuousOn
  have hbulkG := aux_prop_boundary_bulk_le (Gamma.measure uBar) _ hqo.measurableSet f hf0 hf1
    (by rw [hqball]; exact hfq)
  exact hbulk.eventually_lt_const (by linarith)

/-- F3 (upper bound): `limsup Λ_{N,q}(b) ≤ Γ(Ū)(q)`.  Along a bad
subsequence take a weak cluster `ν` (so `ν(∂q) = 0`), a collar width `ρ` with small
`ν`-mass, the catalog cutoff of the collar, the competitor `U_N + χ_N(Φ_N - θ_N)`, and let
`N → ∞` with `ε` fixed. -/
theorem aux_prop_boundary_upper {d : ℕ} (hd : 2 ≤ d)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (h3r : 0 < 3 * r)
    (hr : 0 < r)
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (UNS : ℕ → S.space)
    (uBar : DomainL2 (centeredCube z (3 * r) h3r))
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (Bcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hBcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Bcell k)
    (hCellGrowth : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y *
            ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t))
    (E0 : ℝ) (hE0 : ∀ n : ℕ, responseForm S (aC n) (UNS n) (UNS n) ≤ E0)
    (hB : ∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
          (uN : ℕ → S.space) (E0 : ℝ)
          (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
        nu Set.univ < (⊤ : ENNReal) →
        nu ((closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))ᶜ) = 0 →
        StrictMono sigma →
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        (∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC (sigma n)).val y *
                ∑ i : Fin d, ((uN (sigma n) : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂nu))) →
        u ∈ EQ.toClosedForm.domain ∧
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            Gamma.measure u B ≤ nu B)
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (hacont : ∀ n : ℕ, ContinuousOn (a n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNharm : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      IsWeaklyHarmonicOn (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (hRecovery : ∀ v ∈ EQ.toClosedForm.domain, ∃ vn : ℕ → S.space,
      Tendsto (fun n => ((vn n).val.1,
        (responseForm S (aC n) (vn n) (vn n) : EReal))) atTop
        (𝓝 (v, EQ.toClosedForm.energy v)))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 +
          volume.real (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) *
            ((cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
              (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        KN n * responseForm S (aC n) w w)
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n)
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
              chic n ∧
          (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            x ∉ O → chic n x = 0) ∧
          responseForm S (aC n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y *
                ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (hA : ∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
          (uN : ℕ → S.space),
        u ∈ EQ.toClosedForm.domain →
        Tendsto (fun n => ((uN n).val.1,
          (responseForm S (aC n) (uN n) (uN n) : EReal))) atTop
          (𝓝 (u, EQ.toClosedForm.energy u)) →
        ∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y *
                ∑ i : Fin d, ((uN n : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂(Gamma.measure u))))
    (hdom : uBar ∈ EQ.toClosedForm.domain)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, (((volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((aC n).val y *
          ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal <
      (Gamma.measure uBar (centeredCube z r hr : Set (SpatialCoordinates d))).toReal + δ := by
  have hqball : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) :=
    centeredCube_coe_eq_ball z r hr
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hcon' := hcon.mono fun n hn => not_lt.1 hn
  obtain ⟨σ0, hσ0, hle⟩ := extraction_of_frequently_atTop hcon'
  have hcl := aux_prop_boundary_cluster hd z r h3r EQ Gamma S aC UNS uBar hUNL2 t ht htd Bcell
    hBcell hCellGrowth E0 hE0 hB σ0 hσ0
  obtain ⟨ν, σ, hσ, hνfin, -, hconv, -, hνfr⟩ := hcl
  have hG0 : 0 ≤ (Gamma.measure uBar (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
    ENNReal.toReal_nonneg
  obtain ⟨ε, hε, hε1, hεG⟩ := aux_prop_boundary_eps _ δ hG0 hδ
  have hsph : ν (Metric.sphere z (r / 2)) = 0 := by
    have h := hνfr z r hr
    rwa [hqball, frontier_ball z (ne_of_gt (by linarith))] at h
  obtain ⟨ρ, hρ, h4ρ, hνC⟩ := aux_prop_boundary_collar_choice ν hνfin z (r / 2) (by linarith)
    hsph (ENNReal.ofReal (δ / 8)) (by simpa using hδ)
  have hdata := aux_prop_boundary_upper_data hd hInterp z r h3r hr EQ Gamma S aC UNS uBar hUNL2
    t ht htd Bcell hBcell hCellGrowth E0 hE0 hB hS a hacont haC UN hUNrep hcellsub hUNharm
    hRecovery KN hKN Kstar hKstar hfrac hcoercive hcutoffs hA hdom ρ hρ (by linarith) ε hε
  obtain ⟨c2, E, hstep, hc2, hE⟩ := hdata
  have hCcl : IsClosed (Metric.closedBall z (r / 2) \ Metric.ball z (r / 2 - 3 * ρ)) :=
    Metric.isClosed_closedBall.sdiff Metric.isOpen_ball
  have hnm : Tendsto (fun m => σ0 (σ m)) atTop atTop := (hσ0.comp hσ).tendsto_atTop
  have hmass : ∀ n, ((volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal ((aC n).val y *
          ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
        Set.univ < ⊤ := fun n => by
    rw [aux_prop_boundary_mass_univ S (aC n) (UNS n)]
    exact ENNReal.ofReal_lt_top
  have hlimsup := aux_prop_boundary_limsup_closed _ _ ν (fun m => hmass (σ0 (σ m))) hνfin hconv
    _ hCcl
  have hev1 := eventually_lt_of_limsup_lt (hlimsup.trans_lt hνC)
  have hev2 := hnm.eventually (hc2 (δ / 8) (by positivity))
  have hev3 := hnm.eventually (hE.eventually_lt_const (show (0 : ℝ) < δ / 8 by positivity))
  obtain ⟨m, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
  exact absurd (aux_prop_boundary_upper_numbers _ _ _ _ _ δ ε hδ hε hε1 hεG
    (hstep (σ0 (σ m))) (ENNReal.toReal_lt_of_lt_ofReal h1) h2 h3) (not_lt.2 (hle (σ m)))

end PropBoundaryAux

/-- proposition `mfd:prop-boundary`, native boundary
responses with the corrected native carriers, per-cell estimates, Mosco pair,
weak energy-measure convergence, and truncation input.

Scope and inputs: hUNL2 is the represented smooth-solution coordinate from
conv_represented_sequence. Uniform convergence remains a
conclusion: compactness plus the unique L² limit identifies every cluster.
Inputs and suppliers: finite mesh carriers from mesh_interpolator/cell_boundary_continuity; per-cell data from lem_extension,prop_growth,conv_represented_estimates,conv_represented_sequence; Mosco from prop_killed_inverse; native killed subspaces from prop_killed_consistency; actual trace/coercivity and cutoff inputs from lem_19,lem_coercivity,catalog_cutoff_existence; all three weak measure convergence outputs from cor_energy_measures; hZeroTrace from lem_truncation; Gamma calculus from obl_FOT/conv_energy_measure_normalization.   No cutoff-uniform ellipticity, no setwise convergence, no assumed limit-domain membership and no dense proper killed subdomain on the wrong ambient L2. -/
theorem prop_boundary
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (q : Set (SpatialCoordinates d))
    (hqcell : q = (centeredCube z r hr : Set (SpatialCoordinates d)))
    (Dq : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)))
    (hkilled : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EQ.toClosedForm q Dq)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hacont : ∀ n : ℕ, ContinuousOn (a n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
          a n)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ a n x ∧ a n x ≤ Lam)
    (b beta : SpatialCoordinates d → ℝ)
    (_hbeta : ContDiff ℝ ∞ beta)
    (_hbetasupp : HasCompactSupport beta)
    (_hbetaQ : tsupport beta ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hbetab : ∀ x ∈ frontier q, beta x = b x)
    (betaQ : H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hbetaQfun : betaQ.toFun = beta)
    (betaq : H1Function q)
    (hbetaqfun : betaq.toFun = beta)
    (UN : ℕ → H1Function
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hUNrep : ∀ n : ℕ,
      (UNS n : SobolevData (centeredCube z (3 * r) h3r)) =
        sobolevDataOfH1 (UN n))
    (uBar : DomainL2 (centeredCube z (3 * r) h3r))
    (hUNL2 : Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNharm : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      IsWeaklyHarmonicOn (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (hUNtrace : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      HasZeroTraceDifferenceOn
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k))
        (betaQ.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)))
    (_hUNcellcont : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ContinuousOn (UN n).toFun
        (closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d))))
    (hUNcellb : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ frontier (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
        (UN n).toFun x = beta x)
    (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ)
    (hBcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Bcell k)
    (_hHcell : ∀ k : OddGridIndex d (triadicHalf 1), 0 ≤ Hcell k)
    (hCellEnergy : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      energy (a n)
        (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))
        ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
          (hcellsub k)) ≤ Bcell k)
    (hCellGrowth : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y *
            ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t))
    (hCellHolder : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        ∀ y ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
          |(UN n).toFun x - (UN n).toFun y| ≤ Hcell k * dist x y ^ alpha) ∧
      (∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d)),
        |(UN n).toFun x| ≤ Hcell k))
    (hLower : ∀ (vn : ℕ → S.space)
      (v : DomainL2 (centeredCube z (3 * r) h3r)),
      (∀ f : DomainL2 (centeredCube z (3 * r) h3r),
        Tendsto (fun n => inner ℝ f (vn n).val.1) atTop
          (𝓝 (inner ℝ f v))) →
      EQ.toClosedForm.energy v ≤
        Filter.liminf (fun n =>
          (responseForm S (aC n) (vn n) (vn n) : EReal)) atTop)
    (hRecovery : ∀ v ∈ EQ.toClosedForm.domain, ∃ vn : ℕ → S.space,
      Tendsto (fun n => ((vn n).val.1,
        (responseForm S (aC n) (vn n) (vn n) : EReal))) atTop
        (𝓝 (v, EQ.toClosedForm.energy v)))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 +
          volume.real (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) *
            ((cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
              (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        KN n * responseForm S (aC n) w w)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n)
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
              chic n ∧
          (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            x ∉ O → chic n x = 0) ∧
          responseForm S (aC n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y *
                ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (hEnergyMeasures :
      (∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
          (uN : ℕ → S.space),
        u ∈ EQ.toClosedForm.domain →
        Tendsto (fun n => ((uN n).val.1,
          (responseForm S (aC n) (uN n) (uN n) : EReal))) atTop
          (𝓝 (u, EQ.toClosedForm.energy u)) →
        ∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y *
                ∑ i : Fin d, ((uN n : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂(Gamma.measure u)))) ∧
      (∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
          (uN : ℕ → S.space) (E0 : ℝ)
          (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
        nu Set.univ < (⊤ : ENNReal) →
        nu ((closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))ᶜ) = 0 →
        StrictMono sigma →
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        (∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC (sigma n)).val y *
                ∑ i : Fin d, ((uN (sigma n) : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂nu))) →
        u ∈ EQ.toClosedForm.domain ∧
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            Gamma.measure u B ≤ nu B) ∧
      (∀ (u v : DomainL2 (centeredCube z (3 * r) h3r))
          (uN vN : ℕ → S.space) (E0 : ℝ),
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        v ∈ EQ.toClosedForm.domain →
        Tendsto (fun n => ((vN n).val.1,
          (responseForm S (aC n) (vN n) (vN n) : EReal))) atTop
          (𝓝 (v, EQ.toClosedForm.energy v)) →
        ∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x in (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
              φ x * ((aC n).val x *
                ∑ i : Fin d,
                  ((uN n : SobolevData (centeredCube z (3 * r) h3r)).2 i x) *
                  ((vN n : SobolevData (centeredCube z (3 * r) h3r)).2 i x))) atTop
            (𝓝 (_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ))))
    (hZeroTrace : ∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
      let qc := centeredCube zc rc hrc
      (qc : Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) →
      ∀ D : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EQ.toClosedForm (qc : Set (SpatialCoordinates d)) D →
      ∀ w ∈ EQ.toClosedForm.domain, ∀ wc : SpatialCoordinates d → ℝ,
        ContinuousOn wc
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        (w : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] wc →
        (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), wc x = 0) →
        ∀ wq : DomainL2 (centeredCube z (3 * r) h3r),
          (wq : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
              (closure (qc : Set (SpatialCoordinates d))).indicator wc →
          wq ∈ D ∧
            EQ.form wq wq =
              (Gamma.measure w (qc : Set (SpatialCoordinates d))).toReal)
    (_hKilledCells : ∀ k : OddGridIndex d (triadicHalf 1),
      ∃ D : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)),
        (_root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EQ.toClosedForm
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) D)) :
    ∃ (U : DomainL2 (centeredCube z (3 * r) h3r))
      (Uc : SpatialCoordinates d → ℝ),
      U ∈ EQ.toClosedForm.domain ∧
      ContinuousOn Uc
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (U : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc ∧
      TendstoUniformlyOn (fun n => (UN n).toFun) Uc atTop
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier q, Uc x = b x) ∧
      Gamma.measure U (frontier q) = 0 ∧
      (∀ φ : DomainL2 (centeredCube z (3 * r) h3r), φ ∈ Dq →
        EQ.form U φ = 0) ∧
      Tendsto (fun n => cellDirichletInfimum (a n) q betaq) atTop
        (𝓝 ((Gamma.measure U q).toReal)) ∧
      (∀ V : DomainL2 (centeredCube z (3 * r) h3r),
        V ∈ EQ.toClosedForm.domain →
        ∀ Vc : SpatialCoordinates d → ℝ,
        ContinuousOn Vc
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        (V : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Vc →
        (∀ x ∈ frontier q, Vc x = b x) →
        (Gamma.measure U q).toReal ≤ (Gamma.measure V q).toReal) := by
  subst hqcell
  obtain ⟨E0, hE0⟩ := aux_prop_boundary_energy_bound z r h3r S a aC hacont haC UN UNS
    hUNrep hcellsub Bcell hCellEnergy
  have hdom : uBar ∈ EQ.toClosedForm.domain :=
    aux_prop_boundary_limit_mem_domain EQ.toClosedForm S aC hLower UNS uBar hUNL2 E0 hE0
  have hunifl := aux_prop_boundary_uniform_limit z r h3r S UN UNS hUNrep uBar hUNL2 alpha
    (by linarith) Hcell hCellHolder
  obtain ⟨Uc, hUcont, hUae, hunif⟩ := hunifl
  have hface : Gamma.measure uBar
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 :=
    aux_prop_boundary_face_zero hd z r h3r EQ Gamma S aC UNS uBar hUNL2 t ht htd Bcell hBcell
      hCellGrowth E0 hE0 hEnergyMeasures.2.1 hr
  have hcore := aux_prop_boundary_harmonic_core hd hInterp z r hr h3r EQ Gamma S hS a aC hacont
    haC UN UNS hUNrep uBar hUNL2 hcellsub hUNharm t ht hLower hRecovery KN hKN Kstar hKstar hfrac
    hcoercive hcutoffs hEnergyMeasures.2.2 E0 hE0 hdom
  have hharm : ∀ φ : DomainL2 (centeredCube z (3 * r) h3r), φ ∈ Dq →
      EQ.form uBar φ = 0 :=
    aux_prop_boundary_form_zero_of_core hkilled hdom hcore
  have hlim : Tendsto (fun n => cellDirichletInfimum (a n)
      (centeredCube z r hr : Set (SpatialCoordinates d)) betaq) atTop
      (𝓝 ((Gamma.measure uBar (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have hlow := aux_prop_boundary_lower hd z r h3r EQ Gamma S aC UNS uBar hUNL2 t ht htd Bcell
      hBcell hCellGrowth E0 hE0 hEnergyMeasures.2.1 hr δ hδ
    have hup := aux_prop_boundary_upper hd hInterp z r h3r hr EQ Gamma S aC UNS uBar hUNL2 t ht
      htd Bcell hBcell hCellGrowth E0 hE0 hEnergyMeasures.2.1 hS a hacont haC UN hUNrep hcellsub
      hUNharm hRecovery KN hKN Kstar hKstar hfrac hcoercive hcutoffs hEnergyMeasures.1 hdom δ hδ
    filter_upwards [hlow, hup] with n h1 h2
    rw [aux_prop_boundary_dirichlet_identity hd z r hr h3r S a aC hacont haC hell beta betaQ
      hbetaQfun betaq hbetaqfun UN UNS hUNrep hcellsub hUNharm hUNtrace n, Real.dist_eq,
      abs_sub_lt_iff]
    constructor <;> linarith
  have hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) := by
    show Metric.ball z (r / 2) ⊆ Metric.ball z (3 * r / 2)
    exact Metric.ball_subset_ball (by linarith)
  have hbdry : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      Uc x = b x := by
    refine aux_prop_boundary_limit_boundary_value (fun n => (UN n).toFun) Uc beta b _ _
      (frontier_subset_closure.trans (closure_mono hqQ)) hunif ?_ hbetab
    intro n x hx
    refine hUNcellb n (fun _ => ⟨triadicHalf 1, by simp [triadicHalf]⟩) x ?_
    rw [aux_prop_boundary_center_cell z r hr h3r]
    exact hx
  refine ⟨uBar, Uc, hdom, hUcont, hUae, hunif, hbdry, hface, hharm, hlim, ?_⟩
  exact aux_prop_boundary_minimal z r hr h3r EQ Gamma Dq hkilled b
    (fun w hw wc hwc hwae h0 wq hwq =>
      hZeroTrace z r hr hqQ Dq hkilled w hw wc hwc hwae h0 wq hwq)
    uBar Uc hdom hUcont hUae hbdry hface hharm

end SubdiffusiveProcess.Paper
