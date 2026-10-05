module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.TietzeExtension

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}



theorem lem_truncation_family
    (d : ℕ) (_hd : 2 ≤ d)
    (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (EQ : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure EQ.toClosedForm)
    (hnc : _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions EQ)
    (halg : _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra EQ.toClosedForm)
    (hreg : ∃ C : Set (DomainL2 (centeredCube zQ R hR0)),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn EQ.toClosedForm
        (centeredCube zQ R hR0 : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube zQ R hR0)))
    (hkilled : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain EQ.toClosedForm
      (centeredCube zq r hr0 : Set (SpatialCoordinates d)) Dq)
    (v : DomainL2 (centeredCube zQ R hR0)) (hv : v ∈ EQ.toClosedForm.domain)
    (vc : SpatialCoordinates d → ℝ)
    (hvccont : ContinuousOn vc
      (closure (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (hvrep : (v : SpatialCoordinates d → ℝ)
      =ᵐ[(volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))] vc)
    (hvanish : ∀ x ∈ frontier (centeredCube zq r hr0 : Set (SpatialCoordinates d)),
      vc x = 0)
    (hBH_chain : ∀ T : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K T) → T 0 = 0 →
      ∀ Tderiv : ℝ → ℝ, Measurable Tderiv →
      (∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s) →
      ∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ EQ.toClosedForm.domain →
      ((w : SpatialCoordinates d → ℝ)
        =ᵐ[(volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))]
          fun x => T (vc x)) →
      ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        (Gamma.measure w B).toReal =
          ∫ x in B, (Tderiv (vc x)) ^ 2 ∂(Gamma.measure v)) :
    ∃ w : ℝ → DomainL2 (centeredCube zQ R hR0),
      ∀ ε : ℝ, 0 < ε →
        w ε ∈ Dq ∧
        (∀ B : Set (SpatialCoordinates d), MeasurableSet B →
          Gamma.measure (w ε) B =
            Gamma.measure v (B ∩ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∩
              {x : SpatialCoordinates d | ε < |vc x|})) ∧
        ((w ε : SpatialCoordinates d → ℝ)
          =ᵐ[(volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))]
            fun x => _root_.SubdiffusiveProcess.DirichletForm.truncation ε
              (Set.indicator
                (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d))) vc x)) ∧
      (∀ᵐ x ∂(volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))),
          |(w ε : SpatialCoordinates d → ℝ) x -
            Set.indicator
              (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d))) vc x| ≤ ε) := by
  classical
  let Qs : Set (SpatialCoordinates d) := centeredCube zQ R hR0
  let qs : Set (SpatialCoordinates d) := centeredCube zq r hr0
  let μ : Measure (SpatialCoordinates d) := volume.restrict Qs
  have hQopen : IsOpen Qs := (centeredCube zQ R hR0).isOpen
  have hqopen : IsOpen qs := (centeredCube zq r hr0).isOpen
  have hQc : IsCompact (closure Qs) :=
    lane2_isCompact_closure_centeredCube zQ hR0
  have hqc : IsCompact (closure qs) :=
    lane2_isCompact_closure_centeredCube zq hr0
  have hqQ' : qs ⊆ Qs := hqQ
  have hqclQ : closure qs ⊆ closure Qs := closure_mono hqQ'
  let : CompactSpace (closure Qs) := isCompact_iff_compactSpace.mp hQc
  let fQ : C(closure Qs, ℝ) :=
    ⟨fun x => vc x, hvccont.domRestrict⟩
  let fQb : BoundedContinuousFunction (closure Qs) ℝ :=
    BoundedContinuousFunction.mkOfCompact fQ
  obtain ⟨V, hVnorm, hVeq⟩ :=
    BoundedContinuousFunction.exists_norm_eq_domRestrict_eq_of_closed fQb isClosed_closure
  have hVcont : Continuous (V : SpatialCoordinates d → ℝ) := V.continuous
  have hVeq_vc : ∀ x ∈ closure Qs, V x = vc x := by
    intro x hx
    have hx' := congrArg
      (fun f : BoundedContinuousFunction (closure Qs) ℝ => f ⟨x, hx⟩) hVeq
    simpa [fQb, fQ] using! hx'
  have hQmeas : MeasurableSet Qs := hQopen.measurableSet
  have hVrep : (v : SpatialCoordinates d → ℝ) =ᵐ[μ] V := by
    filter_upwards [hvrep, ae_restrict_mem hQmeas] with x hx hxQ
    rw [hx]
    exact (hVeq_vc x (subset_closure hxQ)).symm
  let Φ : ℝ → ℝ := fun t => Real.smoothTransition (2 * t - 1 / 2)
  have hΦ : ContDiff ℝ 1 Φ := by
    dsimp [Φ]
    exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hΦ0 : Φ 0 = 0 := by
    dsimp [Φ]
    exact Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hmain : ∀ ε : ℝ, 0 < ε → ∃ w : DomainL2 (centeredCube zQ R hR0),
      w ∈ Dq ∧
      (∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        Gamma.measure w B = Gamma.measure v
          (B ∩ qs ∩ {x : SpatialCoordinates d | ε < |vc x|})) ∧
      ((w : SpatialCoordinates d → ℝ) =ᵐ[μ]
        fun x => _root_.SubdiffusiveProcess.DirichletForm.truncation ε (Set.indicator (closure qs) vc x)) ∧
      (∀ᵐ x ∂μ,
        |(w : SpatialCoordinates d → ℝ) x - Set.indicator (closure qs) vc x| ≤ ε) := by
    intro ε hε
    let T : ℝ → ℝ := _root_.SubdiffusiveProcess.DirichletForm.truncation ε
    have hε0 : 0 ≤ ε := hε.le
    have hTnc : _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T := by
      exact _root_.SubdiffusiveProcess.DirichletForm.isIsNormalContraction_truncation hε0
    have hT0 : T 0 = 0 := by
      exact _root_.SubdiffusiveProcess.DirichletForm.truncation_zero ε
    have hTlip : LipschitzWith (1 : ℝ≥0) T := by
      intro x y
      simpa [edist_dist, Real.dist_eq] using hTnc.dist_le x y
    have hTcont : Continuous T := hTlip.continuous
    have hKc : IsCompact ({x : SpatialCoordinates d | ε ≤ |V x|} ∩ closure qs) :=
      _root_.SubdiffusiveProcess.DirichletForm.isCompact_levelSet hVcont hqc ε
    have hVvanish : ∀ x ∈ frontier qs, V x = 0 := by
      intro x hx
      have hxqcl : x ∈ closure qs := frontier_subset_closure hx
      rw [hVeq_vc x (hqclQ hxqcl), hvanish x hx]
    have hKq : ({x : SpatialCoordinates d | ε ≤ |V x|} ∩ closure qs) ⊆ qs :=
      _root_.SubdiffusiveProcess.DirichletForm.levelSet_subset hqopen hVvanish hε
    obtain ⟨θ, hθcont, hθcs, hθsub, hθnn, hθle1, hθone⟩ :=
      _root_.SubdiffusiveProcess.DirichletForm.exists_continuous_plateau hKc hqopen hKq
    obtain ⟨C, hC⟩ := hreg
    obtain ⟨θ0, hθ0C, g, hgcont, hgcs, hgsupp, hθ0rep, hclose⟩ :=
      hC.denseUniform θ hθcont hθcs (hθsub.trans hqQ') (1 / 4)
        (by norm_num : (0 : ℝ) < 1 / 4)
    obtain ⟨θL, hθLcore, hθLrep⟩ :=
      halg.comp_mem θ0 (hC.memCoreOn θ0 hθ0C).memCore Φ hΦ hΦ0
    have hθLrep' : (θL : SpatialCoordinates d → ℝ) =ᵐ[μ]
        fun x => Φ (g x) := by
      exact hθLrep.trans (by
        simpa [Function.comp_def] using hθ0rep.fun_comp Φ)
    have hΦgcont : Continuous (fun x : SpatialCoordinates d => Φ (g x)) :=
      hΦ.continuous.comp hgcont
    have hΦzero_theta : ∀ x : SpatialCoordinates d, θ x = 0 → Φ (g x) = 0 := by
      intro x hθx
      have hcx := hclose x
      rw [hθx] at hcx
      have hglt : g x < (1 / 4 : ℝ) := by
        have := (abs_lt.mp hcx).2
        linarith
      dsimp [Φ]
      exact Real.smoothTransition.zero_of_nonpos (by linarith)
    have hΦg_supp : Function.support (fun x : SpatialCoordinates d => Φ (g x)) ⊆
        Function.support θ := by
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro hθ0
      apply hx
      exact hΦzero_theta x hθ0
    have hΦgcs : HasCompactSupport (fun x : SpatialCoordinates d => Φ (g x)) :=
      hθcs.mono hΦg_supp
    have hΦgsub : tsupport (fun x : SpatialCoordinates d => Φ (g x)) ⊆ qs :=
      (closure_mono hΦg_supp).trans hθsub
    have hθLq : EQ.toClosedForm.MemCoreOn qs θL := by
      refine ⟨hθLcore.mem_domain, ?_⟩
      exact ⟨fun x => Φ (g x), hΦgcont, hΦgcs, hΦgsub, hθLrep'⟩
    have hΦone : ∀ x ∈ {y : SpatialCoordinates d | ε ≤ |V y|} ∩ closure qs,
        Φ (g x) = 1 := by
      intro x hx
      have hcx := hclose x
      have hθx := hθone x hx
      have hglo : (3 / 4 : ℝ) < g x := by
        rw [hθx] at hcx
        have := (abs_lt.mp hcx).1
        linarith
      dsimp [Φ]
      apply Real.smoothTransition.one_of_one_le
      linarith
    have hΦzero : ∀ x ∉ qs, Φ (g x) = 0 := by
      intro x hx
      apply hΦzero_theta x
      by_contra hθ0
      apply hx
      exact hθsub (subset_closure (Function.mem_support.mpr hθ0))
    let W : BoundedContinuousFunction (SpatialCoordinates d) ℝ :=
      V.comp T hTlip
    let u : DomainL2 (centeredCube zQ R hR0) :=
      (BoundedContinuousFunction.toLp 2 μ ℝ) W
    have hu_rep : (u : SpatialCoordinates d → ℝ) =ᵐ[μ]
        fun x => T (V x) := by
      have h := BoundedContinuousFunction.coeFn_toLp 2 μ ℝ W
      simpa [u, W, BoundedContinuousFunction.comp] using h
    have hu_rep_v : (u : SpatialCoordinates d → ℝ) =ᵐ[μ]
        fun x => T (v x) := by
      filter_upwards [hu_rep, hVrep] with x hx hv
      rw [hx, hv]
    have hu_dom : u ∈ EQ.toClosedForm.domain :=
      (hnc.operatesOn T hTnc v hv u hu_rep_v).1
    obtain ⟨wε, hwεcore, hwεeq⟩ :=
      halg.mul_mem_of_bounded qs u θL hu_dom
        (fun x => T (V x)) (hTcont.comp hVcont) hu_rep
        (by
          refine ⟨‖W‖, fun x => ?_⟩
          simpa [W, Real.norm_eq_abs] using W.norm_coe_le_norm x)
        hθLq (fun x => Φ (g x)) hΦgcont hθLrep'
    have hwεdom : wε ∈ EQ.toClosedForm.domain := hwεcore.mem_domain
    let F : SpatialCoordinates d → ℝ := fun x => T (V x) * Φ (g x)
    have hFcont : Continuous F :=
      (hTcont.comp hVcont).mul hΦgcont
    have hF_supp : Function.support F ⊆ Function.support (fun x => Φ (g x)) := by
      intro x hx
      simp only [F, Function.mem_support] at hx ⊢
      intro hφ0
      apply hx
      simp [hφ0]
    have hFts : tsupport F ⊆ qs :=
      (closure_mono hF_supp).trans hΦgsub
    have hVeq_q : ∀ x ∈ qs, V x = vc x := by
      intro x hx
      exact hVeq_vc x (subset_closure (hqQ' hx))
    have hprod_q : ∀ x ∈ qs, F x = T (V x) := by
      intro x hx
      by_cases hxe : ε ≤ |vc x|
      · have hxK : x ∈ {y : SpatialCoordinates d | ε ≤ |V y|} ∩ closure qs := by
          refine ⟨?_, subset_closure hx⟩
          simpa [hVeq_q x hx] using hxe
        simp [F, hΦone x hxK]
      · have hzero : T (V x) = 0 := by
          rw [hVeq_q x hx]
          exact _root_.SubdiffusiveProcess.DirichletForm.truncation_of_abs_le (le_of_not_ge hxe)
        simp [F, hzero]
    have htarget : (wε : SpatialCoordinates d → ℝ) =ᵐ[μ]
        fun x => T (Set.indicator (closure qs) vc x) := by
      filter_upwards [hwεeq, ae_restrict_mem hQmeas] with x hx hxQ
      rw [hx]
      by_cases hxq : x ∈ qs
      · have hprod := hprod_q x hxq
        calc
          T (V x) * Φ (g x) = T (V x) := by simpa [F] using hprod
          _ = T (Set.indicator (closure qs) vc x) := by
            rw [Set.indicator_of_mem (subset_closure hxq)]
            rw [hVeq_q x hxq]
      · have hφ0 := hΦzero x hxq
        rw [hφ0, mul_zero]
        by_cases hxcl : x ∈ closure qs
        · have hxfr : x ∈ frontier qs := by
            rw [← closure_sdiff_interior, hqopen.interior_eq]
            exact ⟨hxcl, hxq⟩
          rw [Set.indicator_of_mem hxcl, hvanish x hxfr, hT0]
        · rw [Set.indicator_of_notMem hxcl, hT0]
    have hloc : (wε : SpatialCoordinates d → ℝ) =ᵐ[μ.restrict qs]
        (u : SpatialCoordinates d → ℝ) := by
      filter_upwards [ae_restrict_of_ae hwεeq, ae_restrict_of_ae hu_rep,
        ae_restrict_mem hqopen.measurableSet] with x hx hw hxq
      rw [hx, hw]
      simpa [F] using hprod_q x hxq
    have hloc_meas : (Gamma.measure wε).restrict qs =
        (Gamma.measure u).restrict qs :=
      Gamma.locality wε hwεdom u hu_dom qs hqopen hloc
    have h0c : Gamma.measure wε (tsupport F)ᶜ = 0 :=
      Gamma.measure_compl_tsupport wε hwεdom F hFcont hwεeq
    have hmeasure : ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        Gamma.measure wε B = Gamma.measure v
          (B ∩ qs ∩ {x : SpatialCoordinates d | ε < |vc x|}) := by
      intro B hB
      have hA : Gamma.measure wε B = Gamma.measure wε (B ∩ qs) := by
        have hzero : Gamma.measure wε (B \ qs) = 0 := by
          refine measure_mono_null (s := B \ qs) (t := (tsupport F)ᶜ) ?_ h0c
          intro x hx hxs
          exact hx.2 (hFts hxs)
        have hsplit : Gamma.measure wε (B ∩ qs) + Gamma.measure wε (B \ qs) =
            Gamma.measure wε B :=
          measure_inter_add_sdiff B hqopen.measurableSet
        rw [hzero, add_zero] at hsplit
        exact hsplit.symm
      have hBq : Gamma.measure wε (B ∩ qs) = Gamma.measure u (B ∩ qs) := by
        have h := congrArg (fun ν : Measure (SpatialCoordinates d) => ν B) hloc_meas
        change (Gamma.measure wε).restrict qs B = (Gamma.measure u).restrict qs B at h
        simpa [Measure.restrict_apply hB] using h
      have hBqmeas : MeasurableSet (B ∩ qs) := hB.inter hqopen.measurableSet
      let Tderiv : ℝ → ℝ := fun s => if ε < |s| then 1 else 0
      have hTderiv_meas : Measurable Tderiv := by
        dsimp [Tderiv]
        exact Measurable.ite
          (measurableSet_lt measurable_const measurable_abs)
          measurable_const measurable_const
      have hTderiv_ae : ∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s := by
        rw [ae_iff]
        refine measure_mono_null
          (s := {s : ℝ | ¬ HasDerivAt T (Tderiv s) s})
          (t := ({-ε, ε} : Set ℝ)) ?_ ?_
        · intro s hs
          by_cases hinside : |s| < ε
          · exact (hs (by
              have hnot : ¬ ε < |s| := not_lt.mpr (le_of_lt hinside)
              simpa [T, Tderiv, hnot] using
                (_root_.SubdiffusiveProcess.DirichletForm.hasDerivAt_truncation_of_abs_lt hinside))).elim
          · have hge : ε ≤ |s| := le_of_not_gt hinside
            by_cases heq : |s| = ε
            · rcases (abs_eq hε0).mp heq with hspos | hsneg
              · simp [hspos]
              · simp [hsneg]
            · have hgt : ε < |s| := lt_of_le_of_ne hge (Ne.symm heq)
              have hder : HasDerivAt T 1 s := by
                by_cases hs0 : 0 ≤ s
                · rw [abs_of_nonneg hs0] at hgt
                  exact _root_.SubdiffusiveProcess.DirichletForm.hasDerivAt_truncation_of_lt hε0 hgt
                · have hsneg : s < 0 := lt_of_not_ge hs0
                  rw [abs_of_neg hsneg] at hgt
                  exact _root_.SubdiffusiveProcess.DirichletForm.hasDerivAt_truncation_of_lt_neg hε0 (by linarith)
              exact (hs (by simpa [T, Tderiv, hgt] using hder)).elim
        · exact (Set.finite_insert.mpr (Set.finite_singleton ε)).measure_zero volume
      have hu_rep_vc : (u : SpatialCoordinates d → ℝ) =ᵐ[μ] fun x => T (vc x) := by
        filter_upwards [hu_rep, ae_restrict_mem hQmeas] with x hx hxQ
        rw [hx, hVeq_vc x (subset_closure hxQ)]
      have hchain : (Gamma.measure u (B ∩ qs)).toReal =
          ∫ x in B ∩ qs, (Tderiv (V x)) ^ 2 ∂(Gamma.measure v) := by
        rw [hBH_chain T ⟨1, hTlip⟩ hT0 Tderiv hTderiv_meas hTderiv_ae u hu_dom
          hu_rep_vc (B ∩ qs) hBqmeas]
        refine setIntegral_congr_fun hBqmeas (fun x hx => ?_)
        rw [hVeq_q x hx.2]
      have hlevelmeas : MeasurableSet {x : SpatialCoordinates d | ε < |V x|} :=
        measurableSet_lt measurable_const hVcont.measurable.abs
      have hHint : (fun x : SpatialCoordinates d => (Tderiv (V x)) ^ 2) =
          Set.indicator {x : SpatialCoordinates d | ε < |V x|} (fun _ => (1 : ℝ)) := by
        funext x
        by_cases hx : ε < |V x| <;> simp [Tderiv, hx]
      have hD : (∫ x in B ∩ qs, (Tderiv (V x)) ^ 2 ∂(Gamma.measure v)) =
          (Gamma.measure v (B ∩ qs ∩ {x : SpatialCoordinates d | ε < |V x|})).toReal := by
        rw [hHint]
        rw [MeasureTheory.setIntegral_indicator hlevelmeas]
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
        rfl
      have hlevel_eq : B ∩ qs ∩ {x : SpatialCoordinates d | ε < |vc x|} =
          B ∩ qs ∩ {x : SpatialCoordinates d | ε < |V x|} := by
        ext x
        by_cases hx : x ∈ qs
        · constructor <;> intro h
          · exact ⟨⟨h.1.1, h.1.2⟩, by simpa [hVeq_q x hx] using h.2⟩
          · exact ⟨⟨h.1.1, h.1.2⟩, by simpa [hVeq_q x hx] using h.2⟩
        · simp [hx]
      have hreal : (Gamma.measure wε B).toReal =
          (Gamma.measure v (B ∩ qs ∩ {x : SpatialCoordinates d | ε < |vc x|})).toReal := by
        rw [hA, hBq, hchain, hD, hlevel_eq]
      have hfin1 : Gamma.measure wε B ≠ ⊤ :=
        ne_top_of_le_ne_top (ne_of_lt (Gamma.measure_univ_lt_top wε hwεdom))
          (measure_mono (Set.subset_univ B))
      have hfin2 : Gamma.measure v (B ∩ qs ∩ {x : SpatialCoordinates d | ε < |vc x|}) ≠ ⊤ :=
        ne_top_of_le_ne_top (ne_of_lt (Gamma.measure_univ_lt_top v hv))
          (measure_mono (Set.subset_univ _))
      exact (ENNReal.toReal_eq_toReal_iff' hfin1 hfin2).mp (by simpa using hreal)
    refine ⟨wε, hkilled.memCoreOn_mem wε hwεcore, hmeasure, htarget, ?_⟩
    filter_upwards [htarget] with x hx
    rw [hx]
    exact _root_.SubdiffusiveProcess.DirichletForm.abs_truncation_sub_self_le hε0 _
  refine ⟨fun ε => if h : 0 < ε then Classical.choose (hmain ε h) else 0, ?_⟩
  intro ε hε
  simp only [dite_eq_left hε]
  exact Classical.choose_spec (hmain ε hε)

end SubdiffusiveProcess.Paper
