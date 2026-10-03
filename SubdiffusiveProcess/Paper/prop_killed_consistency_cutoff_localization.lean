module

public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.prop_locality
public import SubdiffusiveProcess.Paper.prop_locality_recovery
public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_19
public import SubdiffusiveProcess.Paper.conv_catalog_cutoffs
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.catalog_cutoff_existence
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane2.BoundaryPackaging
public import SubdiffusiveProcess.Lane2.NativeBridge
public import SubdiffusiveProcess.Lane2.ResponseMarkov
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane2.MeshError
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Sobolev.EvenReflectionGraph

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem prop_killed_consistency_cutoff_localization
    (d : ℕ) (hd : 2 ≤ d)
    (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (SQ : ResponseSpace (centeredCube zQ R hR0))
    (Sq : ResponseSpace (centeredCube zq r hr0))
    (hSQ : SQ.space = killedSobolevGraph (centeredCube zQ R hR0))
    (hSq : Sq.space = killedSobolevGraph (centeredCube zq r hr0))
    (aQ : ℕ → PositiveCoefficient (centeredCube zQ R hR0))
    (aq : ℕ → PositiveCoefficient (centeredCube zq r hr0))
    (hcoeff : ∀ n, ((aQ n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))]
        ((aq n).val : SpatialCoordinates d → ℝ))
    (EQ : DirichletForm.ClosedForm
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (Eq : DirichletForm.ClosedForm
      (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))))
    (hQrecovery : ∀ v ∈ EQ.domain, ∃ vN : ℕ → SQ.space,
      Tendsto (fun n => ((vN n).val.1,
        (responseForm SQ (aQ n) (vN n) (vN n) : EReal))) atTop
        (𝓝 (v, (EQ.energy v : EReal))))
    (hqlower : ∀ (vN : ℕ → Sq.space) (v : DomainL2 (centeredCube zq r hr0)),
      (∀ f : DomainL2 (centeredCube zq r hr0),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop
          (𝓝 (inner ℝ f v))) →
      (Eq.energy v : EReal) ≤
        liminf (fun n => (responseForm Sq (aq n) (vN n) (vN n) : EReal)) atTop)
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : SQ.space,
      cubeFractionalL2Seminorm hd zQ R hR0 Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : SQ.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube zQ R hR0 : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd zQ R hR0 Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        KN n * responseForm SQ (aQ n) w w)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
        closure O ⊆ (centeredCube zQ R hR0 : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → SQ.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n)
            (closure (centeredCube zQ R hR0 : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))]
              chic n ∧
          (∀ x ∈ (centeredCube zQ R hR0 : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube zQ R hR0 : Set (SpatialCoordinates d)),
            x ∉ O → chic n x = 0) ∧
          responseForm SQ (aQ n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube zQ R hR0 : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((aQ n).val y *
                ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (w : DomainL2 (centeredCube zQ R hR0)) (hw : w ∈ EQ.domain)
    (hwrep : ∃ wc : SpatialCoordinates d → ℝ, Continuous wc ∧
      HasCompactSupport wc ∧
      tsupport wc ⊆ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∧
      (w : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))] wc)
    (hcutoffProduct :
      ∀ (v : DomainL2 (centeredCube zQ R hR0))
        (vc : SpatialCoordinates d → ℝ),
        v ∈ EQ.domain →
        Continuous vc → HasCompactSupport vc →
        tsupport vc ⊆ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) →
        (v : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))] vc →
        ∀ (vN : ℕ → SQ.space),
          Tendsto (fun n => ((vN n).val.1,
            (responseForm SQ (aQ n) (vN n) (vN n) : EReal))) atTop
            (𝓝 (v, (EQ.energy v : EReal))) →
          ∃ (chi : ℕ → SQ.space) (chic : ℕ → SpatialCoordinates d → ℝ)
            (V : Set (SpatialCoordinates d)) (vNq : ℕ → Sq.space)
            (err : ℕ → ℝ),
            IsOpen V ∧
            tsupport vc ⊆ V ∧
            (∀ n,
              ContinuousOn (chic n)
                (closure (centeredCube zQ R hR0 : Set (SpatialCoordinates d))) ∧
              ((chi n).val.1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict
                  (centeredCube zQ R hR0 : Set (SpatialCoordinates d))] chic n ∧
              (∀ x ∈ V, chic n x = 1) ∧
              (∀ x ∈ (centeredCube zQ R hR0 : Set (SpatialCoordinates d)),
                x ∉ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) →
                  chic n x = 0)) ∧
            (∀ n,
              ((zeroExtensionSobolevData hqQ (vNq n).val).1 :
                SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))]
                (fun x => chic n x * (vN n).val.1 x)) ∧
            (∀ n (i : Fin d),
              ((zeroExtensionSobolevData hqQ (vNq n).val).2 i :
                SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))]
                (fun x => (chi n).val.2 i x * (vN n).val.1 x +
                  chic n x * (vN n).val.2 i x)) ∧
            Tendsto (fun n => (vNq n).val.1) atTop
              (𝓝 (domainLpRestrict hqQ v)) ∧
            (∀ n, 0 ≤ err n) ∧
            Tendsto err atTop (𝓝 0) ∧
            (∀ ε : ℝ, 0 < ε → ∀ n,
              (responseForm Sq (aq n) (vNq n) (vNq n) : EReal) ≤
                (((1 + ε) * responseForm SQ (aQ n) (vN n) (vN n) : ℝ) : EReal) +
                  (((1 + ε⁻¹) * err n : ℝ) : EReal))) :
    ∃ wq : DomainL2 (centeredCube zq r hr0),
      wq ∈ Eq.domain ∧ zeroExtensionLp hqQ wq = w ∧
      (Eq.energy wq : EReal) ≤ (EQ.energy w : EReal) := by
  obtain ⟨wc, hwc_cont, hwc_supp, hwc_tsupp, hwc⟩ := hwrep
  obtain ⟨vN, hvN⟩ := hQrecovery w hw
  obtain ⟨chi, chic, V, vNq, err, hV, hVsup, hchi, hzero, hgrad,
    hvNq, herr_nonneg, herr_zero, henergy⟩ :=
    hcutoffProduct w wc hw hwc_cont hwc_supp hwc_tsupp hwc vN hvN
  let wq : DomainL2 (centeredCube zq r hr0) := domainLpRestrict hqQ w
  have hwq_ext : zeroExtensionLp hqQ wq = w := by
    apply Lp.ext
    have hwq_ae := domainLpRestrict_coeFn hqQ w
    have hwq_ae' :=
      ae_restrict_of_ae (s := (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
        ((ae_restrict_iff' (centeredCube zq r hr0).isOpen.measurableSet).mp hwq_ae)
    filter_upwards [zeroExtensionLp_coeFn hqQ wq, hwq_ae', hwc] with x hxext hxq hxc
    rw [hxext]
    by_cases hxin : x ∈ (centeredCube zq r hr0 : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem hxin]
      exact hxq hxin
    · rw [Set.indicator_of_notMem hxin]
      have hxc0 : wc x = 0 := image_eq_zero_of_notMem_tsupport (fun hxt => hxin (hwc_tsupp hxt))
      rw [hxc, hxc0]
  have hweak : ∀ f : DomainL2 (centeredCube zq r hr0),
      Tendsto (fun n => inner ℝ f (vNq n).val.1) atTop
        (𝓝 (inner ℝ f wq)) := by
    intro f
    have hcont : Continuous (fun x : DomainL2 (centeredCube zq r hr0) => inner ℝ f x) :=
      continuous_const.inner continuous_id
    simpa [wq, Function.comp_def] using (hcont.tendsto wq).comp hvNq
  have hlow : (Eq.energy wq : EReal) ≤
      liminf (fun n => (responseForm Sq (aq n) (vNq n) (vNq n) : EReal)) atTop :=
    hqlower vNq wq hweak
  have hEQenergy : EQ.energy w = (EQ.form w w : EReal) := EQ.energy_of_mem hw
  have hrespQ : Tendsto
      (fun n => (responseForm SQ (aQ n) (vN n) (vN n) : EReal)) atTop
      (𝓝 (EQ.energy w : EReal)) := by
    simpa only [Prod.snd] using! (continuous_snd.tendsto (w, (EQ.energy w : EReal))).comp hvN
  have herrE : Tendsto (fun n => (err n : EReal)) atTop (𝓝 (0 : EReal)) :=
    EReal.tendsto_coe.mpr herr_zero
  have hA_bdd : IsBoundedUnder (· ≥ ·) atTop
      (fun n => (responseForm Sq (aq n) (vNq n) (vNq n) : EReal)) := by
    change ∃ b : EReal, ∀ᶠ n : ℕ in atTop,
      (responseForm Sq (aq n) (vNq n) (vNq n) : EReal) ≥ b
    refine ⟨0, Filter.Eventually.of_forall ?_⟩
    intro n
    exact EReal.coe_nonneg.mpr (responseForm_nonneg Sq (aq n) (vNq n))
  have hliminf_bound : ∀ ε : ℝ, 0 < ε →
      liminf (fun n => (responseForm Sq (aq n) (vNq n) (vNq n) : EReal)) atTop ≤
        (((1 + ε) * EQ.form w w : ℝ) : EReal) := by
    intro ε hε
    have hrespQ' : Tendsto
        (fun n => responseForm SQ (aQ n) (vN n) (vN n)) atTop
        (𝓝 (EQ.form w w)) := by
      apply EReal.tendsto_coe.mp
      simpa only [hEQenergy] using hrespQ
    have hCQ : Tendsto
        (fun n => (1 + ε) * responseForm SQ (aQ n) (vN n) (vN n)) atTop
        (𝓝 ((1 + ε) * EQ.form w w)) :=
      tendsto_const_nhds.mul hrespQ'
    have hCE : Tendsto (fun n => (1 + ε⁻¹) * err n) atTop
        (𝓝 ((1 + ε⁻¹) * 0)) := tendsto_const_nhds.mul herr_zero
    have hCreal : Tendsto
        (fun n => (1 + ε) * responseForm SQ (aQ n) (vN n) (vN n) +
          (1 + ε⁻¹) * err n) atTop
        (𝓝 ((1 + ε) * EQ.form w w + (1 + ε⁻¹) * 0)) := hCQ.add hCE
    have hC : Tendsto
        (fun n => (((1 + ε) * responseForm SQ (aQ n) (vN n) (vN n) +
          (1 + ε⁻¹) * err n : ℝ) : EReal)) atTop
        (𝓝 (((1 + ε) * EQ.form w w + (1 + ε⁻¹) * 0 : ℝ) : EReal)) :=
      EReal.tendsto_coe.mpr hCreal
    have hle : ∀ n : ℕ,
        (responseForm Sq (aq n) (vNq n) (vNq n) : EReal) ≤
          (((1 + ε) * responseForm SQ (aQ n) (vN n) (vN n) +
            (1 + ε⁻¹) * err n : ℝ) : EReal) := by
      simpa only [EReal.coe_add, EReal.coe_mul] using henergy ε hε
    have hlim := Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)
      hA_bdd hC.isCoboundedUnder_ge
    rw [hC.liminf_eq] at hlim
    simpa only [mul_zero, add_zero] using hlim
  have hupper : (↑(2 : ℝ) : EReal) * (↑(EQ.form w w) : EReal) < ⊤ := by
    simpa only [EReal.coe_mul] using EReal.coe_lt_top (2 * EQ.form w w)
  have hEq_lt_top : Eq.energy wq < ⊤ := by
    have h₁ := hlow.trans (hliminf_bound 1 (by norm_num))
    norm_num at h₁
    exact h₁.trans_lt hupper
  have hwqdom : wq ∈ Eq.domain := Eq.mem_domain_of_energy_lt_top hEq_lt_top
  refine ⟨wq, ?_, hwq_ext, ?_⟩
  · exact hwqdom
  · refine le_of_forall_gt_imp_ge_of_dense ?_
    intro a ha
    obtain ⟨c, hEc, hca⟩ := EReal.exists_between_coe_real ha
    rw [hEQenergy] at hEc
    have hreal : 0 ≤ EQ.form w w := EQ.form_nonneg w hw
    by_cases heq : EQ.form w w = 0
    · have hb := hlow.trans (hliminf_bound 1 (by norm_num))
      simp [heq] at hb
      have hzero : (0 : EReal) < (c : EReal) := by simpa [heq] using hEc
      exact hb.trans (le_of_lt (hzero.trans hca))
    · have hpos : 0 < EQ.form w w := lt_of_le_of_ne hreal (Ne.symm heq)
      have hce : EQ.form w w < c := EReal.coe_lt_coe_iff.mp hEc
      let ε : ℝ := (c - EQ.form w w) / (2 * EQ.form w w)
      have hε : 0 < ε := by
        dsimp [ε]
        exact div_pos (sub_pos.mpr hce)
          (mul_pos (by norm_num) hpos)
      have hmul : (1 + ε) * EQ.form w w < c := by
        dsimp [ε]
        field_simp
        nlinarith [hce]
      have hb := hlow.trans (hliminf_bound ε hε)
      exact hb.trans (le_of_lt ((EReal.coe_lt_coe_iff.mpr hmul).trans hca))

end Paper
