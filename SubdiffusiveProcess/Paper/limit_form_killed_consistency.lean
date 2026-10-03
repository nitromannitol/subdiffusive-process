module

public import SubdiffusiveProcess.Paper.limit_form_localized_recovery_support
public import SubdiffusiveProcess.Paper.killed_restriction_compact_support
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Sobolev.WeakEquationRestrict
public import SubdiffusiveProcess.Lane2.KilledTest

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess Homogenization
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Localization supplies the reverse killed energy bound on the compact core. -/
theorem aux_limit_form_killed_consistency_core
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
    (GQ : DomainL2 (centeredCube zQ R hR0) →L[ℝ] DomainL2 (centeredCube zQ R hR0))
    (Gq : DomainL2 (centeredCube zq r hr0) →L[ℝ] DomainL2 (centeredCube zq r hr0))
    (LQ : aux_limit_form_package_limit_side d hd zQ R hR0 SQ GQ aQ)
    (Lq : aux_limit_form_package_limit_side d hd zq r hr0 Sq Gq aq)
    (w : DomainL2 (centeredCube zQ R hR0)) (hw : w ∈ LQ.form.domain)
    (wc : SpatialCoordinates d → ℝ) (hwc : Continuous wc) (hcompact : HasCompactSupport wc)
    (hsupport : tsupport wc ⊆ (centeredCube zq r hr0 : Set (SpatialCoordinates d)))
    (hwrep : (w : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))] wc) :
    ∃ wq : DomainL2 (centeredCube zq r hr0), wq ∈ Lq.form.domain ∧
      zeroExtensionLp hqQ wq = w ∧ Lq.form.energy wq ≤ LQ.form.energy w := by
  have hwG : w ∈ limitFormDomain GQ := by
    change limitFormEnergy GQ w < ⊤
    rw [← LQ.energy_eq]
    exact (LQ.form.toClosedForm.energy_lt_top_iff w).mpr hw
  obtain ⟨Y, K, hK, hKq, hY, hZero⟩ := limit_form_localized_recovery_support d hd zQ R hR0
    SQ hSQ aQ GQ LQ (centeredCube zq r hr0) (centeredCube zq r hr0).isOpen hqQ
    w hwG wc hwc hcompact hsupport hwrep
  have hmem : ∀ n, sobolevDataRestrict hqQ (Y n).val ∈ Sq.space := by
    intro n
    rw [hSq]
    exact killed_restriction_compact_support hqQ
      (lane2_isOpenBoundedConvexDomain_centeredCube zq hr0) K hK hKq
      (Y n).val (SQ.le_weak (Y n).property) (hZero n)
  let Yq : ℕ → Sq.space := fun n => ⟨sobolevDataRestrict hqQ (Y n).val, hmem n⟩
  let wq := domainLpRestrict hqQ w
  have hlip : LipschitzWith 1 (fun f : DomainL2 (centeredCube zQ R hR0) => domainLpRestrict hqQ f) := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    have hs : domainLpRestrict hqQ (f - g) = domainLpRestrict hqQ f - domainLpRestrict hqQ g := by
      have hadd : domainLpRestrict hqQ (f + (-1 : ℝ) • g) =
          domainLpRestrict hqQ f + domainLpRestrict hqQ ((-1 : ℝ) • g) := by
        simpa using! domainLpRestrict_add hqQ f ((-1 : ℝ) • g)
      have hsmul : domainLpRestrict hqQ ((-1 : ℝ) • g) =
          (-1 : ℝ) • domainLpRestrict hqQ g := by
        simpa using! domainLpRestrict_smul hqQ (-1 : ℝ) g
      rw [sub_eq_add_neg, ← neg_one_smul ℝ g, hadd, hsmul]
      simp only [neg_one_smul, sub_eq_add_neg]
    rw [dist_eq_norm, dist_eq_norm, ← hs]
    simpa only [NNReal.coe_one, one_mul] using domainLpRestrict_norm_le hqQ (f - g)
  have hYq : Tendsto (fun n => (Yq n).val.1) atTop (𝓝 wq) :=
    (hlip.continuous.tendsto w).comp hY.fst_nhds
  obtain ⟨_, hqlower, _⟩ := aux_limit_form_package_mosco_free d hd zq r hr0 Sq Gq aq
    Lq.response Lq.response_eq Lq.response_tendsto
  have hlow := hqlower Yq wq (fun f => tendsto_const_nhds.inner hYq)
  have henergy : ∀ n, (responseForm Sq (aq n) (Yq n) (Yq n) : EReal) ≤
      (responseForm SQ (aQ n) (Y n) (Y n) : EReal) := by
    intro n
    apply EReal.coe_le_coe_iff.mpr
    exact sobolevCoefficientForm_restrict_le hqQ (aQ n) (aq n) (hcoeff n) (Y n).val
  have hupper : limitFormEnergy Gq wq ≤ limitFormEnergy GQ w := by
    have he := hlow.trans (liminf_le_liminf (Eventually.of_forall henergy))
    rwa [hY.snd_nhds.liminf_eq] at he
  have hdom : wq ∈ Lq.form.domain := by
    apply Lq.form.toClosedForm.mem_domain_of_energy_lt_top
    rw [Lq.energy_eq]
    exact hupper.trans_lt hwG
  have hext : zeroExtensionLp hqQ wq = w := by
    apply Lp.ext
    have hre : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
        x ∈ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) → wq x = w x :=
      (ae_restrict_iff' (centeredCube zq r hr0).isOpen.measurableSet).mp
        (domainLpRestrict_coeFn hqQ w)
    filter_upwards [zeroExtensionLp_coeFn hqQ wq, hwrep, ae_restrict_of_ae hre]
      with x hx hxc hxr
    rw [hx]
    by_cases hxq : x ∈ (centeredCube zq r hr0 : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem hxq]
      exact hxr hxq
    · rw [Set.indicator_of_notMem hxq, hxc]
      exact (image_eq_zero_of_notMem_tsupport (fun hs => hxq (hsupport hs))).symm
  exact ⟨wq, hdom, hext, by simpa only [Lq.energy_eq, LQ.energy_eq] using hupper⟩

/-- Actual norm limits on nested cubes are compatible killed forms. The localization
step and coefficient-sequence bounds are supplied by the two limit-side packages. -/
theorem limit_form_killed_consistency
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
    (GQ : DomainL2 (centeredCube zQ R hR0) →L[ℝ] DomainL2 (centeredCube zQ R hR0))
    (Gq : DomainL2 (centeredCube zq r hr0) →L[ℝ] DomainL2 (centeredCube zq r hr0))
    (LQ : aux_limit_form_package_limit_side d hd zQ R hR0 SQ GQ aQ)
    (Lq : aux_limit_form_package_limit_side d hd zq r hr0 Sq Gq aq)
 :
    let EQ := LQ.form.toClosedForm
    let Eq := Lq.form.toClosedForm
    ∃ D : Submodule ℝ (DomainL2 (centeredCube zQ R hR0)),
      DirichletForm.IsKilledDomain EQ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) D ∧
      (∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ D ↔
        ∃ u : DomainL2 (centeredCube zq r hr0),
          u ∈ Eq.domain ∧ zeroExtensionLp hqQ u = w) ∧
      (∀ u ∈ Eq.domain, zeroExtensionLp hqQ u ∈ EQ.domain ∧
        EQ.energy (zeroExtensionLp hqQ u) = Eq.energy u) ∧
      (∀ u ∈ Eq.domain, ∀ v ∈ Eq.domain,
        EQ.form (zeroExtensionLp hqQ u) (zeroExtensionLp hqQ v) = Eq.form u v) := by
  let EQ := LQ.form.toClosedForm
  let Eq := Lq.form.toClosedForm
  obtain ⟨_, hQlower0, _⟩ := aux_limit_form_package_mosco_free d hd zQ R hR0 SQ GQ aQ
    LQ.response LQ.response_eq LQ.response_tendsto
  obtain ⟨_, _, hqrecovery0⟩ := aux_limit_form_package_mosco_free d hd zq r hr0 Sq Gq aq
    Lq.response Lq.response_eq Lq.response_tendsto
  have hQlower : ∀ (vN : ℕ → SQ.space) (v : DomainL2 (centeredCube zQ R hR0)),
      (∀ f, Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      EQ.energy v ≤ liminf (fun n => (responseForm SQ (aQ n) (vN n) (vN n) : EReal)) atTop := by
    intro vN v hv
    simpa only [EQ, LQ.energy_eq] using hQlower0 vN v hv
  have hqrecovery : ∀ v ∈ Eq.domain, ∃ vN : ℕ → Sq.space,
      Tendsto (fun n => ((vN n).val.1,
        (responseForm Sq (aq n) (vN n) (vN n) : EReal))) atTop (𝓝 (v, Eq.energy v)) := by
    intro v hv
    have hvg : v ∈ limitFormDomain Gq := by
      change limitFormEnergy Gq v < ⊤
      rw [← Lq.energy_eq]
      exact (Eq.energy_lt_top_iff v).mpr hv
    simpa only [Eq, Lq.energy_eq] using hqrecovery0 v hvg
  have hLower : ∀ u ∈ Eq.domain, EQ.energy (zeroExtensionLp hqQ u) ≤ Eq.energy u := by
    intro u hu
    obtain ⟨_, _, _, _, h⟩ := prop_killed_consistency_zero_extension d hd zQ zq R r hR0 hr0
      hqQ SQ Sq hSQ hSq aQ aq hcoeff EQ Eq hQlower hqrecovery u hu
    exact h
  have hupper : ∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ EQ.domain →
      (∃ wc : SpatialCoordinates d → ℝ, Continuous wc ∧ HasCompactSupport wc ∧
        tsupport wc ⊆ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∧
        (w : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))] wc) →
      ∃ wq : DomainL2 (centeredCube zq r hr0), wq ∈ Eq.domain ∧
        zeroExtensionLp hqQ wq = w ∧ Eq.energy wq ≤ EQ.energy w := by
    rintro w hw ⟨wc, hwc, hcompact, hsupp, hae⟩
    exact aux_limit_form_killed_consistency_core d hd zQ zq R r hR0 hr0 hqQ SQ Sq hSQ hSq
      aQ aq hcoeff GQ Gq LQ Lq w hw wc hwc hcompact hsupp hae
  obtain ⟨C, hC⟩ := Lq.core
  have hclosure := prop_killed_consistency_core_closure d hd zQ zq R r hR0 hr0 hqQ EQ Eq
    ⟨C, hC⟩ hLower hupper
  let ext : DomainL2 (centeredCube zq r hr0) →ₗ[ℝ]
      DomainL2 (centeredCube zQ R hR0) :=
    { toFun := zeroExtensionLp hqQ
      map_add' := aux_prop_killed_consistency_zeroExtension_add hqQ
      map_smul' := aux_prop_killed_consistency_zeroExtension_smul hqQ }
  let D : Submodule ℝ (DomainL2 (centeredCube zQ R hR0)) :=
    Submodule.map ext Eq.domain
  have hdom : ∀ u : DomainL2 (centeredCube zq r hr0), u ∈ Eq.domain →
      ext u ∈ EQ.domain := by
    intro u hu
    exact (hclosure u hu).1
  have henergy : ∀ u : DomainL2 (centeredCube zq r hr0), u ∈ Eq.domain →
      EQ.energy (ext u) = Eq.energy u := by
    intro u hu
    exact (hclosure u hu).2.1
  have hform : ∀ (u : DomainL2 (centeredCube zq r hr0)) (hu : u ∈ Eq.domain)
      (v : DomainL2 (centeredCube zq r hr0)) (hv : v ∈ Eq.domain),
      EQ.form (ext u) (ext v) = Eq.form u v := by
    intro u hu v hv
    exact (hclosure u hu).2.2 v hv
  have hznorm : ∀ u : DomainL2 (centeredCube zq r hr0),
      ‖zeroExtensionLp hqQ u‖ = ‖u‖ := by
    intro u
    simpa using! lane2_norm_zeroExtensionLp hqQ u
  have henergy_norm : ∀ (u : DomainL2 (centeredCube zq r hr0)) (hu : u ∈ Eq.domain),
      EQ.energyNormSq (ext u) = Eq.energyNormSq u := by
    intro u hu
    have hformself := hform u hu u hu
    rw [DirichletForm.ClosedForm.energyNormSq,
      DirichletForm.ClosedForm.energyNormSq, hformself]
    change Eq.form u u + ‖zeroExtensionLp hqQ u‖ ^ 2 = Eq.form u u + ‖u‖ ^ 2
    rw [hznorm]
  have henergy_norm_sub :
      ∀ (u v : DomainL2 (centeredCube zq r hr0)), u ∈ Eq.domain → v ∈ Eq.domain →
        EQ.energyNormSq (ext u - ext v) = Eq.energyNormSq (u - v) := by
    intro u v hu hv
    rw [← ext.map_sub, henergy_norm (u - v) (Eq.domain.sub_mem hu hv)]
  have hcore_ext : ∀ u : DomainL2 (centeredCube zq r hr0), u ∈ C →
      EQ.MemCoreOn (centeredCube zq r hr0 : Set (SpatialCoordinates d)) (ext u) := by
    intro u hu
    have hcu := hC.memCoreOn u hu
    exact ⟨hdom u hcu.mem_domain,
      aux_prop_killed_consistency_zeroExtension_core_rep hqQ u hcu.hasCoreRep⟩
  have hle : D ≤ EQ.domain := by
    intro w hw
    change w ∈ Submodule.map ext Eq.domain at hw
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_map.mp hw)
    exact hdom u hu
  have hmemcore : ∀ w : DomainL2 (centeredCube zQ R hR0),
      EQ.MemCoreOn (centeredCube zq r hr0 : Set (SpatialCoordinates d)) w → w ∈ D := by
    intro w hw
    obtain ⟨u, hu, hext, _⟩ := hupper w hw.mem_domain hw.hasCoreRep
    change w ∈ Submodule.map ext Eq.domain
    apply Submodule.mem_map.mpr
    refine ⟨u, hu, ?_⟩
    exact hext
  have happrox : ∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ D →
      ∀ ε : ℝ, 0 < ε →
        ∃ w' : DomainL2 (centeredCube zQ R hR0),
          EQ.MemCoreOn (centeredCube zq r hr0 : Set (SpatialCoordinates d)) w' ∧
          EQ.energyNormSq (w - w') < ε := by
    intro w hw ε hε
    change w ∈ Submodule.map ext Eq.domain at hw
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_map.mp hw)
    obtain ⟨c, hc, hlt⟩ := hC.denseEnergy u hu ε hε
    refine ⟨ext c, hcore_ext c hc, ?_⟩
    rw [← ext.map_sub, henergy_norm (u - c)
      (Eq.domain.sub_mem hu (hC.memCoreOn c hc).mem_domain)]
    exact hlt
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · refine
      { le_domain := hle
        memCoreOn_mem := hmemcore
        approx := happrox
        isClosed := ?_ }
    intro wN w hwN hwd hconv
    have hdomN : ∀ n, wN n ∈ EQ.domain := fun n => hle (hwN n)
    have hwN' : ∀ n, wN n ∈ Submodule.map ext Eq.domain := by
      intro n
      simpa only [D] using hwN n
    choose uN huN hwu using fun n => Submodule.mem_map.mp (hwN' n)
    have hEQcauchy : ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
          EQ.energyNormSq (wN p - wN q) < ε := by
      intro ε hε
      have hδ : 0 < ε / 4 := by linarith
      obtain ⟨N, hN⟩ := (eventually_atTop.1 ((tendsto_order.mp hconv).2 (ε / 4) hδ))
      refine ⟨N, ?_⟩
      intro p hp q hq
      have hEp := hN p hp
      have hEq := hN q hq
      have hsubp : wN p - w ∈ EQ.domain := EQ.domain.sub_mem (hdomN p) hwd
      have hsubq : wN q - w ∈ EQ.domain := EQ.domain.sub_mem (hdomN q) hwd
      have hsp : Real.sqrt (EQ.energyNormSq (wN p - w)) < Real.sqrt ε / 2 := by
        calc
          Real.sqrt (EQ.energyNormSq (wN p - w)) < Real.sqrt (ε / 4) :=
            Real.sqrt_lt_sqrt (EQ.energyNormSq_nonneg hsubp) hEp
          _ = Real.sqrt ε / 2 := by
            rw [Real.sqrt_div (le_of_lt hε)]
            norm_num
      have hsq : Real.sqrt (EQ.energyNormSq (w - wN q)) < Real.sqrt ε / 2 := by
        rw [EQ.energyNormSq_sub_comm hwd (hdomN q)]
        calc
          Real.sqrt (EQ.energyNormSq (wN q - w)) < Real.sqrt (ε / 4) :=
            Real.sqrt_lt_sqrt (EQ.energyNormSq_nonneg hsubq) hEq
          _ = Real.sqrt ε / 2 := by
            rw [Real.sqrt_div (le_of_lt hε)]
            norm_num
      have htri := EQ.sqrt_energyNormSq_sub_le (hdomN p) hwd (hdomN q)
      have hsqrt : Real.sqrt (EQ.energyNormSq (wN p - wN q)) < Real.sqrt ε := by
        exact lt_of_le_of_lt htri (by linarith)
      have hsquare := (Real.sqrt_lt (EQ.energyNormSq_nonneg
        (EQ.domain.sub_mem (hdomN p) (hdomN q))) (Real.sqrt_nonneg ε)).mp hsqrt
      nlinarith [Real.sq_sqrt (le_of_lt hε)]
    have hEqcauchy : ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
          Eq.energyNormSq (uN p - uN q) < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hEQcauchy ε hε
      refine ⟨N, ?_⟩
      intro p hp q hq
      have heq := henergy_norm_sub (uN p) (uN q) (huN p) (huN q)
      have heq' : EQ.energyNormSq (wN p - wN q) =
          Eq.energyNormSq (uN p - uN q) := by
        rw [← hwu p, ← hwu q]
        exact heq
      rw [← heq']
      exact hN p hp q hq
    obtain ⟨u, hu, huconv⟩ := Eq.complete uN huN hEqcauchy
    have huconv' : Tendsto (fun n => Eq.energyNormSq (uN n - u)) atTop (𝓝 0) := by
      simpa only [DirichletForm.ClosedForm.energyNormSq] using huconv
    have hEQnorm : Tendsto (fun n => ‖wN n - w‖) atTop (𝓝 0) := by
      have hsqrt : Tendsto
          (fun n => Real.sqrt (EQ.energyNormSq (wN n - w))) atTop (𝓝 0) := by
        have hc : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
          simpa using (Real.continuous_sqrt.tendsto 0)
        simpa using! hc.comp hconv
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsqrt
      exact (Real.le_sqrt (norm_nonneg _) (EQ.energyNormSq_nonneg
        (EQ.domain.sub_mem (hdomN n) hwd))).mpr (EQ.sq_norm_le_energyNormSq
          (EQ.domain.sub_mem (hdomN n) hwd))
    have hEqnorm : Tendsto (fun n => ‖uN n - u‖) atTop (𝓝 0) := by
      have hsqrt : Tendsto
          (fun n => Real.sqrt (Eq.energyNormSq (uN n - u))) atTop (𝓝 0) := by
        have hc : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
          simpa using (Real.continuous_sqrt.tendsto 0)
        simpa using! hc.comp huconv'
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsqrt
      exact (Real.le_sqrt (norm_nonneg _) (Eq.energyNormSq_nonneg
        (Eq.domain.sub_mem (huN n) hu))).mpr (Eq.sq_norm_le_energyNormSq
          (Eq.domain.sub_mem (huN n) hu))
    have hExtnorm : Tendsto (fun n => ‖ext (uN n) - ext u‖) atTop (𝓝 0) := by
      apply hEqnorm.congr
      intro n
      rw [← ext.map_sub]
      change ‖uN n - u‖ = ‖zeroExtensionLp hqQ (uN n - u)‖
      rw [hznorm]
    have hWExtnorm : Tendsto (fun n => ‖wN n - ext u‖) atTop (𝓝 0) := by
      apply hExtnorm.congr
      intro n
      rw [hwu n]
    have hWtoW : Tendsto wN atTop (𝓝 w) :=
      (tendsto_iff_norm_sub_tendsto_zero).2 hEQnorm
    have hWtoExt : Tendsto wN atTop (𝓝 (ext u)) :=
      (tendsto_iff_norm_sub_tendsto_zero).2 hWExtnorm
    have hext : ext u = w := tendsto_nhds_unique hWtoExt hWtoW
    change w ∈ Submodule.map ext Eq.domain
    apply Submodule.mem_map.mpr
    exact ⟨u, hu, hext⟩
  · intro w
    constructor
    · intro hw
      change w ∈ Submodule.map ext Eq.domain at hw
      obtain ⟨u, hu, hext⟩ := Submodule.mem_map.mp hw
      exact ⟨u, hu, hext⟩
    · rintro ⟨u, hu, hext⟩
      change w ∈ Submodule.map ext Eq.domain
      exact Submodule.mem_map.mpr ⟨u, hu, hext⟩
  · intro u hu
    exact ⟨hdom u hu, henergy u hu⟩
  · intro u hu v hv
    exact hform u hu v hv

end Paper
