module

public import SubdiffusiveProcess.Paper.catalog_cutoff_existence
public import SubdiffusiveProcess.Paper.prop_killed_consistency_zero_extension
public import SubdiffusiveProcess.Paper.prop_killed_consistency_cutoff_localization
public import SubdiffusiveProcess.Paper.prop_killed_consistency_core_closure
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

lemma aux_prop_killed_consistency_zeroExtension_add
    {d : ℕ} {V U : Opens (SpatialCoordinates d)} (hV : V ≤ U)
    (u v : DomainL2 V) :
    zeroExtensionLp hV (u + v) = zeroExtensionLp hV u + zeroExtensionLp hV v := by
  apply Lp.ext
  have huv0 : ∀ᵐ x ∂volume.restrict (V : Set (SpatialCoordinates d)),
      ((u + v : DomainL2 V) : SpatialCoordinates d → ℝ) x = u x + v x := by
    filter_upwards [Lp.coeFn_add u v] with x hx
    simpa using hx
  have huv : ∀ᵐ x ∂volume, x ∈ (V : Set (SpatialCoordinates d)) →
      ((u + v : DomainL2 V) : SpatialCoordinates d → ℝ) x = u x + v x :=
    (ae_restrict_iff' V.isOpen.measurableSet).mp huv0
  have huv' := ae_restrict_of_ae (s := (U : Set (SpatialCoordinates d))) huv
  filter_upwards [zeroExtensionLp_coeFn hV (u + v),
    zeroExtensionLp_coeFn hV u, zeroExtensionLp_coeFn hV v,
    Lp.coeFn_add (zeroExtensionLp hV u) (zeroExtensionLp hV v), huv'] with
    x hsum hu hv hadd hinside
  rw [hsum, hadd]
  change (V : Set (SpatialCoordinates d)).indicator
      ((u + v : DomainL2 V) : SpatialCoordinates d → ℝ) x =
    zeroExtensionLp hV u x + zeroExtensionLp hV v x
  rw [hu, hv]
  by_cases hx : x ∈ (V : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    simpa using hinside hx
  · simp only [Set.indicator_of_notMem hx, add_zero]

lemma aux_prop_killed_consistency_zeroExtension_smul
    {d : ℕ} {V U : Opens (SpatialCoordinates d)} (hV : V ≤ U)
    (c : ℝ) (u : DomainL2 V) :
    zeroExtensionLp hV (c • u) = c • zeroExtensionLp hV u := by
  apply Lp.ext
  have hu0 : ∀ᵐ x ∂volume.restrict (V : Set (SpatialCoordinates d)),
      ((c • u : DomainL2 V) : SpatialCoordinates d → ℝ) x = c • u x := by
    filter_upwards [Lp.coeFn_smul c u] with x hx
    simpa using hx
  have hu : ∀ᵐ x ∂volume, x ∈ (V : Set (SpatialCoordinates d)) →
      ((c • u : DomainL2 V) : SpatialCoordinates d → ℝ) x = c • u x :=
    (ae_restrict_iff' V.isOpen.measurableSet).mp hu0
  have hu' := ae_restrict_of_ae (s := (U : Set (SpatialCoordinates d))) hu
  filter_upwards [zeroExtensionLp_coeFn hV (c • u), zeroExtensionLp_coeFn hV u,
    Lp.coeFn_smul c (zeroExtensionLp hV u), hu'] with x hsm hu hmul hinside
  rw [hsm, hmul]
  change (V : Set (SpatialCoordinates d)).indicator
      ((c • u : DomainL2 V) : SpatialCoordinates d → ℝ) x =
    c • zeroExtensionLp hV u x
  rw [hu]
  by_cases hx : x ∈ (V : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    simpa using hinside hx
  · simp only [Set.indicator_of_notMem hx, smul_zero]

lemma aux_prop_killed_consistency_zeroExtension_core_rep
    {d : ℕ} {V U : Opens (SpatialCoordinates d)} (hV : V ≤ U)
    (u : DomainL2 V) (hu : DirichletForm.HasCoreRep
      (volume.restrict (V : Set (SpatialCoordinates d)))
      (V : Set (SpatialCoordinates d)) u) :
    DirichletForm.HasCoreRep
      (volume.restrict (U : Set (SpatialCoordinates d)))
      (V : Set (SpatialCoordinates d)) (zeroExtensionLp hV u) := by
  obtain ⟨f, hf, hfc, hsupp, hae⟩ := hu
  refine ⟨f, hf, hfc, hsupp, ?_⟩
  have hae' : ∀ᵐ x ∂volume, x ∈ (V : Set (SpatialCoordinates d)) → u x = f x :=
    (ae_restrict_iff' V.isOpen.measurableSet).mp hae
  have haeU := ae_restrict_of_ae (s := (U : Set (SpatialCoordinates d))) hae'
  filter_upwards [zeroExtensionLp_coeFn hV u, haeU] with x hx hxeq
  rw [hx]
  by_cases hxV : x ∈ (V : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hxV]
    exact hxeq hxV
  · rw [Set.indicator_of_notMem hxV]
    exact (image_eq_zero_of_notMem_tsupport (fun h => hxV (hsupp h))).symm



theorem prop_killed_consistency
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
    (hQlower : ∀ (vN : ℕ → SQ.space) (v : DomainL2 (centeredCube zQ R hR0)),
      (∀ f : DomainL2 (centeredCube zQ R hR0),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      (EQ.energy v : EReal) ≤
        liminf (fun n => (responseForm SQ (aQ n) (vN n) (vN n) : EReal)) atTop)
    (hQrecovery : ∀ v ∈ EQ.domain, ∃ vN : ℕ → SQ.space,
      Tendsto (fun n => ((vN n).val.1,
        (responseForm SQ (aQ n) (vN n) (vN n) : EReal))) atTop
        (𝓝 (v, (EQ.energy v : EReal))))
    (hqlower : ∀ (vN : ℕ → Sq.space) (v : DomainL2 (centeredCube zq r hr0)),
      (∀ f : DomainL2 (centeredCube zq r hr0),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      (Eq.energy v : EReal) ≤
        liminf (fun n => (responseForm Sq (aq n) (vN n) (vN n) : EReal)) atTop)
    (hqrecovery : ∀ v ∈ Eq.domain, ∃ vN : ℕ → Sq.space,
      Tendsto (fun n => ((vN n).val.1,
        (responseForm Sq (aq n) (vN n) (vN n) : EReal))) atTop
        (𝓝 (v, (Eq.energy v : EReal))))
    (hqRegular : ∃ C : Set (DomainL2 (centeredCube zq r hr0)),
      DirichletForm.IsCoreOn Eq (centeredCube zq r hr0 : Set (SpatialCoordinates d)) C)
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : SQ.space,
      cubeFractionalL2Seminorm hd zQ R hR0 Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : SQ.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube zQ R hR0 : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd zQ R hR0 Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm SQ (aQ n) w w)
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
    ∃ D : Submodule ℝ (DomainL2 (centeredCube zQ R hR0)),
      DirichletForm.IsKilledDomain EQ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) D ∧
      (∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ D ↔
        ∃ u : DomainL2 (centeredCube zq r hr0),
          u ∈ Eq.domain ∧ zeroExtensionLp hqQ u = w) ∧
      (∀ u ∈ Eq.domain, zeroExtensionLp hqQ u ∈ EQ.domain ∧
        EQ.energy (zeroExtensionLp hqQ u) = Eq.energy u) ∧
      (∀ u ∈ Eq.domain, ∀ v ∈ Eq.domain,
        EQ.form (zeroExtensionLp hqQ u) (zeroExtensionLp hqQ v) = Eq.form u v) := by
  have hzero : ∀ (u : DomainL2 (centeredCube zq r hr0)) (hu : u ∈ Eq.domain),
      ∃ uNQ : ℕ → SQ.space,
        (∀ n, (uNQ n).val.1 = zeroExtensionLp hqQ
          ((Classical.choose (hqrecovery u hu) n).val.1)) ∧
        (∀ n, responseForm SQ (aQ n) (uNQ n) (uNQ n) =
          responseForm Sq (aq n) (Classical.choose (hqrecovery u hu) n)
            (Classical.choose (hqrecovery u hu) n)) ∧
        Tendsto (fun n => ((uNQ n).val.1,
          (responseForm SQ (aQ n) (uNQ n) (uNQ n) : EReal))) atTop
          (𝓝 (zeroExtensionLp hqQ u, (Eq.energy u : EReal))) ∧
        (EQ.energy (zeroExtensionLp hqQ u) : EReal) ≤ (Eq.energy u : EReal) := by
    intro u hu
    exact prop_killed_consistency_zero_extension d hd zQ zq R r hR0 hr0 hqQ SQ Sq
      hSQ hSq aQ aq hcoeff EQ Eq hQlower hqrecovery u hu
  have hupper :
      ∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ EQ.domain →
        (∃ wc : SpatialCoordinates d → ℝ, Continuous wc ∧
          HasCompactSupport wc ∧
          tsupport wc ⊆ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∧
          (w : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))] wc) →
        ∃ wq : DomainL2 (centeredCube zq r hr0),
          wq ∈ Eq.domain ∧ zeroExtensionLp hqQ wq = w ∧
          (Eq.energy wq : EReal) ≤ (EQ.energy w : EReal) := by
    intro w hw hwrep
    exact prop_killed_consistency_cutoff_localization d hd zQ zq R r hR0 hr0 hqQ SQ Sq
      hSQ hSq aQ aq hcoeff EQ Eq hQrecovery hqlower KN hKN Kstar hKstar hfrac hcoercive
      hInterp t ht htd hcutoffs w hw hwrep hcutoffProduct
  obtain ⟨C, hC⟩ := hqRegular
  have hclosure := prop_killed_consistency_core_closure d hd zQ zq R r hR0 hr0 hqQ EQ Eq
    ⟨C, hC⟩
    (fun u hu => by
      obtain ⟨uNQ, h1, h2, h3, h4⟩ := hzero u hu
      exact h4)
    hupper
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
  have henergy_norm : ∀ (u : DomainL2 (centeredCube zq r hr0)) (hu : u ∈ Eq.domain),
      EQ.energyNormSq (ext u) = Eq.energyNormSq u := by
    intro u hu
    have hformself := hform u hu u hu
    rw [DirichletForm.ClosedForm.energyNormSq,
      DirichletForm.ClosedForm.energyNormSq, hformself]
    change Eq.form u u + ‖zeroExtensionLp hqQ u‖ ^ 2 = Eq.form u u + ‖u‖ ^ 2
    have hn : ‖zeroExtensionLp hqQ u‖ = ‖u‖ := by
      simpa only [] using! (lane2_norm_zeroExtensionLp hqQ u)
    rw [hn]
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
        simpa only [Function.comp_apply] using! hc.comp hconv
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsqrt
      exact (Real.le_sqrt (norm_nonneg _) (EQ.energyNormSq_nonneg
        (EQ.domain.sub_mem (hdomN n) hwd))).mpr (EQ.sq_norm_le_energyNormSq
          (EQ.domain.sub_mem (hdomN n) hwd))
    have hEqnorm : Tendsto (fun n => ‖uN n - u‖) atTop (𝓝 0) := by
      have hsqrt : Tendsto
          (fun n => Real.sqrt (Eq.energyNormSq (uN n - u))) atTop (𝓝 0) := by
        have hc : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by
          simpa using (Real.continuous_sqrt.tendsto 0)
        simpa only [Function.comp_apply] using! hc.comp huconv'
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsqrt
      exact (Real.le_sqrt (norm_nonneg _) (Eq.energyNormSq_nonneg
        (Eq.domain.sub_mem (huN n) hu))).mpr (Eq.sq_norm_le_energyNormSq
          (Eq.domain.sub_mem (huN n) hu))
    have hExtnorm : Tendsto (fun n => ‖ext (uN n) - ext u‖) atTop (𝓝 0) := by
      apply hEqnorm.congr
      intro n
      rw [← ext.map_sub]
      change ‖uN n - u‖ = ‖zeroExtensionLp hqQ (uN n - u)‖
      symm
      simpa only [] using! (lane2_norm_zeroExtensionLp hqQ (uN n - u))
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
