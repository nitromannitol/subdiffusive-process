module

public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_endpoints_support_1
public import SubdiffusiveProcess.Paper.in_represented_mosco
public import SubdiffusiveProcess.Paper.prop_locality
public import SubdiffusiveProcess.Paper.energy_order_of_form_order

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ContDiff
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Paper

theorem aux_lem_endpoints_support_2_property_of_limit {V : Type*} [TopologicalSpace V] [T2Space V]
    (GN : ℕ → V) (G : V) (hconv : Tendsto GN atTop (𝓝 G))
    (property : V → Prop) (hconv_of : ∀ x, property x → Tendsto GN atTop (𝓝 x))
    (hex : ∃! x, property x) : property G := by
  obtain ⟨x, hx, _⟩ := hex
  have hxG : x = G := tendsto_nhds_unique (hconv_of x hx) hconv
  exact hxG ▸ hx

theorem aux_lem_endpoints_support_2_inverse_limit_form
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (hcontract : ∀ (n : ℕ) (T : ℝ → ℝ),
      DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
        ((v.val.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
            (fun x => T (u.val.1 x))) ∧
        responseForm S (a n) v v ≤ responseForm S (a n) u u)
    (GN : ℕ → DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (hGN : ∀ (n : ℕ) (f : DomainL2 (centeredCube z R hR)), GN n f =
      (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (K : ℝ) (hK : 0 < K)
    (hCoercive : ∀ (n : ℕ) (v : S.space),
      cubeFractionalL2Seminorm hd z R hR Lane4.threeQuarterOrder
          (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 + volume.real (centeredCube z R hR : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z R hR Lane4.threeQuarterOrder
              (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
        K * responseForm S (a n) v v)
    (D : Submodule ℚ (DomainL2 (centeredCube z R hR)))
    (hDcount : (D : Set (DomainL2 (centeredCube z R hR))).Countable)
    (hDdense : Dense (D : Set (DomainL2 (centeredCube z R hR))))
    (hDsmooth : ∀ f : D,
      ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (f.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] fc)
    (hresponse : ∀ f : D, CauchySeq (fun n => inner ℝ f.val (GN n f.val)))
    (hmesh : ∀ φ : DomainL2 (centeredCube z R hR),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (φ : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] fc) →
      ∀ ε : ℝ, 0 < ε → ∃ w : ℕ → S.space, ∃ C : ℝ,
        (∀ n : ℕ, responseForm S (a n) (w n) (w n) ≤ C) ∧
        (∀ n : ℕ, ‖(w n).val.1 - φ‖ ≤ ε))
    (G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (hconv : Tendsto GN atTop (𝓝 G)) :
    ∃ (EForm : _root_.DirichletForm
        (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
      (Rroot : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR)),
      (∀ v : DomainL2 (centeredCube z R hR),
        EForm.toClosedForm.energy v = limitFormEnergy G v) ∧
      (∀ x y : DomainL2 (centeredCube z R hR), inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x y : DomainL2 (centeredCube z R hR), inner ℝ (Rroot x) y = inner ℝ x (Rroot y)) ∧
      Rroot.comp Rroot = G ∧
      limitFormDomain G = Set.range Rroot ∧
      Function.Injective Rroot ∧
      (∀ (vN : ℕ → S.space) (v : DomainL2 (centeredCube z R hR)),
        (∀ f : DomainL2 (centeredCube z R hR),
          Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
        EForm.toClosedForm.energy v ≤
          liminf (fun n => ((responseForm S
            (a n) (vN n) (vN n) : ℝ) :
              EReal)) atTop) := by
  let EN : ℕ → DomainL2 (centeredCube z R hR) → EReal := fun n u =>
    sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧ e = (responseForm S (a n) w w : EReal)}
  have hEN : ∀ n u, EN n u =
      sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧ e = (responseForm S (a n) w w : EReal)} :=
    fun _ _ => rfl
  have hGc := aux_lem_endpoints_support_2_property_of_limit GN G hconv _
    (fun _ h => h.1.1)
    (prop_killed_inverse d hd z R hR S hS a hcontract GN hGN
      hInterp K hK hCoercive D hDcount hDdense hDsmooth hresponse EN hEN hmesh)
  obtain ⟨Rroot, hRsymm, _hRpos, hRcomp, hRdom⟩ := hGc.2.1
  obtain ⟨EForm, hEForm, _hHNC⟩ := hGc.2.2.1
  refine ⟨EForm, Rroot, hEForm, hGc.1.2.2.1, hRsymm, hRcomp, hRdom,
    aux_prop_killed_inverse_dirichlet_form_root_injective G Rroot hRcomp hGc.1.2.2.2.2, ?_⟩
  intro vN v hv
  rw [hEForm]
  exact aux_prop_killed_inverse_moscoS S a G EN hEN hGc.2.2.2.1.1 vN v hv

theorem aux_lem_endpoints_support_2_response_cauchy {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (GN : ℕ → V →L[ℝ] V) (G : V →L[ℝ] V)
    (hconv : Tendsto GN atTop (𝓝 G)) (f : V) :
    CauchySeq (fun n => inner ℝ f (GN n f)) := by
  have heval := ((ContinuousLinearMap.apply ℝ V f).continuous.tendsto G).comp hconv
  exact (tendsto_const_nhds.inner heval).cauchySeq

theorem aux_lem_endpoints_support_2_hregularity_construct
    {d : ℕ} (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (Sspace0 : ResponseSpace (centeredCube z0 r0 hr0))
    (hSspace0 : Sspace0.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (hcontract0 : ∀ (n : ℕ) (T : ℝ → ℝ),
      DirichletForm.IsNormalContraction T → ∀ u : Sspace0.space,
        ∃ v : Sspace0.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm Sspace0
              (Lane4.cutoffPositiveCoefficient model H om n z0 hr0) v v ≤
            responseForm Sspace0
              (Lane4.cutoffPositiveCoefficient model H om n z0 hr0) u u)
    (G0 : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N0 : ℕ → ℕ)
    (GN0 : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGN0 : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), GN0 n f =
      (responseSolution Sspace0
          (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0)
          ((sobolevVolumeLoad f).comp Sspace0.space.subtypeL)).val.1)
    (hGN0tendsto : Tendsto GN0 atTop (𝓝 G0))
    (K : ℝ) (hK0 : 0 < K)
    (hCoercive : ∀ (n : ℕ) (v : Sspace0.space),
      cubeFractionalL2Seminorm hd z0 r0 hr0 Lane4.threeQuarterOrder
          (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 + volume.real (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z0 r0 hr0 Lane4.threeQuarterOrder
              (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
        K * responseForm Sspace0
          (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0) v v)
    (D : Submodule ℚ (DomainL2 (centeredCube z0 r0 hr0)))
    (hDcount : (D : Set (DomainL2 (centeredCube z0 r0 hr0))).Countable)
    (hDdense : Dense (D : Set (DomainL2 (centeredCube z0 r0 hr0))))
    (hDsmooth : ∀ f : D, ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧
      HasCompactSupport fc ∧
      tsupport fc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
      (f.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] fc)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (hbundle0 : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 Sspace0 G0 N0) :
    ∃ (EForm : _root_.DirichletForm
        (volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
      (Rroot : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0)),
      (∀ v : DomainL2 (centeredCube z0 r0 hr0),
        EForm.toClosedForm.energy v = limitFormEnergy G0 v) ∧
      (∀ x y : DomainL2 (centeredCube z0 r0 hr0), inner ℝ (G0 x) y = inner ℝ x (G0 y)) ∧
      (∀ x y : DomainL2 (centeredCube z0 r0 hr0), inner ℝ (Rroot x) y = inner ℝ x (Rroot y)) ∧
      Rroot.comp Rroot = G0 ∧
      limitFormDomain G0 = Set.range Rroot ∧
      Function.Injective Rroot ∧
      (∀ (vN : ℕ → Sspace0.space) (v : DomainL2 (centeredCube z0 r0 hr0)),
        (∀ f : DomainL2 (centeredCube z0 r0 hr0),
          Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
        EForm.toClosedForm.energy v ≤
          liminf (fun n => ((responseForm Sspace0
            (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0) (vN n) (vN n) : ℝ) :
              EReal)) atTop) := by
  exact aux_lem_endpoints_support_2_inverse_limit_form d hd z0 r0 hr0 Sspace0 hSspace0
    (fun n => Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0)
    (fun n => hcontract0 (N0 n)) GN0 hGN0 hInterp K hK0 hCoercive D hDcount hDdense hDsmooth
    (fun f => aux_lem_endpoints_support_2_response_cauchy GN0 G0 hGN0tendsto f.val)
    (aux_lem_endpoints_support_1_endpoint_invariance_hmesh_of_bounds_side hd model H om z0 r0 hr0
      Sspace0 G0 N0 hbundle0) G0 hGN0tendsto

theorem aux_lem_endpoints_support_2_hregularity_side
    {d : ℕ} (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (Sspace0 : ResponseSpace (centeredCube z0 r0 hr0))
    (hSspace0 : Sspace0.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (hcontract0 : ∀ (n : ℕ) (T : ℝ → ℝ),
      DirichletForm.IsNormalContraction T → ∀ u : Sspace0.space,
        ∃ v : Sspace0.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm Sspace0
              (Lane4.cutoffPositiveCoefficient model H om n z0 hr0) v v ≤
            responseForm Sspace0
              (Lane4.cutoffPositiveCoefficient model H om n z0 hr0) u u)
    (G0 : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N0 : ℕ → ℕ)
    (GN0 : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGN0 : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), GN0 n f =
      (responseSolution Sspace0
          (Lane4.cutoffPositiveCoefficient model H om (N0 n) z0 hr0)
          ((sobolevVolumeLoad f).comp Sspace0.space.subtypeL)).val.1)
    (hGN0tendsto : Tendsto GN0 atTop (𝓝 G0))
    (hbundle0 : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 Sspace0 G0 N0) :
    ∃ E : _root_.DirichletForm
        (volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))),
      E.domain = limitFormDomain G0 ∧
      (∀ v : DomainL2 (centeredCube z0 r0 hr0),
        E.toClosedForm.energy v = limitFormEnergy G0 v) ∧
      ∃ Cc : Set (DomainL2 (centeredCube z0 r0 hr0)),
        DirichletForm.IsCoreOn E.toClosedForm
          (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) Cc := by
  obtain ⟨K, hK0, hCoercive, D, hDcount, hDdense, hDsmooth, hInterp⟩ :=
    aux_lem_endpoints_support_1_hregularity_supply hd model H om z0 r0 hr0 Sspace0 G0 N0 hbundle0
  obtain ⟨EForm, Rroot, hE, hSymmC, hRsymm, hRcomp, hRdom, hRinj, hLower⟩ :=
    aux_lem_endpoints_support_2_hregularity_construct hd model H om z0 r0 hr0 Sspace0 hSspace0 hcontract0 G0 N0 GN0 hGN0
      hGN0tendsto K hK0 hCoercive D hDcount hDdense hDsmooth hInterp hbundle0
  have hEdomIff : ∀ v0 : DomainL2 (centeredCube z0 r0 hr0),
      v0 ∈ EForm.toClosedForm.domain ↔ v0 ∈ limitFormDomain G0 := by
    intro v0
    show v0 ∈ EForm.toClosedForm.domain ↔ limitFormEnergy G0 v0 < ⊤
    rw [← hE v0]
    exact (EForm.toClosedForm.energy_lt_top_iff v0).symm
  have hGmem : ∀ f : DomainL2 (centeredCube z0 r0 hr0), G0 f ∈ EForm.toClosedForm.domain := by
    intro f
    refine (hEdomIff (G0 f)).mpr ?_
    rw [hRdom]
    exact ⟨Rroot f, by rw [← ContinuousLinearMap.comp_apply, hRcomp]⟩
  have hRange := aux_lem_endpoints_support_1_hregularity_hRange_of_root G0 Rroot EForm hE hSymmC hRsymm hRcomp hRinj
    hRdom hGmem hEdomIff
  have hGbound := aux_lem_endpoints_support_1_hregularity_hGbound_of_root G0 Rroot EForm hE hSymmC hRsymm hRcomp hRinj
    hGmem
  obtain ⟨⟨Cc, hCc⟩, _hIsRegular⟩ :=
    aux_lem_endpoints_support_1_regularity_instance_killed d hd z0 r0 hr0 Sspace0 hSspace0 model H om N0 G0 EForm
      hE hGmem hLower hbundle0 hRange hGbound
  exact ⟨EForm, Set.ext hEdomIff, hE, Cc, hCc⟩

theorem aux_lem_endpoints_support_2_core_locality
    (d : ℕ) (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (hS : S.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ)
    (Gn : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGnEq : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), Gn n f =
      (responseSolution S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hGnTendsto : Tendsto Gn atTop (𝓝 G))
    (hbundle : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 S G N) :
    ∀ (u v : DomainL2 (centeredCube z0 r0 hr0)) (hu : MemFormCore G u) (hv : MemFormCore G v)
    (uc vc : SpatialCoordinates d → ℝ)
    (huc : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] uc)
    (hvc : (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vc)
    (hucont : Continuous uc) (hvcont : Continuous vc)
    (hvsupp : HasCompactSupport vc)
    (husuppQ : tsupport uc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
    (hvsuppQ : tsupport vc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)))
    (husupp : HasCompactSupport uc)
    (c : ℝ) (W : Set (SpatialCoordinates d)) (hW : IsOpen W)
    (hsupp : tsupport vc ⊆ W) (hconst : ∀ x ∈ W, uc x = c),
    limitFormBilinear G u v = 0 := by
  have hMosco := aux_in_represented_mosco_free d hd model H om z0 r0 hr0 S G N Gn hGnEq hGnTendsto
  obtain ⟨KN, hKN, Kstar, hKstar, hfrac, hcoercive, hInterp, t, ht, htd, hcutoffs, _⟩ := hbundle
  exact prop_locality d hd z0 r0 hr0 S hS
    (fun n => Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0) G
    hMosco.1 hMosco.2.1 hMosco.2.2 KN hKN Kstar hKstar hfrac hcoercive hInterp
    t ht htd hcutoffs

theorem aux_lem_endpoints_support_2_endpoint_invariance_core_lower_one_sided
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

theorem aux_lem_endpoints_support_2_endpoint_invariance_energy_order_one_sided_light
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
      exact aux_lem_endpoints_support_2_endpoint_invariance_core_lower_one_sided Q E F hFreg hdom
        GammaE GammaF m hm hform hw A)
  rwa [one_mul] at h

theorem aux_lem_endpoints_support_2_energy_measure_support
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mu : Measure X}
    {E : DirichletForm.ClosedForm mu} (Gamma : DirichletForm.EnergyMeasure E)
    {U : Set X} (hU : MeasurableSet U) {Cc : Set (Lp ℝ 2 mu)}
    (hCc : DirichletForm.IsCoreOn E U Cc) {u : Lp ℝ 2 mu} (hu : u ∈ E.domain) :
    Gamma.measure u Uᶜ = 0 := by
  have hsqrt : Real.sqrt (Gamma.measure u Uᶜ).toReal ≤ 0 := by
    refine le_of_forall_pos_le_add fun eps heps => ?_
    obtain ⟨w, hwC, hsmall⟩ := hCc.denseEnergy u hu (eps ^ 2) (sq_pos_of_pos heps)
    have hw := hCc.memCoreOn w hwC
    have hw0 : Gamma.measure w Uᶜ = 0 := by
      obtain ⟨hwE, wc, hwc, _hwcompact, hwsupport, hwae⟩ := hw
      exact measure_mono_null (compl_subset_compl.mpr hwsupport)
        (Gamma.measure_compl_tsupport w hwE wc hwc hwae)
    have hdiff := E.domain.sub_mem hu hw.mem_domain
    have hbound : (Gamma.measure (u - w) Uᶜ).toReal ≤ eps ^ 2 :=
      (Gamma.toReal_measure_le_form hdiff Uᶜ).trans
        (E.form_le_energyNormSq.trans hsmall.le)
    have hs := aux_energy_order_of_form_order_sqrt_le Gamma hu hw.mem_domain hU.compl
    rw [hw0, ENNReal.toReal_zero, Real.sqrt_zero, zero_add] at hs
    exact (hs.trans (Real.sqrt_le_sqrt hbound)).trans_eq
      (by rw [Real.sqrt_sq heps.le, zero_add])
  have hz : (Gamma.measure u Uᶜ).toReal = 0 := by
    have hs0 := le_antisymm hsqrt (Real.sqrt_nonneg _)
    have hsq := Real.sq_sqrt (ENNReal.toReal_nonneg : 0 ≤ (Gamma.measure u Uᶜ).toReal)
    rw [hs0, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsq
    exact hsq.symm
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (Gamma.measure_ne_top hu Uᶜ)

end Paper

namespace Paper

theorem aux_lem_endpoints_support_2_form_eq_zero_of_bilinear
    {d : ℕ} {Q : TopologicalSpace.Opens (SpatialCoordinates d)}
    (F : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (hF : ∀ w, F.energy w = limitFormEnergy G w)
    (u v : DomainL2 Q) (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    (h0 : limitFormBilinear G u v = 0) : F.form u v = 0 := by
  unfold limitFormBilinear at h0
  rw [← hF (u + v), ← hF (u - v),
    F.energy_of_mem (F.domain.add_mem hu hv),
    F.energy_of_mem (F.domain.sub_mem hu hv)] at h0
  have h4 : (4 : EReal) = ((4 : ℝ) : EReal) := (EReal.coe_natCast (n := 4)).symm
  rw [h4, ← EReal.coe_sub, ← EReal.coe_div, EReal.coe_eq_zero] at h0
  have hA : F.form (u + v) (u + v) = F.form u u + 2 * F.form u v + F.form v v :=
    F.form_add_self hu hv
  have hB : F.form (u - v) (u - v) = F.form u u - 2 * F.form u v + F.form v v := by
    rw [F.form_sub_left hu hv (F.domain.sub_mem hu hv),
      F.form_sub_right hu hu hv, F.form_sub_right hv hu hv, F.form_symm v hv u hu]
    ring
  rw [hA, hB] at h0
  linarith

theorem aux_lem_endpoints_support_2_form_core_locality
    (d : ℕ) (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (hS : S.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ)
    (Gn : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGnEq : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), Gn n f =
      (responseSolution S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hGnTendsto : Tendsto Gn atTop (𝓝 G))
    (hbundle : aux_in_represented_bounds_side d hd model H om z0 r0 hr0 S G N)
    (E : DirichletForm.ClosedForm
      (volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) :
    ∀ u v : DomainL2 (centeredCube z0 r0 hr0),
      E.MemCoreOn (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) u →
      E.MemCoreOn (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → E.form u v = 0 := by
  intro u v hu hv uc vc huc hvc hcu hcv hsu hsv hsuQ hsvQ c W hW hsupp hconst
  have hu' : MemFormCore G u :=
    ⟨by
        show limitFormEnergy G u < ⊤
        rw [← hE u]
        exact (E.energy_lt_top_iff u).2 hu.1,
      hu.2⟩
  have hv' : MemFormCore G v :=
    ⟨by
        show limitFormEnergy G v < ⊤
        rw [← hE v]
        exact (E.energy_lt_top_iff v).2 hv.1,
      hv.2⟩
  have hbi := aux_lem_endpoints_support_2_core_locality d hd model H om z0 r0 hr0 S hS G N Gn
    hGnEq hGnTendsto hbundle u v hu' hv' uc vc huc hvc hcu hcv hsv hsuQ hsvQ hsu
    c W hW hsupp hconst
  exact aux_lem_endpoints_support_2_form_eq_zero_of_bilinear E G hE u v hu.1 hv.1 hbi

def aux_lem_endpoints_lowerSet {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω) : Set ℝ :=
  {a : ℝ | ∀ i : ℕ, ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
    u ∈ limitFormDomain (GE i omega) →
      a * (limitFormEnergy (GE i omega) u).toReal ≤
        (limitFormEnergy (GF i omega) u).toReal}

def aux_lem_endpoints_upperSet {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω) : Set ℝ :=
  {a : ℝ | ∀ i : ℕ, ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
    u ∈ limitFormDomain (GE i omega) →
      (limitFormEnergy (GF i omega) u).toReal ≤
        a * (limitFormEnergy (GE i omega) u).toReal}

def aux_lem_endpoints_compare {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (C0 : ℝ) (omega : Ω) : Prop :=
  ∀ i : ℕ, limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
    ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
      u ∈ limitFormDomain (GE i omega) →
      C0⁻¹ * (limitFormEnergy (GE i omega) u).toReal ≤
          (limitFormEnergy (GF i omega) u).toReal ∧
        (limitFormEnergy (GF i omega) u).toReal ≤
          C0 * (limitFormEnergy (GE i omega) u).toReal

def aux_lem_endpoints_nonzero {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω) : Prop :=
  ∃ i : ℕ, ∃ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
    u ∈ limitFormDomain (GE i omega) ∧ 0 < (limitFormEnergy (GE i omega) u).toReal

def aux_lem_endpoints_catalogue (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ) : Prop :=
  ∃ (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (root : ℕ)
    (hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) ⊆
      (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
    (Dcat : ∀ i, Submodule ℚ
      (DomainL2 (centeredCube (z i) (r i) (hr i))))
    (hDcat : ∀ i, Countable (Dcat i))
    (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
    (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (traceH1 : ∀ i, ℕ → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (Sspace i).space)
    (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (Cext beta t : ℝ) (I : Paper.in_J d)
    (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
    (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
    (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
    letI : ∀ i, Countable (Dcat i) := hDcat
    conv_represented_estimates d hd model H Ω P NE (fun _ omega => field omega)
      ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t {1} I
      ℕ (fun i n omega => catalogResponse i (NE n) (field omega)) responseE
      (fun i n omega => catalogConstant i (NE n) (field omega)) eventE
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
    conv_represented_estimates d hd model H Ω P NF (fun _ omega => field omega)
      ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcF srcRepF ucellF Cext beta alpha eta t {1} I
      ℕ (fun i n omega => catalogResponse i (NF n) (field omega)) responseF
      (fun i n omega => catalogConstant i (NF n) (field omega)) eventF
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey

theorem lem_endpoints_support_2
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q) (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hlim : Tendsto GN atTop (𝓝 G))
    (hsym : ∀ n (x y : DomainL2 Q), inner ℝ (GN n x) y = inner ℝ x (GN n y))
    (hpos : ∀ n (x : DomainL2 Q), 0 ≤ inner ℝ x (GN n x)) :
    (∀ x y : DomainL2 Q, inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x : DomainL2 Q, 0 ≤ inner ℝ x (G x)) := by
  have happ (x : DomainL2 Q) : Tendsto (fun n => GN n x) atTop (𝓝 (G x)) :=
    ((ContinuousLinearMap.apply ℝ (DomainL2 Q) x).continuous.tendsto G).comp hlim
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have hL : Tendsto (fun n => inner ℝ (GN n x) y) atTop (𝓝 (inner ℝ (G x) y)) :=
      ((continuous_inner (𝕜 := ℝ) (E := DomainL2 Q)).tendsto _).comp
        ((happ x).prodMk_nhds tendsto_const_nhds)
    have hR : Tendsto (fun n => inner ℝ x (GN n y)) atTop (𝓝 (inner ℝ x (G y))) :=
      ((continuous_inner (𝕜 := ℝ) (E := DomainL2 Q)).tendsto _).comp
        ((tendsto_const_nhds (x := x)).prodMk_nhds (happ y))
    have hEq : (fun n => inner ℝ (GN n x) y) = (fun n => inner ℝ x (GN n y)) :=
      funext fun n => hsym n x y
    rw [hEq] at hL
    exact tendsto_nhds_unique hL hR
  · have hT : Tendsto (fun n => inner ℝ x (GN n x)) atTop (𝓝 (inner ℝ x (G x))) :=
      ((continuous_inner (𝕜 := ℝ) (E := DomainL2 Q)).tendsto _).comp
        ((tendsto_const_nhds (x := x)).prodMk_nhds (happ x))
    exact ge_of_tendsto hT (Eventually.of_forall fun n => hpos n x)

end Paper
