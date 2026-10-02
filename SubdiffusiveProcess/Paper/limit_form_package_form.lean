import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Sobolev.ReflectionResponses
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.limit_form_package_regularity_supply
import SubdiffusiveProcess.Paper.energy_order_of_form_order
import SubdiffusiveProcess.Paper.killed_inverse_mosco
import SubdiffusiveProcess.Paper.prop_killed_inverse
import SubdiffusiveProcess.Paper.prop_killed_inverse_dirichlet_form
import SubdiffusiveProcess.Paper.prop_locality

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_limit_form_package_mosco_free
    (d : ℕ) (hd : 2 ≤ d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (a : ℕ → PositiveCoefficient (centeredCube z0 r0 hr0))
    (Gn : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGnEq : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), Gn n f =
      (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hGnTendsto : Tendsto Gn atTop (𝓝 G)) :
    (∀ f g : DomainL2 (centeredCube z0 r0 hr0),
      (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ)) ∧
    (∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z0 r0 hr0)),
      (∀ f : DomainL2 (centeredCube z0 r0 hr0),
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n =>
          ((responseForm S (a n)
            (wN n) (wN n) : ℝ) : EReal)) atTop) ∧
    (∀ w ∈ limitFormDomain G, ∃ wN : ℕ → S.space,
      Tendsto (fun n => ((wN n).val.1,
        (responseForm S (a n)
          (wN n) (wN n) : EReal))) atTop (𝓝 (w, limitFormEnergy G w))) := by
  have hsym : ∀ (n : ℕ) (x y : DomainL2 (centeredCube z0 r0 hr0)),
      inner ℝ (Gn n x) y = inner ℝ x (Gn n y) := by
    intro n x y
    rw [hGnEq, hGnEq, real_inner_comm]
    exact volumeResponse_pairing_symm S (a n) y x
  have hpos : ∀ (n : ℕ) (x : DomainL2 (centeredCube z0 r0 hr0)),
      0 ≤ inner ℝ x (Gn n x) := by
    intro n x
    rw [hGnEq]
    exact volumeResponse_pairing_nonneg S (a n) x
  have hEval (f : DomainL2 (centeredCube z0 r0 hr0)) :
      Continuous (fun T : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ]
        DomainL2 (centeredCube z0 r0 hr0) => T f) :=
    (continuous_id : Continuous (fun T : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ]
      DomainL2 (centeredCube z0 r0 hr0) => T)).clm_apply
      (continuous_const : Continuous
        (fun _ : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ]
          DomainL2 (centeredCube z0 r0 hr0) => f))
  have hstrong : ∀ f : DomainL2 (centeredCube z0 r0 hr0),
      Tendsto (fun n => Gn n f) atTop (𝓝 (G f)) := fun f =>
    (hEval f).tendsto G |>.comp hGnTendsto
  have hGsymm : ∀ f g : DomainL2 (centeredCube z0 r0 hr0),
      (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ) := by
    intro f g
    have e1 : Tendsto (fun n => (inner ℝ f (Gn n g) : ℝ)) atTop (𝓝 (inner ℝ f (G g) : ℝ)) :=
      tendsto_const_nhds.inner (hstrong g)
    have e2 : Tendsto (fun n => (inner ℝ g (Gn n f) : ℝ)) atTop (𝓝 (inner ℝ g (G f) : ℝ)) :=
      tendsto_const_nhds.inner (hstrong f)
    have e3 : (fun n => (inner ℝ f (Gn n g) : ℝ)) = (fun n => (inner ℝ g (Gn n f) : ℝ)) :=
      funext (fun n => (real_inner_comm f (Gn n g)).symm.trans (hsym n g f))
    rw [e3] at e1
    exact tendsto_nhds_unique e1 e2
  have hGpos : ∀ x : DomainL2 (centeredCube z0 r0 hr0), 0 ≤ (inner ℝ x (G x) : ℝ) := by
    intro x
    have e : Tendsto (fun n => (inner ℝ x (Gn n x) : ℝ)) atTop (𝓝 (inner ℝ x (G x) : ℝ)) :=
      tendsto_const_nhds.inner (hstrong x)
    exact ge_of_tendsto' e (fun n => hpos n x)
  have hweakresponse : ∀ f : DomainL2 (centeredCube z0 r0 hr0),
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (𝓝 (inner ℝ f (G f))) := by
    intro f
    have hi : Tendsto (fun n => inner ℝ f (Gn n f)) atTop (𝓝 (inner ℝ f (G f))) :=
      tendsto_const_nhds.inner (hstrong f)
    exact hi.congr' (Eventually.of_forall (fun n => by
      calc
        inner ℝ f (Gn n f) = inner ℝ f
            (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 :=
          congrArg (fun x : DomainL2 (centeredCube z0 r0 hr0) => inner ℝ f x) (hGnEq n f)
        _ = inverseResponse S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL) :=
          (inverseResponse_eq_load S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).symm))
  let EN : ℕ → DomainL2 (centeredCube z0 r0 hr0) → EReal :=
    fun n u => sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧
      e = (responseForm S (a n) w w : EReal)}
  have hEN : ∀ (n : ℕ) (u : DomainL2 (centeredCube z0 r0 hr0)),
      EN n u = sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧
        e = (responseForm S (a n) w w : EReal)} := fun _ _ => rfl
  have hlower : ∀ (uN : ℕ → DomainL2 (centeredCube z0 r0 hr0))
      (u : DomainL2 (centeredCube z0 r0 hr0)),
      (∀ f : DomainL2 (centeredCube z0 r0 hr0),
        Tendsto (fun n => inner ℝ f (uN n)) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy G u ≤ liminf (fun n => EN n (uN n)) atTop := by
    intro uN u hweak
    refine iSup_le fun f => ?_
    refine aux_killed_inverse_mosco_liminf
      (fun n => inner ℝ f (uN n))
      (fun n => inverseResponse S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL))
      (inner ℝ f u) (inner ℝ f (G f)) (fun n => EN n (uN n))
      (hweak f) (hweakresponse f) ?_
    intro n
    exact aux_killed_inverse_mosco_dual S a EN hEN n uN f
  refine ⟨hGsymm, ?_, ?_⟩
  · intro wN w hweak
    have h1 := hlower (fun n => (wN n).val.1) w hweak
    have h2 : ∀ n, EN n ((wN n).val.1) ≤
        ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal) := by
      intro n
      rw [hEN]
      exact sInf_le ⟨wN n, rfl, rfl⟩
    exact h1.trans (liminf_le_liminf (Eventually.of_forall h2))
  · intro u hu
    have hu' : (⨆ f : DomainL2 (centeredCube z0 r0 hr0),
        ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) < ⊤ := hu
    have hsym' : ∀ x y : DomainL2 (centeredCube z0 r0 hr0),
        inner ℝ (G x) y = inner ℝ x (G y) := fun x y =>
      (real_inner_comm (G x) y).symm.trans (hGsymm y x)
    have hstrong' : ∀ f : DomainL2 (centeredCube z0 r0 hr0),
        Tendsto (fun n => (responseSolution S (a n)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) atTop (𝓝 (G f)) :=
      fun f => (hstrong f).congr' (Eventually.of_forall (fun n => hGnEq n f))
    exact exists_responseForm_recoverySequence S a G hsym' hGpos hstrong' u hu'

theorem aux_limit_form_package_property_of_limit {V : Type*} [TopologicalSpace V] [T2Space V]
    (GN : ℕ → V) (G : V) (hconv : Tendsto GN atTop (𝓝 G))
    (property : V → Prop) (hconv_of : ∀ x, property x → Tendsto GN atTop (𝓝 x))
    (hex : ∃! x, property x) : property G := by
  obtain ⟨x, hx, _⟩ := hex
  have hxG : x = G := tendsto_nhds_unique (hconv_of x hx) hconv
  exact hxG ▸ hx

theorem aux_limit_form_package_inverse_limit_form
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
  have hGc := aux_limit_form_package_property_of_limit GN G hconv _
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

theorem aux_limit_form_package_response_cauchy {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (GN : ℕ → V →L[ℝ] V) (G : V →L[ℝ] V)
    (hconv : Tendsto GN atTop (𝓝 G)) (f : V) :
    CauchySeq (fun n => inner ℝ f (GN n f)) := by
  have heval := ((ContinuousLinearMap.apply ℝ V f).continuous.tendsto G).comp hconv
  exact (tendsto_const_nhds.inner heval).cauchySeq

theorem aux_limit_form_package_hregularity_construct
    {d : ℕ} (hd : 2 ≤ d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (Sspace0 : ResponseSpace (centeredCube z0 r0 hr0))
    (hSspace0 : Sspace0.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (a0 : ℕ → PositiveCoefficient (centeredCube z0 r0 hr0))
    (hcontract0 : ∀ (n : ℕ) (T : ℝ → ℝ),
      DirichletForm.IsNormalContraction T → ∀ u : Sspace0.space,
        ∃ v : Sspace0.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm Sspace0
              (a0 n) v v ≤
            responseForm Sspace0
              (a0 n) u u)
    (G0 : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (GN0 : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGN0 : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), GN0 n f =
      (responseSolution Sspace0
          (a0 n)
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
          (a0 n) v v)
    (D : Submodule ℚ (DomainL2 (centeredCube z0 r0 hr0)))
    (hDcount : (D : Set (DomainL2 (centeredCube z0 r0 hr0))).Countable)
    (hDdense : Dense (D : Set (DomainL2 (centeredCube z0 r0 hr0))))
    (hDsmooth : ∀ f : D, ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧
      HasCompactSupport fc ∧
      tsupport fc ⊆ (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ∧
      (f.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))] fc)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (hbundle0 : in_represented_bounds_seq d hd z0 r0 hr0 Sspace0 a0 G0) :
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
            (a0 n) (vN n) (vN n) : ℝ) :
              EReal)) atTop) := by
  exact aux_limit_form_package_inverse_limit_form d hd z0 r0 hr0 Sspace0 hSspace0
    (fun n => a0 n)
    hcontract0 GN0 hGN0 hInterp K hK0 hCoercive D hDcount hDdense hDsmooth
    (fun f => aux_limit_form_package_response_cauchy GN0 G0 hGN0tendsto f.val)
    (aux_limit_form_package_endpoint_invariance_hmesh_of_bounds_side hd z0 r0 hr0
      Sspace0 G0 a0 hbundle0) G0 hGN0tendsto

theorem limit_form_package_form
    {d : ℕ} (hd : 2 ≤ d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (Sspace0 : ResponseSpace (centeredCube z0 r0 hr0))
    (hSspace0 : Sspace0.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (a0 : ℕ → PositiveCoefficient (centeredCube z0 r0 hr0))
    (hcontract0 : ∀ (n : ℕ) (T : ℝ → ℝ),
      DirichletForm.IsNormalContraction T → ∀ u : Sspace0.space,
        ∃ v : Sspace0.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm Sspace0
              (a0 n) v v ≤
            responseForm Sspace0
              (a0 n) u u)
    (G0 : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (GN0 : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGN0 : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), GN0 n f =
      (responseSolution Sspace0
          (a0 n)
          ((sobolevVolumeLoad f).comp Sspace0.space.subtypeL)).val.1)
    (hGN0tendsto : Tendsto GN0 atTop (𝓝 G0))
    (hbundle0 : in_represented_bounds_seq d hd z0 r0 hr0 Sspace0 a0 G0) :
    ∃ E : _root_.DirichletForm
        (volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))),
      E.domain = limitFormDomain G0 ∧
      (∀ v : DomainL2 (centeredCube z0 r0 hr0),
        E.toClosedForm.energy v = limitFormEnergy G0 v) ∧
      ∃ Cc : Set (DomainL2 (centeredCube z0 r0 hr0)),
        DirichletForm.IsCoreOn E.toClosedForm
          (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) Cc := by
  obtain ⟨K, hK0, hCoercive, D, hDcount, hDdense, hDsmooth, hInterp⟩ :=
    limit_form_package_regularity_supply hd z0 r0 hr0 Sspace0 G0 a0 hbundle0
  obtain ⟨EForm, Rroot, hE, hSymmC, hRsymm, hRcomp, hRdom, hRinj, hLower⟩ :=
    aux_limit_form_package_hregularity_construct hd z0 r0 hr0 Sspace0 hSspace0 a0 hcontract0 G0 GN0 hGN0
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
  have hRange := aux_limit_form_package_hregularity_hRange_of_root G0 Rroot EForm hE hSymmC hRsymm hRcomp hRinj
    hRdom hGmem hEdomIff
  have hGbound := aux_limit_form_package_hregularity_hGbound_of_root G0 Rroot EForm hE hSymmC hRsymm hRcomp hRinj
    hGmem
  obtain ⟨⟨Cc, hCc⟩, _hIsRegular⟩ :=
    aux_limit_form_package_regularity_instance_killed d hd z0 r0 hr0 Sspace0 hSspace0 a0 G0 EForm
      hE hGmem hLower hbundle0 hRange hGbound
  exact ⟨EForm, Set.ext hEdomIff, hE, Cc, hCc⟩

theorem aux_limit_form_package_energy_measure_support
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

theorem aux_limit_form_package_core_locality
    (d : ℕ) (hd : 2 ≤ d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (hS : S.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (a : ℕ → PositiveCoefficient (centeredCube z0 r0 hr0))
    (Gn : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGnEq : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), Gn n f =
      (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hGnTendsto : Tendsto Gn atTop (𝓝 G))
    (hbundle : in_represented_bounds_seq d hd z0 r0 hr0 S a G) :
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
  have hMosco := aux_limit_form_package_mosco_free d hd z0 r0 hr0 S G a Gn hGnEq hGnTendsto
  obtain ⟨KN, hKN, Kstar, hKstar, hfrac, hcoercive, hInterp, t, ht, htd, hcutoffs, _⟩ := hbundle
  exact prop_locality d hd z0 r0 hr0 S hS
    (fun n => a n) G
    hMosco.1 hMosco.2.1 hMosco.2.2 KN hKN Kstar hKstar hfrac hcoercive hInterp
    t ht htd hcutoffs

theorem aux_limit_form_package_form_eq_zero_of_bilinear
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

theorem aux_limit_form_package_form_core_locality
    (d : ℕ) (hd : 2 ≤ d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (hS : S.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (a : ℕ → PositiveCoefficient (centeredCube z0 r0 hr0))
    (Gn : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGnEq : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), Gn n f =
      (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hGnTendsto : Tendsto Gn atTop (𝓝 G))
    (hbundle : in_represented_bounds_seq d hd z0 r0 hr0 S a G)
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
  have hbi := aux_limit_form_package_core_locality d hd z0 r0 hr0 S hS G a Gn
    hGnEq hGnTendsto hbundle u v hu' hv' uc vc huc hvc hcu hcv hsv hsuQ hsvQ hsu
    c W hW hsupp hconst
  exact aux_limit_form_package_form_eq_zero_of_bilinear E G hE u v hu.1 hv.1 hbi

theorem aux_limit_form_package_energy_coe {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) (hu : u ∈ limitFormDomain G) :
    limitFormEnergy G u = ((limitFormEnergy G u).toReal : EReal) := by
  have hu' : limitFormEnergy G u < ⊤ := hu
  exact (EReal.coe_toReal (ne_of_lt hu')
    (ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg G u)))).symm

end Paper
