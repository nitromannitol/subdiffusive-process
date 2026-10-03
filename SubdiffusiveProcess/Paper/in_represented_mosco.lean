module

public import SubdiffusiveProcess.Paper.in_represented_bounds
public import SubdiffusiveProcess.Paper.killed_inverse_mosco
public import SubdiffusiveProcess.Sobolev.ResponseRecovery
public import SubdiffusiveProcess.Sobolev.ResponsePositivity

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem aux_in_represented_mosco_free
    (d : ℕ) (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ)
    (Gn : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGnEq : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), Gn n f =
      (responseSolution S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hGnTendsto : Tendsto Gn atTop (𝓝 G)) :
    (∀ f g : DomainL2 (centeredCube z0 r0 hr0),
      (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ)) ∧
    (∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z0 r0 hr0)),
      (∀ f : DomainL2 (centeredCube z0 r0 hr0),
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n =>
          ((responseForm S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
            (wN n) (wN n) : ℝ) : EReal)) atTop) ∧
    (∀ w ∈ limitFormDomain G, ∃ wN : ℕ → S.space,
      Tendsto (fun n => ((wN n).val.1,
        (responseForm S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
          (wN n) (wN n) : EReal))) atTop (𝓝 (w, limitFormEnergy G w))) := by
  let a : ℕ → PositiveCoefficient (centeredCube z0 r0 hr0) :=
    fun n => Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0
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

/-- **DRAFT (STEP TPHDR, item B1), one candidate side.** `aux_in_represented_mosco_free`'s
package (`hGsymm`/`hLower`/`hRecovery`, free of any standing input beyond
`in_joint_extracted_candidates` itself) together with `aux_in_represented_bounds_side`'s package
(`KN≤Kstar`/`hcoercive`/`hInterp`/`hcutoffs` and the `prop_regularity` Hölder/mesh/smooth data) —
everything `prop_locality` and `prop_regularity` (minus `E`/`hE`/`hGmem`/`hGdense`) need, in one
`Prop`. -/
def aux_in_represented_mosco_side
    (d : ℕ) (hd : 2 ≤ d)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (S : ResponseSpace (centeredCube z0 r0 hr0))
    (G : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (N : ℕ → ℕ) : Prop :=
  (∀ f g : DomainL2 (centeredCube z0 r0 hr0),
    (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ)) ∧
  (∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z0 r0 hr0)),
    (∀ f : DomainL2 (centeredCube z0 r0 hr0),
      Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
    limitFormEnergy G w ≤
      liminf (fun n =>
        ((responseForm S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
          (wN n) (wN n) : ℝ) : EReal)) atTop) ∧
  (∀ w ∈ limitFormDomain G, ∃ wN : ℕ → S.space,
    Tendsto (fun n => ((wN n).val.1,
      (responseForm S (Lane4.cutoffPositiveCoefficient model H om (N n) z0 hr0)
        (wN n) (wN n) : EReal))) atTop (𝓝 (w, limitFormEnergy G w))) ∧
  aux_in_represented_bounds_side d hd model H om z0 r0 hr0 S G N

/-- **DRAFT (STEP TPHDR, item B1).** The Mosco package, per ω on the joint candidates'
full-measure event and per killed cube `i`, for both candidates `GE`/`GF` along `NE`/`NF`: derives
`hGsymm`/`hLower`/`hRecovery` fresh from `in_joint_extracted_candidates` alone (via
`aux_in_represented_mosco_free`, itself built from `killed_inverse_mosco`'s own internal helpers)
and re-exports `in_represented_bounds`'s own package unchanged. Not yet landed: no `sorry`, no new
axiom; `#print axioms` below. -/
theorem in_represented_mosco
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GN : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ)
    (hJoint : in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF)
    (hBounds : in_represented_bounds d hd model H Ω P field z r hr Sspace GE GF NE NF) :
    ∀ᵐ ω ∂P, ∀ i : ℕ,
      aux_in_represented_mosco_side d hd model H (field ω) (z i) (r i) (hr i)
        (Sspace i) (GE i ω) NE ∧
      aux_in_represented_mosco_side d hd model H (field ω) (z i) (r i) (hr i)
        (Sspace i) (GF i ω) NF := by
  obtain ⟨_, _, _, _, _, _, hGNeq, hconv⟩ := hJoint
  filter_upwards [hconv, hBounds] with ω hω hBω i
  obtain ⟨hEconv, hFconv⟩ := hω i
  obtain ⟨hBE, hBF⟩ := hBω i
  have hE := aux_in_represented_mosco_free d hd model H (field ω) (z i) (r i) (hr i) (Sspace i)
    (GE i ω) NE (fun n => GN i (NE n) ω) (fun n f => hGNeq i (NE n) ω f) hEconv
  have hF := aux_in_represented_mosco_free d hd model H (field ω) (z i) (r i) (hr i) (Sspace i)
    (GF i ω) NF (fun n => GN i (NF n) ω) (fun n f => hGNeq i (NF n) ω f) hFconv
  exact ⟨⟨hE.1, hE.2.1, hE.2.2, hBE⟩, ⟨hF.1, hF.2.1, hF.2.2, hBF⟩⟩

end Paper
