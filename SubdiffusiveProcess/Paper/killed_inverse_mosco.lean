import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.MeshError
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.CubeFractionalL2Norm
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_killed_inverse_mosco_dual
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : ℕ → PositiveCoefficient Ω)
    (EN : ℕ → DomainL2 Ω → EReal)
    (hEN : ∀ (n : ℕ) (u : DomainL2 Ω),
      EN n u = sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧
        e = (responseForm S (a n) w w : EReal)})
    (n : ℕ) (uN : ℕ → DomainL2 Ω) (f : DomainL2 Ω) :
    ((2 * inner ℝ f (uN n) -
      inverseResponse S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL) : ℝ) : EReal) ≤
      EN n (uN n) := by
  let L : S.space →L[ℝ] ℝ :=
    (sobolevVolumeLoad f).comp S.space.subtypeL
  let B : Set EReal := {e : EReal | ∃ w : S.space, w.val.1 = uN n ∧
    e = (responseForm S (a n) w w : EReal)}
  have hbound :
      ((2 * inner ℝ f (uN n) - inverseResponse S (a n) L : ℝ) : EReal) ≤
        sInf B := by
    apply le_sInf
    intro e he
    rcases he with ⟨w, hw, rfl⟩
    apply EReal.coe_le_coe_iff.mpr
    have hmax := (inverseResponse_isGreatest S (a n) L).2
      (show 2 * L w - responseForm S (a n) w w ∈
          Set.range (fun v : S.space =>
            2 * L v - responseForm S (a n) v v) from ⟨w, rfl⟩)
    change 2 * inner ℝ f w.val.1 - responseForm S (a n) w w ≤
      inverseResponse S (a n) L at hmax
    have hw' : inner ℝ f w.val.1 = inner ℝ f (uN n) := by
      simpa only [Function.comp_apply] using
        congrArg (fun x : DomainL2 Ω => inner ℝ f x) hw
    rw [hw'] at hmax
    linarith
  have hB : sInf B = EN n (uN n) := by
    simpa only [B, L] using (hEN n (uN n)).symm
  change ((2 * inner ℝ f (uN n) - inverseResponse S (a n) L : ℝ) : EReal) ≤
    EN n (uN n)
  exact hbound.trans_eq hB

theorem aux_killed_inverse_mosco_liminf
    (q r : ℕ → ℝ) (q₀ r₀ : ℝ) (E : ℕ → EReal)
    (hq : Tendsto q atTop (𝓝 q₀)) (hr : Tendsto r atTop (𝓝 r₀))
    (hpoint : ∀ n, ((2 * q n - r n : ℝ) : EReal) ≤ E n) :
    ((2 * q₀ - r₀ : ℝ) : EReal) ≤ liminf E atTop := by
  have hreal : Tendsto (fun n => 2 * q n - r n) atTop (𝓝 (2 * q₀ - r₀)) :=
    (tendsto_const_nhds.mul hq).sub hr
  have hereal : Tendsto (fun n => ((2 * q n - r n : ℝ) : EReal)) atTop
      (𝓝 ((2 * q₀ - r₀ : ℝ) : EReal)) := EReal.tendsto_coe.mpr hreal
  calc
    ((2 * q₀ - r₀ : ℝ) : EReal) = liminf (fun n => ((2 * q n - r n : ℝ) : EReal)) atTop :=
      hereal.liminf_eq.symm
    _ ≤ liminf E atTop := liminf_le_liminf (Eventually.of_forall hpoint)

theorem aux_killed_inverse_mosco_compact
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (GN : ℕ → DomainL2 (centeredCube z R hR) →L[ℝ]
      DomainL2 (centeredCube z R hR))
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
        K * responseForm S (a n) v v) :
    IsCompact (closure (⋃ n : ℕ,
      (GN n) '' Metric.closedBall (0 : DomainL2 (centeredCube z R hR)) 1)) := by
  let V : ℝ := volume.real (centeredCube z R hR : Set (SpatialCoordinates d))
  have hV : 0 < V := by
    dsimp [V]
    exact centeredCube_volume_pos z hR
  let c : ℝ := R ^ (-(Lane4.threeQuarterOrder : ℝ))
  have hc : 0 ≤ c := by
    dsimp [c]
    exact Real.rpow_nonneg hR.le _
  have hsqrtV : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hsqrtV_sq : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
  let M : ℝ := K / Real.sqrt V + c * (K / Real.sqrt V)
  have hnorm_bound (n : ℕ) (f : DomainL2 (centeredCube z R hR))
      (hf : ‖f‖ ≤ 1) :
      cubeFractionalL2Norm hd z R hR Lane4.threeQuarterOrder
        ⟨fun _ : Fin 1 =>
          (responseSolution S (a n)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1,
          (hCoercive n (responseSolution S (a n)
            ((sobolevVolumeLoad f).comp S.space.subtypeL))).1⟩ ≤ M := by
    let v : S.space := responseSolution S (a n)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)
    let x : ℝ := ‖v.val.1‖
    let q : ℝ :=
      (cubeFractionalL2Seminorm hd z R hR Lane4.threeQuarterOrder
        (fun _ : Fin 1 => v.val.1)).toReal
    have henergy : responseForm S (a n) v v = inner ℝ f v.val.1 := by
      rw [responseSolution_spec]
      rfl
    have hinner : inner ℝ f v.val.1 ≤ x := by
      calc
        inner ℝ f v.val.1 ≤ ‖inner ℝ f v.val.1‖ := le_abs_self _
        _ ≤ ‖f‖ * ‖v.val.1‖ := by
          simpa only [Real.norm_eq_abs] using
            norm_inner_le_norm (𝕜 := ℝ) f v.val.1
        _ ≤ x := by
          dsimp [x]
          nlinarith [mul_nonneg (sub_nonneg.mpr hf) (norm_nonneg v.val.1)]
    have hce := (hCoercive n v).2
    change x ^ 2 + V * q ^ 2 ≤ K * responseForm S (a n) v v at hce
    rw [henergy] at hce
    have hx : 0 ≤ x := norm_nonneg _
    have hxK : x ≤ K := by
      nlinarith [hce, hinner, mul_nonneg (mul_nonneg hK.le hx) hx]
    have hq : 0 ≤ q := by
      dsimp [q]
      exact ENNReal.toReal_nonneg
    have hqK : q ≤ K / Real.sqrt V := by
      apply (le_div_iff₀ hsqrtV).2
      nlinarith [hce, hinner, hxK, hsqrtV_sq,
        mul_nonneg hq (le_of_lt hsqrtV),
        mul_nonneg (mul_nonneg hq (le_of_lt hsqrtV))
          (mul_nonneg hq (le_of_lt hsqrtV))]
    have hsumsqrt : Real.sqrt (∑ i : Fin 1, ‖v.val.1‖ ^ 2) = x := by
      simp [x]
    change q + c *
      (Real.sqrt (∑ i : Fin 1, ‖v.val.1‖ ^ 2) / Real.sqrt V) ≤ M
    rw [hsumsqrt]
    dsimp [M]
    gcongr
  apply isCompact_closure_of_subseq_tendsto
  intro u hu
  have hu' : ∀ n, u n ∈ ⋃ k : ℕ,
      (GN k) '' Metric.closedBall (0 : DomainL2 (centeredCube z R hR)) 1 := hu
  choose k hk using fun n => Set.mem_iUnion.mp (hu' n)
  choose f hf huf using fun n => hk n
  have hfball : ∀ n, ‖f n‖ ≤ 1 := by
    intro n
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hf n)
  have hfrac (n : ℕ) :
      cubeFractionalL2Seminorm hd z R hR Lane4.threeQuarterOrder
          (fun _ : Fin 1 =>
            (responseSolution S (a (k n))
              ((sobolevVolumeLoad (f n)).comp S.space.subtypeL)).val.1) < ⊤ :=
    (hCoercive (k n)
      (responseSolution S (a (k n))
        ((sobolevVolumeLoad (f n)).comp S.space.subtypeL))).1
  let w : ℕ → CubeFractionalL2 (k := 1) hd z R hR Lane4.threeQuarterOrder :=
    fun n => ⟨fun _ : Fin 1 =>
      (responseSolution S (a (k n))
        ((sobolevVolumeLoad (f n)).comp S.space.subtypeL)).val.1, hfrac n⟩
  obtain ⟨sigma, hsigma, wlim, hwlim⟩ := hInterp.compact_embedding z R hR
    Lane4.threeQuarterOrder (by norm_num [Lane4.threeQuarterOrder]) w M
      (by
        intro n
        exact hnorm_bound (k n) (f n) (hfball n))
  refine ⟨wlim, sigma, hsigma, ?_⟩
  have hwu : ∀ n, u n = (w n).val 0 := by
    intro n
    calc
      u n = (GN (k n)) (f n) := (huf n).symm
      _ = (responseSolution S (a (k n))
          ((sobolevVolumeLoad (f n)).comp S.space.subtypeL)).val.1 := hGN _ _
      _ = (w n).val 0 := by rfl
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_apply, hwu] using hwlim



theorem killed_inverse_mosco
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
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
    (EN : ℕ → DomainL2 (centeredCube z R hR) → EReal)
    (hEN : ∀ (n : ℕ) (u : DomainL2 (centeredCube z R hR)),
      EN n u = sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧
        e = (responseForm S (a n) w w : EReal)}) :
    ∃! G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR),
      (Tendsto GN atTop (𝓝 G) ∧ IsCompactOperator G ∧
        (∀ x y : DomainL2 (centeredCube z R hR),
          inner ℝ (G x) y = inner ℝ x (G y)) ∧
        (∀ x : DomainL2 (centeredCube z R hR), 0 ≤ inner ℝ x (G x))) ∧
      (∀ (uN : ℕ → DomainL2 (centeredCube z R hR))
          (u : DomainL2 (centeredCube z R hR)),
        (∀ f : DomainL2 (centeredCube z R hR),
          Tendsto (fun n => inner ℝ f (uN n)) atTop
            (𝓝 (inner ℝ f u))) →
        limitFormEnergy G u ≤ liminf (fun n => EN n (uN n)) atTop) ∧
      (∀ u ∈ limitFormDomain G, ∃ w : ℕ → S.space,
        Tendsto (fun n => ((w n).val.1,
          (responseForm S (a n) (w n) (w n) : EReal))) atTop
        (𝓝 (u, limitFormEnergy G u))) := by
  have hDadd : ∀ x ∈ (D : Set (DomainL2 (centeredCube z R hR))),
      ∀ y ∈ (D : Set (DomainL2 (centeredCube z R hR))), x + y ∈ D := by
    intro x hx y hy
    exact D.add_mem hx hy
  have hsym : ∀ (n : ℕ) (x y : DomainL2 (centeredCube z R hR)),
      inner ℝ (GN n x) y = inner ℝ x (GN n y) := by
    intro n x y
    rw [hGN, hGN, real_inner_comm]
    exact volumeResponse_pairing_symm S (a n) y x
  have hpos : ∀ (n : ℕ) (x : DomainL2 (centeredCube z R hR)),
      0 ≤ inner ℝ x (GN n x) := by
    intro n x
    rw [hGN]
    exact volumeResponse_pairing_nonneg S (a n) x
  have hcompact := aux_killed_inverse_mosco_compact d hd z R hR S a GN hGN
    hInterp K hK hCoercive
  have hq : ∀ x ∈ (D : Set (DomainL2 (centeredCube z R hR))),
      CauchySeq (fun n => inner ℝ x (GN n x)) := by
    intro x hx
    let dx : D := ⟨x, hx⟩
    simpa only [dx] using hresponse dx
  obtain ⟨G, hG, hGuniq⟩ := existsUnique_limit_of_collectively_compact_quadratic_responses
    hDdense hDadd hsym hpos hcompact hq
  have hEval (f : DomainL2 (centeredCube z R hR)) :
      Continuous
        (fun T : DomainL2 (centeredCube z R hR) →L[ℝ]
          DomainL2 (centeredCube z R hR) => T f) :=
    (continuous_id : Continuous (fun T : DomainL2 (centeredCube z R hR) →L[ℝ]
      DomainL2 (centeredCube z R hR) => T)).clm_apply
      (continuous_const : Continuous
        (fun _ : DomainL2 (centeredCube z R hR) →L[ℝ]
          DomainL2 (centeredCube z R hR) => f))
  have hstrong : ∀ f : DomainL2 (centeredCube z R hR),
      Tendsto (fun n => (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) atTop (𝓝 (G f)) := by
    intro f
    have h := (hEval f).tendsto G |>.comp hG.1
    exact h.congr' (Eventually.of_forall (fun n => by
      change (GN n) f =
        (responseSolution S (a n)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1
      exact hGN n f))
  have hweakresponse : ∀ f : DomainL2 (centeredCube z R hR),
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (𝓝 (inner ℝ f (G f))) := by
    intro f
    have hi : Tendsto (fun n => inner ℝ f (GN n f)) atTop
        (𝓝 (inner ℝ f (G f))) := tendsto_const_nhds.inner
      ((hEval f).tendsto G |>.comp hG.1)
    exact hi.congr' (Eventually.of_forall (fun n => by
      calc
        inner ℝ f (GN n f) = inner ℝ f
            (responseSolution S (a n)
              ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 :=
          congrArg (fun x : DomainL2 (centeredCube z R hR) => inner ℝ f x)
            (hGN n f)
        _ = inverseResponse S (a n)
            ((sobolevVolumeLoad f).comp S.space.subtypeL) :=
          (inverseResponse_eq_load S (a n)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).symm))
  have hlower : ∀ (uN : ℕ → DomainL2 (centeredCube z R hR))
      (u : DomainL2 (centeredCube z R hR)),
      (∀ f : DomainL2 (centeredCube z R hR),
        Tendsto (fun n => inner ℝ f (uN n)) atTop
          (𝓝 (inner ℝ f u))) →
      limitFormEnergy G u ≤ liminf (fun n => EN n (uN n)) atTop := by
    intro uN u hweak
    refine iSup_le fun f => ?_
    refine aux_killed_inverse_mosco_liminf
      (fun n => inner ℝ f (uN n))
      (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL))
      (inner ℝ f u) (inner ℝ f (G f)) (fun n => EN n (uN n))
      (hweak f) (hweakresponse f) ?_
    intro n
    exact aux_killed_inverse_mosco_dual S a EN hEN n uN f
  have hrec (u : DomainL2 (centeredCube z R hR)) (hu : u ∈ limitFormDomain G) :
      ∃ w : ℕ → S.space,
        Tendsto (fun n => ((w n).val.1,
          (responseForm S (a n) (w n) (w n) : EReal))) atTop
          (𝓝 (u, limitFormEnergy G u)) := by
    change limitFormEnergy G u < (⊤ : EReal) at hu
    exact exists_responseForm_recoverySequence S a G hG.2.2.1 hG.2.2.2 hstrong u hu
  refine ⟨G, ?_, ?_⟩
  · exact ⟨⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2⟩, hlower, hrec⟩
  · intro G' hG'
    exact hGuniq G' hG'.1

end Paper
