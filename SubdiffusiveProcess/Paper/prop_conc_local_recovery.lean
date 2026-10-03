module

public import Mathlib.Tactic
public import SubdiffusiveProcess.Compactness.SequentialCompactness
public import SubdiffusiveProcess.DirichletForm.FOTProduct
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.Paper.prop_locality_recovery

@[expose] public section

/-! Deterministic prop conc local recovery data extracted upstream of process convergence.
This module does not assert concentration or invoke the process-convergence theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace Paper
noncomputable section

/-- Extracted responseForm le local argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_local_recovery_responseForm_le_local
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (a b : PositiveCoefficient Q) (K : ℝ) (q : Set (SpatialCoordinates d))
    (u : S.space)
    (hcoeff : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ q → b.val x ≤ K * a.val x)
    (hgrad : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ q → u.val.2 i x = 0) :
    responseForm S b u u ≤ K * responseForm S a u u := by
  rw [aux_prop_locality_recovery_responseForm_eq_sum,
    aux_prop_locality_recovery_responseForm_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [weightedL2Form_apply, weightedL2Form_apply, ← integral_const_mul]
  apply integral_mono_ae (integrable_weighted_inner b.val _ _)
    ((integrable_weighted_inner a.val _ _).const_mul K)
  filter_upwards [hcoeff, hgrad i] with x hx hg
  simp only [RCLike.inner_apply, conj_trivial]
  by_cases hxq : x ∈ q
  · simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (hx hxq) (mul_self_nonneg (u.val.2 i x))
  · rw [hg hxq]
    simp only [mul_zero, le_refl]

/-- Extracted modV recovery argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_local_recovery_modV_recovery {d : ℕ} (hd : 2 ≤ d) (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hLower : ∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n) (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (cut : ℕ → S.space) (B : ℝ) (hB : 0 ≤ B)
    (hcutE : ∀ n, responseForm S (a n) (cut n) (cut n) ≤ B)
    (hgrowth : ∀ n, ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((cut n).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))
    (w : DomainL2 (centeredCube z r hr)) (hw : limitFormEnergy G w < ⊤)
    (Φ : ℕ → S.space) (hΦ1 : Tendsto (fun n => (Φ n).val.1) atTop (𝓝 w))
    (hΦE : Tendsto (fun n => responseForm S (a n) (Φ n) (Φ n)) atTop
      (𝓝 (limitFormEnergy G w).toReal))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (phi : ℕ → TestFunction (centeredCube z r hr) ℝ ⊤)
    (hPhi : ∀ n, (Φ n).val = smoothSobolevData (phi n))
    (hinner : ∀ n,
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        0 ≤ (cut n).val.1 x ∧ (cut n).val.1 x ≤ 1) ∧
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        w x ≠ 0 → (cut n).val.1 x = 1) ∧
      (∀ i, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        (cut n).val.2 i x ≠ 0 → w x = 0)) :
    Tendsto (fun n =>
      ((aux_prop_locality_recovery_modV S hS (phi n) (cut n)).val.1,
       (responseForm S (a n)
         (aux_prop_locality_recovery_modV S hS (phi n) (cut n))
         (aux_prop_locality_recovery_modV S hS (phi n) (cut n)) : EReal)))
      atTop (𝓝 (w, limitFormEnergy G w)) := by
  have hp := fun n => aux_prop_locality_recovery_modV_props S hS
    (phi n) (Φ n) (hPhi n) (cut n) w
    (hinner n).1 (hinner n).2.1 (hinner n).2.2
  exact aux_prop_locality_recovery_side hd hInterp z r hr t ht S a G
    hLower KN hKN Kstar hKstar hfrac hcoercive cut B hB hcutE hgrowth
    w hw Φ hΦ1 hΦE (fun n => aux_prop_locality_recovery_modV S hS (phi n) (cut n))
    (fun n i => aux_prop_locality_recovery_mulL
      (aux_prop_locality_recovery_testPartialLinf (phi n) i) (cut n).val.1)
    (fun n i => aux_prop_locality_recovery_mulL
      (aux_prop_locality_recovery_testLinf (phi n)) ((cut n).val.2 i))
    (fun n i => aux_prop_locality_recovery_modV_grad S hS (phi n) (cut n) i)
    (fun n => (hp n).1) (fun n => (hp n).2.1) (fun n => (hp n).2.2)

/-- Extracted modV grad zero argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_local_recovery_modV_grad_zero
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (phi : TestFunction Q ℝ ⊤) (chi : S.space) (chic : SpatialCoordinates d → ℝ)
    (hchi : (chi.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic)
    (O q : Set (SpatialCoordinates d)) (hOq : closure O ⊆ q)
    (hzero : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ O → chic x = 0) :
    ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ q → (aux_prop_locality_recovery_modV S hS phi chi).val.2 i x = 0 := by
  let Y := aux_prop_locality_recovery_modV S hS phi chi
  have hz : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ (closure O)ᶜ → Y.val.1 x = 0 := by
    filter_upwards [aux_prop_locality_recovery_modV_fst_ae S hS phi chi,
      hchi, ae_restrict_mem Q.isOpen.measurableSet] with x hx hcx hxQ hxO
    change (aux_prop_locality_recovery_modV S hS phi chi).val.1 x = 0
    rw [hx, hcx, hzero x hxQ (fun h => hxO (subset_closure h)), mul_zero]
  intro i
  have hg := aux_prop_locality_recovery_grad_ae_zero_of_const Y.val
    (S.le_weak Y.2) (closure O)ᶜ isClosed_closure.isOpen_compl 0 hz i
  filter_upwards [hg] with x hx hxq
  exact hx (fun hxO => hxq (hOq hxO))

/-- Extracted localized recovery base argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_local_recovery_localized_recovery_base
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    let Q := centeredCube z r hr
    let H := DomainL2 Q
    ∀ (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (a : ℕ → PositiveCoefficient Q)
    (G : H →L[ℝ] H)
    (hLower : ∀ (wN : ℕ → S.space) (w : H),
      (∀ f : H, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (hRecovery : ∀ w ∈ limitFormDomain G, ∃ wN : ℕ → S.space,
      Tendsto (fun n => ((wN n).val.1,
        ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop
        (𝓝 (w, limitFormEnergy G w)))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (Q : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (hqQ : q ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (u : DomainL2 (centeredCube z r hr)) (hu : u ∈ limitFormDomain G)
    (uc : SpatialCoordinates d → ℝ) (huc : Continuous uc)
    (hucs : HasCompactSupport uc) (hucq : tsupport uc ⊆ q)
    (huae : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc),
    ∃ Y : ℕ → S.space,
      Tendsto (fun n => ((Y n).val.1,
        (responseForm S (a n)
          (Y n) (Y n) : EReal))) atTop (𝓝 (u, limitFormEnergy G u)) ∧
      ∀ n (i : Fin d), ∀ᵐ x ∂volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d)),
        x ∉ q → (Y n).val.2 i x = 0 := by
  intro Q H S hS a G hLower hRecovery KN hKN Kstar hKstar hfrac hcoercive
    hInterp t ht _htd hcutoffs q hq hqQ u hu uc huc hucs hucq huae
  have hb1 := exists_open_between_and_isCompact_closure hucs.isCompact hq hucq
  obtain ⟨O, hO, hKO, hOq, _hOc⟩ := hb1
  have hb2 := hcutoffs (tsupport uc) O hucs.isCompact hO hKO (hOq.trans hqQ)
  obtain ⟨V, chi, chic, B, hV, hKV, _hVO, hB, hchi⟩ := hb2
  have hb3 := hRecovery u hu
  obtain ⟨vN, hvN⟩ := hb3
  have hb4 := aux_prop_locality_recovery_recovery_parts
    (fun n => (vN n).val.1) (fun n => responseForm S (a n) (vN n) (vN n))
    u (limitFormEnergy G u) (limitFormEnergy_nonneg G u) hu hvN
  obtain ⟨hvN1, hvNE⟩ := hb4
  have hb5 := aux_prop_locality_recovery_smooth_seq S hS a vN u _ hvN1 hvNE
  obtain ⟨phi, Phi, hPhi, hPhi1, hPhiE⟩ := hb5
  let Y := fun n => aux_prop_locality_recovery_modV S hS (phi n) (chi n)
  have hin := fun n => aux_prop_locality_recovery_inner_ae
    (chi n).val (S.le_weak (chi n).2) (chic n)
    (hchi n).2.1 (hchi n).2.2.1 V hV (hchi n).2.2.2.1
    u uc huae hKV
  have hrec := Paper.aux_prop_conc_local_recovery_modV_recovery hd hInterp z r hr t ht S a G
    hLower KN hKN Kstar hKstar hfrac hcoercive chi B hB
    (fun n => (hchi n).2.2.2.2.2.1) (fun n => (hchi n).2.2.2.2.2.2)
    u hu Phi hPhi1 hPhiE hS phi hPhi hin
  refine ⟨Y, hrec, ?_⟩
  intro n
  exact Paper.aux_prop_conc_local_recovery_modV_grad_zero S hS (phi n) (chi n) (chic n)
    (hchi n).2.1 O q hOq (hchi n).2.2.2.2.1

/-- Extracted energy order of recovery argument from the pre-convergence deterministic proof. -/
theorem prop_conc_local_recovery
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (a b : ℕ → PositiveCoefficient Q)
    (GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hlower : ∀ (vN : ℕ → S.space) (v : DomainL2 Q),
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      limitFormEnergy GF v ≤
        liminf (fun n => (responseForm S (b n) (vN n) (vN n) : EReal)) atTop)
    (u : DomainL2 Q) (Eu K : ℝ) (Y : ℕ → S.space)
    (hY : Tendsto (fun n => ((Y n).val.1,
      (responseForm S (a n) (Y n) (Y n) : EReal))) atTop (𝓝 (u, (Eu : EReal))))
    (horder : ∀ᶠ n in atTop,
      responseForm S (b n) (Y n) (Y n) ≤ K * responseForm S (a n) (Y n) (Y n)) :
    limitFormEnergy GF u ≤ ((K * Eu : ℝ) : EReal) := by
  have he : Tendsto (fun n => responseForm S (a n) (Y n) (Y n)) atTop (𝓝 Eu) :=
    EReal.tendsto_coe.mp hY.snd_nhds
  have hbound : Tendsto (fun n => ((K * responseForm S (a n) (Y n) (Y n) : ℝ) : EReal))
      atTop (𝓝 ((K * Eu : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr (tendsto_const_nhds.mul he)
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun n => (responseForm S (b n) (Y n) (Y n) : EReal)) := by
    change ∃ bound : EReal, ∀ᶠ n : ℕ in atTop,
      (responseForm S (b n) (Y n) (Y n) : EReal) ≥ bound
    refine ⟨0, Eventually.of_forall ?_⟩
    intro n
    exact EReal.coe_nonneg.mpr (responseForm_nonneg S (b n) (Y n))
  have hlim := Filter.liminf_le_liminf
    (horder.mono (fun n hn => EReal.coe_le_coe_iff.mpr hn)) hbdd hbound.isCoboundedUnder_ge
  rw [hbound.liminf_eq] at hlim
  exact (hlower Y u (fun f => tendsto_const_nhds.inner hY.fst_nhds)).trans hlim

end
end Paper
