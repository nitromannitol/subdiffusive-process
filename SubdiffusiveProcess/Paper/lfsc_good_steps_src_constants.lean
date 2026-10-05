module

public import SubdiffusiveProcess.Paper.lfsc_good_steps_src_zero
public import SubdiffusiveProcess.Paper.lfsc_regboth_witness
public import SubdiffusiveProcess.Paper.lfsgs_trace_witness
public import SubdiffusiveProcess.Paper.infrared_characterization_local_lipschitz_majorant
public import SubdiffusiveProcess.Paper.lem_finite_stopping_moments

@[expose] public section

/-!
# `lfsc_good_steps_src_constants` — the sourced good-step event outside one small event

Constants of the sourced finite stopping construction (paper `\label{mfd:lem-finite-source-comparison}`,
"use the partition of the proof of Lemma `mfd:lem-finite-stopping`", both infrared coefficients).  Exactly as
`lfsgs_good_steps_constants` (the unsourced ChildA): the geometric exponents and a witness rate exceeding the branch
entropy are fixed before the model.  The exceptional event depends on `(N, M)` only: it is the union of the interval-packing
events for `A` and for `A^0`, and the event `{Lip(H; root) > 3^{N/8}}` (moment of `infrared_characterization_local_lipschitz_majorant`)
that keeps the weight `w = e^{-H}` almost constant, `sup_q w/ inf_q w ≤ 1 + rho`, on every working cube. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.FiniteStopping
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.Paper

open Classical in
theorem lfsc_good_steps_src_constants
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Step : @cutoff_good_scale_input d ⟨by omega⟩)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Dbase : @sum_errors_baseline_input d ⟨by omega⟩ _ _) :
    haveI instNeZeroDimension : NeZero d := ⟨by omega⟩
    ∃ P : ℕ, 1 ≤ P ∧
    ∀ θbad : ℝ, 0 < θbad → ∃ H1min : ℕ, ∀ H1 : ℕ, H1min ≤ H1 → 0 < H1 →
    ∃ Cg delta0 : ℝ, 0 < Cg ∧ 0 < delta0 ∧
    ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d model)
      (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ delta0 →
    ∀ (z : SpatialCoordinates d) (j : ℤ),
    ∀ eta : ℝ, 0 < eta → ∀ rho : ℝ, 0 < rho → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
    ∀ N M : ℕ, N0 ≤ N → N ≤ M →
      ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
        (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
        ∀ omega ∉ Bad, ∀ reverse : Bool,
          good_steps_src_at model H P H1 θbad Cg eta 1 z j N M reverse omega ∧
          good_steps_src_at model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) P H1 θbad Cg eta
            (1 + rho) z j N M reverse omega := by
  classical
  let instDimension : NeZero d := ⟨by omega⟩
  refine ⟨2, by norm_num, ?_⟩
  intro thetaBad hthetaBad
  refine ⟨4, ?_⟩
  intro H1 hH1min hH1
  let alpha : ℝ := 3 / 4
  let beta : ℝ := (1 / 2 + alpha) / 2
  have hbeta : 1 / 2 < beta := by dsimp [beta, alpha]; norm_num
  have hba : beta < alpha := by dsimp [beta]; linarith only [hd, hthetaBad, hH1min, hH1, hbeta]
  have halpha : alpha < 1 := by dsimp [alpha]; norm_num
  have halphaLower : 1 / 2 < alpha := by dsimp [alpha]; norm_num
  let thetaPack : ℝ := min (thetaBad / 2) (1 / 4)
  have hthetaPack : 0 < thetaPack := by
    apply lt_min
    · positivity
    · norm_num
  have hthetaPack_le : thetaPack ≤ thetaBad := by
    dsimp [thetaPack]
    exact (min_le_left _ _).trans (by linarith only [hd, hthetaBad, hH1min, hH1, hbeta])
  have hthetaPack_gap : thetaPack < (3 / 4 : ℝ) - 1 / 4 := by
    have hq : thetaPack ≤ 1 / 4 := (min_le_right _ _)
    norm_num at hq ⊢
    linarith only [hd, hthetaBad, hH1min, hH1, hbeta, hba, halpha, halphaLower, hthetaPack, hthetaPack_le, hq]
  let B : ℝ := 2000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / thetaPack
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hB : B > 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / thetaPack := by
    have hbase : 0 < 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / thetaPack := by
      positivity
    dsimp [B]
    calc
      2000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / thetaPack =
          2 * (1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / thetaPack) := by ring
      _ > 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / thetaPack := by
        linarith only [hbase]
  obtain ⟨Cfin, pad, deltaReg, sigmaReg, epsReg, hCfin, hpad, hpadle3,
      hdeltaReg, hsigmaReg, hepsReg, hRegSup⟩ :=
    _root_.SubdiffusiveProcess.Paper.lfsc_regboth_witness d hd Jc Pc Xc Sf W Cp Step D Dbase alpha beta B hbeta hba halpha
      hBpos H1 hH1 hH1min
  obtain ⟨deltaTrace, hdeltaTrace, hTraceSup⟩ :=
    _root_.SubdiffusiveProcess.Paper.lfsgs_trace_witness d hd Jc Pc Xc Sf W Cp Step D hES Dbase
      alpha halphaLower halpha B hBpos
  refine ⟨2 * Cfin ^ 2, min deltaReg deltaTrace, by positivity, lt_min hdeltaReg hdeltaTrace, ?_⟩
  intro model _Rm Sreg _It H hH hdelta z j eta heta rho hrho
  have hdeltaRegModel : model.delta ≤ deltaReg := le_trans hdelta (min_le_left _ _)
  have hdeltaTraceModel : model.delta ≤ deltaTrace := le_trans hdelta (min_le_right _ _)
  have hReg2 := fun (N k : ℕ) (zc : SpatialCoordinates d) (hkN : k ≤ N) =>
    hRegSup model _Rm Sreg _It H hH hdeltaRegModel N k zc hkN
  have hTraceM : has_trace_windows model H alpha B :=
    hTraceSup model _Rm Sreg _It H hH hdeltaTraceModel
  obtain ⟨C1, γ1, N01, hC1, hγ1, hw1⟩ :=
    lfsc_good_steps_src hd H1 hH1 thetaBad thetaPack alpha Cfin pad B hthetaPack
      hthetaPack_le hthetaPack_gap hCfin hpad hpadle3 hB model H
      (fun N k zc hkN => (hReg2 N k zc hkN).1) hTraceM z j eta heta
  obtain ⟨C2, γ2, N02, hC2, hγ2, hw2⟩ :=
    lfsc_good_steps_src_zero hd H1 hH1 thetaBad thetaPack alpha Cfin pad B hthetaPack
      hthetaPack_le hthetaPack_gap hCfin hpad hpadle3 hB model H
      (fun N k zc hkN => (hReg2 N k zc hkN).2) hTraceM z j eta heta
  -- the Lipschitz constant of `H` on the root cube
  have hr : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  obtain ⟨CL, hCL, hLipG⟩ :=
    infrared_characterization_local_lipschitz_majorant d hd z ((3 : ℝ) ^ j) hr 1 le_rfl
  obtain ⟨G, hG0, hGlip, hGmem, hGnorm⟩ := hLipG model H hH
  obtain ⟨Ctail, hCtail, hloc⟩ :=
    _root_.SubdiffusiveProcess.Paper.lem_finite_stopping_moments d model 1 1 (CL * model.delta * Real.sqrt 1) le_rfl
      (fun _ _ => G) (fun _ _ => hGmem) (fun _ _ => hGnorm)
  -- the threshold `N03`: `3^{-N/8} ≤ log(1+rho)`
  have hlogpos : 0 < Real.log (1 + rho) := Real.log_pos (by linarith)
  obtain ⟨N03, hN03⟩ : ∃ n : ℕ, (Real.log (1 + rho))⁻¹ < (3 : ℝ) ^ (n : ℕ) :=
    pow_unbounded_of_one_lt _ (by norm_num)
  have hnull : (chaosSampleLaw model).toMeasure
      {om | ¬ (∀ x y, x ∈ (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) →
        y ∈ (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) →
        |H om x - H om y| ≤ G om * dist x y)} = 0 := ae_iff.1 hGlip
  refine ⟨C1 + C2 + Ctail, min (min γ1 γ2) (1 / 8), max (max N01 N02) (max (8 * N03) 1),
    by positivity, lt_min (lt_min hγ1 hγ2) (by norm_num), ?_⟩
  intro N M hN hNM
  have hN01 : N01 ≤ N := by omega
  have hN02 : N02 ≤ N := by omega
  have hN03' : 8 * N03 ≤ N := by omega
  obtain ⟨Bad1, hB1m, hB1p, hB1⟩ := hw1 N M hN01 hNM
  obtain ⟨Bad2, hB2m, hB2p, hB2⟩ := hw2 N M hN02 hNM
  obtain ⟨Bad0, hB0m, hB0p, hB0⟩ := hloc (1 / 8) (by norm_num) N M
  set Gc := {om | ¬ (∀ x y, x ∈ (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) →
        y ∈ (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) →
        |H om x - H om y| ≤ G om * dist x y)} with hGc
  have hB3p : (chaosSampleLaw model).toMeasure (Bad0 ∪ toMeasurable (chaosSampleLaw model).toMeasure Gc) ≤
      ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-(1 / 8 : ℝ) * (N : ℝ))) := by
    calc _ ≤ (chaosSampleLaw model).toMeasure Bad0 +
          (chaosSampleLaw model).toMeasure (toMeasurable (chaosSampleLaw model).toMeasure Gc) :=
          measure_union_le _ _
      _ = (chaosSampleLaw model).toMeasure Bad0 := by rw [measure_toMeasurable, hnull, add_zero]
      _ ≤ ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-1 * (1 / 8 : ℝ) * (N : ℝ))) := hB0p
      _ = _ := by ring_nf
  have hγ12 : min (min γ1 γ2) (1 / 8) ≤ min γ1 γ2 := min_le_left _ _
  have hγ18 : min (min γ1 γ2) (1 / 8) ≤ (1 / 8 : ℝ) := min_le_right _ _
  refine ⟨(Bad1 ∪ Bad2) ∪ (Bad0 ∪ toMeasurable (chaosSampleLaw model).toMeasure Gc),
    (hB1m.union hB2m).union (hB0m.union (measurableSet_toMeasurable _ _)), ?_, ?_⟩
  · have hU12 : (chaosSampleLaw model).toMeasure (Bad1 ∪ Bad2) ≤
        ENNReal.ofReal ((C1 + C2) * (3 : ℝ) ^ (-(min γ1 γ2) * (N : ℝ))) :=
      _root_.SubdiffusiveProcess.Paper.aux_lem_finite_stopping_partition_prob_union_le _ Bad1 Bad2 C1 C2 γ1 γ2 (min γ1 γ2)
        (C1 + C2) (N : ℝ) hC1.le hC2.le (min_le_left _ _) (min_le_right _ _) (Nat.cast_nonneg N)
        le_rfl hB1p hB2p
    exact _root_.SubdiffusiveProcess.Paper.aux_lem_finite_stopping_partition_prob_union_le _ (Bad1 ∪ Bad2)
      (Bad0 ∪ toMeasurable (chaosSampleLaw model).toMeasure Gc) (C1 + C2) Ctail (min γ1 γ2) (1 / 8)
      (min (min γ1 γ2) (1 / 8)) (C1 + C2 + Ctail) (N : ℝ) (by positivity) hCtail.le hγ12 hγ18
      (Nat.cast_nonneg N) le_rfl hU12 hB3p
  · intro omega hom reverse
    have hom1 : omega ∉ Bad1 := fun h => hom (Or.inl (Or.inl h))
    have hom2 : omega ∉ Bad2 := fun h => hom (Or.inl (Or.inr h))
    have hom0 : omega ∉ Bad0 := fun h => hom (Or.inr (Or.inl h))
    have homG : omega ∉ toMeasurable (chaosSampleLaw model).toMeasure Gc :=
      fun h => hom (Or.inr (Or.inr h))
    have hLip : ∀ x y, x ∈ (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) →
        y ∈ (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) →
        |H omega x - H omega y| ≤ G omega * dist x y := by
      by_contra hcon
      exact homG (subset_toMeasurable _ _ hcon)
    have hGN : |G omega| ≤ (3 : ℝ) ^ ((1 / 8 : ℝ) * (N : ℝ)) := (hB0 omega hom0 0).1
    have hGN' : G omega ≤ (3 : ℝ) ^ ((1 / 8 : ℝ) * (N : ℝ)) := (le_abs_self _).trans hGN
    refine ⟨hB1 omega hom1 reverse, ?_⟩
    have hwt : Real.exp (G omega * (3 : ℝ) ^ (-((N : ℝ) / 4))) ≤ 1 + rho := by
      have h1 : G omega * (3 : ℝ) ^ (-((N : ℝ) / 4)) ≤ (3 : ℝ) ^ (-((N : ℝ) / 8)) := by
        calc G omega * (3 : ℝ) ^ (-((N : ℝ) / 4))
            ≤ (3 : ℝ) ^ ((1 / 8 : ℝ) * (N : ℝ)) * (3 : ℝ) ^ (-((N : ℝ) / 4)) :=
              mul_le_mul_of_nonneg_right hGN' (Real.rpow_nonneg (by norm_num) _)
          _ = (3 : ℝ) ^ (-((N : ℝ) / 8)) := by
              rw [← Real.rpow_add (by norm_num)]
              congr 1
              ring
      have h2 : (3 : ℝ) ^ (-((N : ℝ) / 8)) ≤ Real.log (1 + rho) := by
        have h8 : (N03 : ℝ) ≤ (N : ℝ) / 8 := by
          have h := (Nat.cast_le (α := ℝ)).2 hN03'
          push_cast at h
          linarith
        have hpow : (3 : ℝ) ^ (N03 : ℕ) ≤ (3 : ℝ) ^ ((N : ℝ) / 8) := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h8
        have hlt : (Real.log (1 + rho))⁻¹ ≤ (3 : ℝ) ^ ((N : ℝ) / 8) := (hN03.trans_le hpow).le
        rw [Real.rpow_neg (by norm_num)]
        exact inv_le_of_inv_le₀ hlogpos hlt
      calc Real.exp (G omega * (3 : ℝ) ^ (-((N : ℝ) / 4)))
          ≤ Real.exp (Real.log (1 + rho)) := Real.exp_le_exp.mpr (h1.trans h2)
        _ = 1 + rho := Real.exp_log (by linarith)
    exact hB2 omega hom2 (G omega) (hG0 omega) (fun x hx y hy => hLip x y hx hy) (1 + rho) hwt reverse

end SubdiffusiveProcess.Paper
