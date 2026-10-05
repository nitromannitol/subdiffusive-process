module

public import SubdiffusiveProcess.Paper.lfsgs_good_steps_from_windows
public import SubdiffusiveProcess.Paper.lfsgs_hRegWitness_of_arbitrary_Rm
public import SubdiffusiveProcess.Paper.lfsgs_trace_witness

@[expose] public section

/-! This module selects the constants and supplies both window families for finite good steps. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.FiniteStopping
open scoped ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SubdiffusiveProcess.Paper

open Classical in
/-- Fix the geometric exponents and a witness rate exceeding branch entropy before choosing the model. -/
theorem lfsgs_good_steps_constants
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
    ∀ eta : ℝ, 0 < eta → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
    good_steps_on_root model H P H1 θbad Cg eta z j C γ N0 := by
  classical
  let instDimension : NeZero d := ⟨by omega⟩
  refine ⟨2, by norm_num, ?_⟩
  intro thetaBad hthetaBad
  refine ⟨max 4 2, ?_⟩
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
    exact (min_le_left _ _).trans (by linarith only [hd, hthetaBad, hH1min, hH1, hbeta, hba, halpha, halphaLower, hthetaPack])
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
      _ > 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / thetaPack := by linarith only [hd, hthetaBad, hH1min, hH1, hbeta, hba, halpha, halphaLower, hthetaPack, hthetaPack_le, hthetaPack_gap, hBpos, hbase]
  obtain ⟨Cfin, pad, deltaReg, sigmaReg, epsReg, hCfin, hpad, hpadle3,
      hdeltaReg, hsigmaReg, hepsReg, hRegSup⟩ :=
    _root_.SubdiffusiveProcess.Paper.lfsgs_hRegWitness_of_arbitrary_Rm d hd Jc Pc Xc Sf W Cp
      Step D Dbase alpha beta B hbeta hba halpha hBpos H1 hH1 ((le_max_left 4 2).trans hH1min)
  obtain ⟨deltaTrace, hdeltaTrace, hTraceSup⟩ :=
    _root_.SubdiffusiveProcess.Paper.lfsgs_trace_witness d hd Jc Pc Xc Sf W Cp Step D hES Dbase
      alpha halphaLower halpha B hBpos
  have hdeltaMain : 0 < min deltaReg deltaTrace := lt_min hdeltaReg hdeltaTrace
  refine ⟨Cfin ^ 2, min deltaReg deltaTrace, by positivity, hdeltaMain, ?_⟩
  intro model _Rm Sreg _It H hH hdelta
  have hdeltaRegModel : model.delta ≤ deltaReg := le_trans hdelta (min_le_left _ _)
  have hdeltaTraceModel : model.delta ≤ deltaTrace := le_trans hdelta (min_le_right _ _)
  have hRegWitness : ∀ (N k : ℕ) (zc : SpatialCoordinates d), k ≤ N →
      ∃ Wt : ℕ+ → Set (BilateralField d),
        (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
          ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).domRestrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
              C(SpatialCoordinates d, ℝ)))] (Wt h)) ∧
        (∀ h : ℕ+, (chaosSampleLaw model).toMeasure (Wt h) ≤
          ENNReal.ofReal (Real.exp (-B * (h : ℝ)))) ∧
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
          ¬Reg model H alpha H1 pad Cfin hpad N k zc omega →
            omega ∈ ⋃ h : ℕ+, Wt h) := by
    intro N k zc hkN
    exact hRegSup model _Rm Sreg _It H hH hdeltaRegModel N k zc hkN
  have hpadL : pad < (3 : ℝ) ^ H1 := by
    calc
      pad ≤ 3 := hpadle3
      _ < (3 : ℝ) ^ 2 := by norm_num
      _ ≤ (3 : ℝ) ^ H1 := pow_le_pow_right₀ (by norm_num) ((le_max_right 4 2).trans hH1min)
  exact lfsgs_good_steps_from_windows hd H1 hH1 thetaBad thetaPack alpha beta Cfin pad B
    hthetaPack hthetaPack_le hthetaPack_gap hbeta hba halpha hCfin hpad hpadle3 hpadL hB
    model H hH hRegWitness (hTraceSup model _Rm Sreg _It H hH hdeltaTraceModel)

end SubdiffusiveProcess.Paper
