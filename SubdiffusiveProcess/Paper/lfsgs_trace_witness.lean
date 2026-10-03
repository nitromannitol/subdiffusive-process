module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Lane3.Subdivision
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.Lane2.CellDirichlet
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Lane4.Inputs
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Main.LayerScaling
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.cell_catalogue
public import SubdiffusiveProcess.Paper.good_event
public import SubdiffusiveProcess.Paper.lem_finite_good_cell
public import SubdiffusiveProcess.Paper.finite_interval_packing
public import SubdiffusiveProcess.Paper.paper_responses_bank
public import SubdiffusiveProcess.Paper.finite_response_ramp
public import SubdiffusiveProcess.Paper.lem_rare_tests
public import SubdiffusiveProcess.Paper.lem_finite_trace_tests
public import SubdiffusiveProcess.Paper.lem_local_normalizations
public import SubdiffusiveProcess.Paper.inputs_EM_witness
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.rem_bank
public import SubdiffusiveProcess.Paper.prop_16
public import SubdiffusiveProcess.Paper.lfsgs_trace_moments
public import SubdiffusiveProcess.Paper.aux_test_prop16_rd_band
public import SubdiffusiveProcess.Paper.classical_cube_fractional_interpolation
public import SubdiffusiveProcess.Paper.classical_cube_fractional_compact_embedding
public import SubdiffusiveProcess.FiniteStopping.AffineBoundaryTest
public import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison
public import SubdiffusiveProcess.FiniteStopping.HolderInterpolation
public import SubdiffusiveProcess.FiniteStopping.TraceRescaling
public import SubdiffusiveProcess.FiniteStopping.WitnessUnion
public import SubdiffusiveProcess.Paper.lfsgs_hRegWitness_of_arbitrary_Rm
public import SubdiffusiveProcess.Paper.lfsgs_normalized_Aext_seminorm
public import SubdiffusiveProcess.Paper.lfsgs_response_bank
public import SubdiffusiveProcess.Paper.lfsgs_step3_hR
public import SubdiffusiveProcess.Paper.lfsgs_step5_ramp
public import SubdiffusiveProcess.Paper.lfsgs_step7_close
public import SubdiffusiveProcess.Paper.lfsgs_theta_band_measurable

@[expose] public section

/-! This module establishes trace witness for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

variable {d : ℕ}

/-- trace quotient zero of boundary const in the finite stopping construction. -/
theorem aux_lfsgs_trace_witness_trace_quotient_zero_of_boundary_const {d : ℕ} (beta : ℝ)
    (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) (c : ℝ)
    (hS : ∃ x, x ∈ S) (hxy : ∃ x ∈ S, ∃ y ∈ S, x ≠ y)
    (hconst : ∀ x ∈ S, f x = c) :
    quotientCBetaNorm beta S f = 0 := by
  have hval : {v : ℝ | ∃ x ∈ S, v = |f x - c|} = {0} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [hconst x hx, sub_self, abs_zero]
    · intro hv
      have hv0 : v = 0 := by simpa only using hv
      subst v
      obtain ⟨x, hx⟩ := hS
      exact ⟨x, hx, by simp only [hconst x hx, sub_self, abs_zero]⟩
  have hratio : Lane4.holderRatioSet beta S (fun x => f x - c) = {0} := by
    ext v
    simp only [Lane4.holderRatioSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, y, hy, hneq, rfl⟩
      simp only [hconst x hx, sub_self, hconst y hy, abs_zero, zero_div]
    · intro hv
      have hv0 : v = 0 := by simpa only using hv
      subst v
      obtain ⟨x, hx, y, hy, hneq⟩ := hxy
      exact ⟨x, hx, y, hy, hneq, by simp only [hconst x hx, sub_self, hconst y hy, abs_zero, zero_div]⟩
  have hcA : Lane4.cAlphaNorm beta S (fun x => f x - c) = 0 := by
    unfold Lane4.cAlphaNorm Lane4.holderSeminorm
    rw [hval, hratio]
    simp only [csSup_singleton, add_zero]
  have hbelow : BddBelow {v : ℝ | ∃ c' : ℝ, v = Lane4.cAlphaNorm beta S
      (fun x => f x - c')} := by
    refine ⟨0, ?_⟩
    rintro v ⟨c', rfl⟩
    exact aux_lem_finite_trace_holder_beta_bound_cAlphaNorm_nonneg beta S
      (fun x => f x - c')
  have hu : quotientCBetaNorm beta S (fun x => f x) ≤ 0 := by
    unfold quotientCBetaNorm
    exact csInf_le hbelow ⟨c, hcA.symm⟩
  have hnonneg := aux_lem_finite_trace_tests_quotient_nonneg beta S f
  exact le_antisymm hu hnonneg

/-- trace witness in the finite stopping construction. -/
theorem lfsgs_trace_witness
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Step : @cutoff_good_scale_input d ⟨by omega⟩)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (Dbase : @sum_errors_baseline_input d ⟨by omega⟩ _ _)
    (alpha : ℝ) (halpha_lower : 1 / 2 < alpha) (halpha_upper : alpha < 1)
    (Bc : ℝ) (hBc : 0 < Bc) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Rm : in_responses d model) (Sreg : in_6_16 d model) (It : in_iteration d model Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (hH : InfraredCharacterization model H),
      model.delta ≤ delta0 →
      ∀ eta : ℝ, 0 < eta →
    let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
    ∃ m0 : ℕ,
    ∃ TraceClose : ℕ → ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop,
      (∀ N M k z omega, TraceClose N M k z omega ↔
        SubdiffusiveProcess.FiniteStopping.trace_close model H alpha eta N M k z omega) ∧
      (∀ (N M k : ℕ) (z : SpatialCoordinates d),
        k ≤ N → k ≤ M → m0 ≤ N - k → m0 ≤ M - k →
        ∃ Wtn : ℕ+ → Set (BilateralField d),
        (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
          ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).restrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
              C(SpatialCoordinates d, ℝ)))] (Wtn h)) ∧
        (∀ h : ℕ+, P (Wtn h) ≤ ENNReal.ofReal (Real.exp (-Bc * (h : ℝ)))) ∧
        (∀ᵐ omega ∂P, ¬TraceClose N M k z omega → omega ∈ ⋃ h : ℕ+, Wtn h)) := by
  classical
  haveI instNeZeroDimension : NeZero d := ⟨by omega⟩
  have hbeta : (1 : ℝ) / 2 < (1 / 2 + alpha) / 2 := by linarith only [hd, halpha_lower, halpha_upper, hBc]
  have hba : (1 / 2 + alpha) / 2 < alpha := by linarith only [hd, halpha_lower, halpha_upper, hBc, hbeta]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  let Breg : ℝ := Bc + 2 * Real.log 2 + 1
  have hBreg : 0 < Breg := by dsimp [Breg]; linarith only [hd, halpha_lower, halpha_upper, hBc, hbeta, hba, hlog2]

  obtain ⟨Cresp, hCresp, hRmAll⟩ := Paper.lfsgs_response_bank hd
  obtain ⟨sigma, eps, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _,
      hsigma, heps, _, _, _, _, _, _, _, _, _, _, _,
      delta0, _, Aext, _,
      hdelta0, _, hAext,
      _,
      _, _, _, hinner⟩ :=
    lem_finite_good_cell d hd Jc Pc Xc Sf W Cp Step D Dbase Cresp hCresp
      alpha ((1 / 2 + alpha) / 2) Breg hbeta hba halpha_upper hBreg 1 Nat.one_pos
  have haD : 0 < aux_prop16_aD d := by
    unfold aux_prop16_aD
    have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have ht : 0 < (d : ℝ) - 1 / 2 := by linarith only [hd, halpha_lower, halpha_upper, hBc, hbeta, hba, hlog2, hBreg, hCresp, hdelta0, hAext, hdreal]
    have ht2 : 0 < (d : ℝ) - 1 / 2 - (d : ℝ) + 1 := by ring_nf; norm_num
    have hden : 0 < (d : ℝ) - 1 / 2 + 1 := by linarith only [hd, halpha_lower, halpha_upper, hBc, hbeta, hba, hlog2, hBreg, hCresp, hdelta0, hAext, hdreal, ht, ht2]
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    change 0 < ((d : ℝ) - 1 / 2) * (((d : ℝ) - 1 / 2) - (d : ℝ) + 1) /
      (((d : ℝ) - 1 / 2) + 1) / (8 * Real.log 3)
    positivity
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let pMoment : ℝ := 2 + Paper.aux_lfsgs_step5_ramp_Cgeom * Breg /
    (aux_prop16_aD d * Real.log 3)
  have hpMoment : 2 ≤ pMoment := by
    dsimp [pMoment]
    have hCgeom : 0 < Paper.aux_lfsgs_step5_ramp_Cgeom := lt_of_lt_of_le (by norm_num) Paper.aux_lfsgs_step5_ramp_Cgeom_ge4
    have hden : 0 < aux_prop16_aD d * Real.log 3 := mul_pos haD hlog3
    have hnum : 0 ≤ Paper.aux_lfsgs_step5_ramp_Cgeom * Breg :=
      mul_nonneg (le_of_lt hCgeom) (le_of_lt hBreg)
    have hfrac : 0 ≤ Paper.aux_lfsgs_step5_ramp_Cgeom * Breg / (aux_prop16_aD d * Real.log 3) :=
      div_nonneg hnum hden.le
    linarith only [hd, halpha_lower, halpha_upper, hBc, hbeta, hba, hlog2, hBreg, hCresp, hdelta0, hAext, haD, hlog3, hCgeom, hden, hnum, hfrac]
  have hpMargin : Paper.aux_lfsgs_step5_ramp_Cgeom * Breg < aux_prop16_aD d * pMoment * Real.log 3 := by
    have hden : aux_prop16_aD d * Real.log 3 ≠ 0 := (mul_pos haD hlog3).ne'
    have heq : aux_prop16_aD d * pMoment * Real.log 3 =
        2 * (aux_prop16_aD d * Real.log 3) + Paper.aux_lfsgs_step5_ramp_Cgeom * Breg := by
      dsimp [pMoment]
      field_simp
    rw [heq]
    have : 0 < 2 * (aux_prop16_aD d * Real.log 3) := by positivity
    linarith only [hd, halpha_lower, halpha_upper, hBc, hbeta, hba, hlog2, hBreg, hCresp, hdelta0, hAext, haD, hlog3, hpMoment, heq, this]
  obtain ⟨qMoment, deltaTrace, aMoment, hpqMoment, hdeltaTrace, haMoment,
      hAMomentEq, hStep4⟩ :=
    Paper.aux_lfsgs_theta_band_measurable_step4_bank hd Jc Pc Xc W Sf Cp D hES Step Dbase pMoment hpMoment
  refine ⟨min delta0 deltaTrace, lt_min hdelta0 hdeltaTrace, ?_⟩
  intro model Rm Sreg It H hH hdeltamin eta hetapos

  obtain ⟨RmBank, hRmBankC⟩ := hRmAll model
  obtain ⟨eta0, F0, Praw0, Rraw0, Draw0, Z0, rawGood0, hEta0, hprim0⟩ :=
    Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_primitive_scores_exists model sigma eps hsigma heps
  have hdeltaCell : model.delta ≤ delta0 := le_trans hdeltamin (min_le_left _ _)
  have hdeltaStep4 : model.delta ≤ deltaTrace := le_trans hdeltamin (min_le_right _ _)
  obtain ⟨Good, Carrier, hCarrierMeas, hCarrierNull, hGoodIff, hGoodMeasW, hClause⟩ :=
    hinner model RmBank (le_of_eq hRmBankC) Sreg It H hH hdeltaCell eta0 hEta0
      F0 Praw0 Rraw0 Draw0 Z0 rawGood0 hprim0
  obtain ⟨Hs, hHsSmooth, hHsMain⟩ :=
    lem_finite_trace_tests d hd ((1 / 2 + alpha) / 2) alpha hbeta hba halpha_upper
      Aext eta hAext.le hetapos
  obtain ⟨phiAffine, hphiAffine, xAffine, hxAffine, yAffine, hyAffine, hneAffine⟩ :=
    SubdiffusiveProcess.FiniteStopping.trace_affine_test hd
  let S : Set (SpatialCoordinates d) :=
    frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
  let nonconst : (SpatialCoordinates d → ℝ) → Prop := fun h =>
    ∃ x ∈ S, ∃ y ∈ S, h x ≠ h y
  let testCarrier : Finset (SpatialCoordinates d → ℝ) := Hs.filter nonconst
  let T := Option {h : SpatialCoordinates d → ℝ // h ∈ testCarrier}
  let testOf : T → SpatialCoordinates d → ℝ := fun t =>
    match t with
    | none => phiAffine
    | some hh => hh.1
  letI instFiniteTests : Fintype T := by
    dsimp [T]
    infer_instance
  letI instNonemptyTests : Nonempty T := ⟨none⟩
  have htestSmooth : ∀ t : T, ContDiff ℝ ∞ (testOf t) := by
    intro t
    cases t with
    | none => exact hphiAffine
    | some hh => exact hHsSmooth hh.1 (Finset.mem_filter.mp hh.2).1
  have htestNonconst : ∀ t : T,
      ∃ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
        testOf t x ≠ testOf t y := by
    intro t
    cases t with
    | none => exact ⟨xAffine, hxAffine, yAffine, hyAffine, hneAffine⟩
    | some hh => exact (Finset.mem_filter.mp hh.2).2
  have hPunit : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) w‖ :=
    aux_lem_local_normalizations_unit_poincare hd
  let bOf : T → weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos) :=
    fun t => Classical.choose (aux_lem_local_normalizations_smooth_representative
      (0 : SpatialCoordinates d) 1 one_pos (testOf t) (htestSmooth t))
  have hbOf : ∀ t : T,
      ((bOf t : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))]
        testOf t := by
    intro t
    exact Classical.choose_spec (aux_lem_local_normalizations_smooth_representative
      (0 : SpatialCoordinates d) 1 one_pos (testOf t) (htestSmooth t))
  obtain ⟨Cmom, Cband, hCmom, hCband, R0, hR0, Rlim0, hBank⟩ :=
    hStep4 model Rm Sreg It H hH hdeltaStep4 T testOf htestSmooth htestNonconst
      hPunit bOf hbOf
  let TraceClose := SubdiffusiveProcess.FiniteStopping.trace_close model H alpha eta
  have hBankEq := hBank
  rw [hR0] at hBankEq
  obtain ⟨hR0meas, hRlim0meas, hR0mem, hR0mom, hR0conv, hR0band⟩ := hBankEq
  rw [hAMomentEq] at hR0band
  let R0 : T → ℕ → BilateralField d → ℝ := fun t m tau =>
    dirichletResponse (killedResponseSpace hPunit)
      (cutoffPositiveCoefficient model H tau m (0 : SpatialCoordinates d) one_pos) (bOf t)
  have hetaRamp : 0 < eta / 4 := by positivity
  obtain ⟨H0, m0, hH0pos, hRamp⟩ :=
    Paper.lfsgs_step5_ramp hd model T pMoment qMoment (aux_prop16_aD d) Cmom Cband
      (by linarith only [hd, halpha_lower, halpha_upper, hBc, hbeta, hba, hlog2, hBreg, hCresp, hdelta0, hAext, haD, hlog3, hpMoment, hpMargin, hpqMoment, hdeltaTrace, haMoment, hAMomentEq, hdeltamin, hetapos, hRmBankC, hdeltaCell, hdeltaStep4, hCarrierNull, hCmom, hCband, hR0, hBank, hetaRamp, hpMoment]) hpqMoment haD hCmom hCband R0 Rlim0
      hR0meas hRlim0meas hR0mem hR0mom hR0conv hR0band
      (eta / 4) hetaRamp Breg hBreg hpMargin
  have hrateDown : ∀ h : ℕ+,
      Real.exp (-(Breg * (h : ℝ))) ≤
        Real.exp (-(Bc + 2 * Real.log 2) * (h : ℝ)) := by
    intro h
    apply Real.exp_le_exp.mpr
    have hh : 0 ≤ (h : ℝ) := by positivity
    dsimp [Breg]
    nlinarith only [hd, halpha_lower, halpha_upper, hBc, hbeta, hba, hlog2, hBreg, hCresp, hdelta0, hAext, haD, hlog3, hpMoment, hpMargin, hpqMoment, hdeltaTrace, haMoment, hAMomentEq, hdeltamin, hetapos, hRmBankC, hdeltaCell, hdeltaStep4, hCarrierNull, hCmom, hCband, hR0, hBank, hetaRamp, hH0pos, hh, mul_nonneg hh (have this := Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero) (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl true); this)]
  have hrateDownReg : ∀ h : ℕ+,
      Real.exp (-Breg * (h : ℝ)) ≤
        Real.exp (-(Bc + 2 * Real.log 2) * (h : ℝ)) := by
    intro h
    have hh := hrateDown h
    convert hh using 1 <;> congr 1 <;> ring
  have hrateFormat : ∀ h : ℕ+,
      Real.exp (-(Bc + 2 * Real.log 2) * (h : ℝ)) =
        Real.exp (-(Bc + Real.log 2 + Real.log 2) * (h : ℝ)) := by
    intro h
    congr 1
    ring
  have hTW : ∀ (N M k : ℕ) (z : SpatialCoordinates d),
      k ≤ N → k ≤ M → m0 ≤ N - k → m0 ≤ M - k →
      ∃ Wtn : ℕ+ → Set (BilateralField d),
      (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
        ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).restrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
            C(SpatialCoordinates d, ℝ)))] (Wtn h)) ∧
      (∀ h : ℕ+, (chaosSampleLaw model).toMeasure (Wtn h) ≤
        ENNReal.ofReal (Real.exp (-Bc * (h : ℝ)))) ∧
      (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
        ¬ TraceClose N M k z omega → omega ∈ ⋃ h : ℕ+, Wtn h) := by
    intro N M k z hkN hkM hmN hmM
    obtain ⟨_, WNreg, hWNregMeas, hWNregProb, hWNregCover⟩ :=
      hGoodMeasW (N - k) k z
    obtain ⟨_, WMreg, hWMregMeas, hWMregProb, hWMregCover⟩ :=
      hGoodMeasW (M - k) k z
    obtain ⟨WNtest, hWNtestMeas, hWNtestProb, _, hWNtestCover⟩ :=
      hRamp k z (N - k) hmN
    obtain ⟨WMtest, hWMtestMeas, hWMtestProb, _, hWMtestCover⟩ :=
      hRamp k z (M - k) hmM
    have hprobNreg : ∀ h : ℕ+,
        (chaosSampleLaw model).toMeasure (WNreg h) ≤
          ENNReal.ofReal (Real.exp (-(Bc + 2 * Real.log 2) * (h : ℝ))) := by
      intro h
      exact (hWNregProb h).trans (ENNReal.ofReal_le_ofReal (hrateDownReg h))
    have hprobMreg : ∀ h : ℕ+,
        (chaosSampleLaw model).toMeasure (WMreg h) ≤
          ENNReal.ofReal (Real.exp (-(Bc + 2 * Real.log 2) * (h : ℝ))) := by
      intro h
      exact (hWMregProb h).trans (ENNReal.ofReal_le_ofReal (hrateDownReg h))
    have hprobNtest : ∀ h : ℕ+,
        (chaosSampleLaw model).toMeasure (WNtest h) ≤
          ENNReal.ofReal (Real.exp (-(Bc + 2 * Real.log 2) * (h : ℝ))) := by
      intro h
      exact (hWNtestProb h).trans (ENNReal.ofReal_le_ofReal (hrateDown h))
    have hprobMtest : ∀ h : ℕ+,
        (chaosSampleLaw model).toMeasure (WMtest h) ≤
          ENNReal.ofReal (Real.exp (-(Bc + 2 * Real.log 2) * (h : ℝ))) := by
      intro h
      exact (hWMtestProb h).trans (ENNReal.ofReal_le_ofReal (hrateDown h))
    have hprobNreg' : ∀ h : ℕ+,
        (chaosSampleLaw model).toMeasure (WNreg h) ≤
          ENNReal.ofReal (Real.exp (-(Bc + Real.log 2 + Real.log 2) * (h : ℝ))) := by
      intro h
      calc
        (chaosSampleLaw model).toMeasure (WNreg h) ≤
            ENNReal.ofReal (Real.exp (-(Bc + 2 * Real.log 2) * (h : ℝ))) := hprobNreg h
        _ = ENNReal.ofReal (Real.exp (-(Bc + Real.log 2 + Real.log 2) * (h : ℝ))) := by
            rw [hrateFormat h]
    have hprobMreg' : ∀ h : ℕ+,
        (chaosSampleLaw model).toMeasure (WMreg h) ≤
          ENNReal.ofReal (Real.exp (-(Bc + Real.log 2 + Real.log 2) * (h : ℝ))) := by
      intro h
      calc
        (chaosSampleLaw model).toMeasure (WMreg h) ≤
            ENNReal.ofReal (Real.exp (-(Bc + 2 * Real.log 2) * (h : ℝ))) := hprobMreg h
        _ = ENNReal.ofReal (Real.exp (-(Bc + Real.log 2 + Real.log 2) * (h : ℝ))) := by
            rw [hrateFormat h]
    have hprobNtest' : ∀ h : ℕ+,
        (chaosSampleLaw model).toMeasure (WNtest h) ≤
          ENNReal.ofReal (Real.exp (-(Bc + Real.log 2 + Real.log 2) * (h : ℝ))) := by
      intro h
      calc
        (chaosSampleLaw model).toMeasure (WNtest h) ≤
            ENNReal.ofReal (Real.exp (-(Bc + 2 * Real.log 2) * (h : ℝ))) := hprobNtest h
        _ = ENNReal.ofReal (Real.exp (-(Bc + Real.log 2 + Real.log 2) * (h : ℝ))) := by
            rw [hrateFormat h]
    have hprobMtest' : ∀ h : ℕ+,
        (chaosSampleLaw model).toMeasure (WMtest h) ≤
          ENNReal.ofReal (Real.exp (-(Bc + Real.log 2 + Real.log 2) * (h : ℝ))) := by
      intro h
      calc
        (chaosSampleLaw model).toMeasure (WMtest h) ≤
            ENNReal.ofReal (Real.exp (-(Bc + 2 * Real.log 2) * (h : ℝ))) := hprobMtest h
        _ = ENNReal.ofReal (Real.exp (-(Bc + Real.log 2 + Real.log 2) * (h : ℝ))) := by
            rw [hrateFormat h]
    obtain ⟨Wtn, hWtnMeas, hWtnProb, hWtnUnion⟩ :=
      SubdiffusiveProcess.FiniteStopping.step6_union (chaosSampleLaw model).toMeasure (k : ℤ) Bc hBc
        WNreg WMreg WNtest WMtest hWNregMeas hWMregMeas hWNtestMeas hWMtestMeas
        hprobNreg' hprobMreg' hprobNtest' hprobMtest'
    refine ⟨Wtn, hWtnMeas, hWtnProb, ?_⟩
    have hCarrier : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, omega ∈ Carrier := by
      rw [ae_iff]
      simpa only using! hCarrierNull
    have hscaleAE := aux_lem_local_normalizations_finite_scaling model H hH k z
      (by positivity : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)))
    filter_upwards [hCarrier, hWNtestCover, hWMtestCover, hscaleAE]
      with omega hcar hrampN hrampM hscale
    intro hnotTrace
    by_contra hnotW
    rw [hWtnUnion] at hnotW
    have hnotWNreg : omega ∉ ⋃ h : ℕ+, WNreg h := by
      intro hm
      exact hnotW (Or.inl (Or.inl hm))
    have hnotWMreg : omega ∉ ⋃ h : ℕ+, WMreg h := by
      intro hm
      exact hnotW (Or.inl (Or.inr hm))
    have hnotWNtest : omega ∉ ⋃ h : ℕ+, WNtest h := by
      intro hm
      exact hnotW (Or.inr (Or.inl hm))
    have hnotWMtest : omega ∉ ⋃ h : ℕ+, WMtest h := by
      intro hm
      exact hnotW (Or.inr (Or.inr hm))
    have hRampN : ∀ t : T,
        |R0 t (N - k) (aux_lem_local_normalizations_Theta k z omega) -
          Rlim0 t (aux_lem_local_normalizations_Theta k z omega)| ≤ eta / 4 :=
      hrampN hnotWNtest
    have hRampM : ∀ t : T,
        |R0 t (M - k) (aux_lem_local_normalizations_Theta k z omega) -
          Rlim0 t (aux_lem_local_normalizations_Theta k z omega)| ≤ eta / 4 :=
      hrampM hnotWMtest
    have hGoodN : omega ∈ Good (N - k) k z := by
      by_contra hbad
      exact hnotWNreg (hWNregCover hbad)
    have hGoodM : omega ∈ Good (M - k) k z := by
      by_contra hbad
      exact hnotWMreg (hWMregCover hbad)
    have hClauseN := (hClause omega hcar (N - k) k z hGoodN true).2
    have hClauseM := (hClause omega hcar (M - k) k z hGoodM true).2
    have hmkN : N - k + k = N := Nat.sub_add_cancel hkN
    have hmkM : M - k + k = M := Nat.sub_add_cancel hkM
    simp only [hmkN, if_true] at hClauseN
    simp only [hmkM, if_true] at hClauseM
    let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
    have hr : 0 < r := by dsimp [r]; positivity
    let kappa : ℕ → ℝ := fun J => aux_lem_local_normalizations_kap model J
    let sN : ℝ := (kappa (N - k) / kappa N) *
      Real.exp ((H omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)
    let sM : ℝ := (kappa (M - k) / kappa M) *
      Real.exp ((H omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)
    let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
    let aN : PositiveCoefficient Q := cutoffPositiveCoefficient model H omega N z hr
    let aM : PositiveCoefficient Q := cutoffPositiveCoefficient model H omega M z hr
    let thetaOmega := aux_lem_local_normalizations_Theta k z omega
    have hRampN' : ∀ t : T,
        |R0 t (N - k) thetaOmega - Rlim0 t thetaOmega| ≤ eta / 4 := by
      simpa only using hRampN
    have hRampM' : ∀ t : T,
        |R0 t (M - k) thetaOmega - Rlim0 t thetaOmega| ≤ eta / 4 := by
      simpa only using hRampM
    let aUN : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos) :=
      cutoffPositiveCoefficient model H thetaOmega (N - k) 0 one_pos
    let aUM : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos) :=
      cutoffPositiveCoefficient model H thetaOmega (M - k) 0 one_pos
    have hsN : 0 < sN := by
      dsimp [sN, kappa]
      exact mul_pos (div_pos (aux_lem_local_normalizations_kap_pos model (N - k))
        (aux_lem_local_normalizations_kap_pos model N)) (Real.exp_pos _)
    have hsM : 0 < sM := by
      dsimp [sM, kappa]
      exact mul_pos (div_pos (aux_lem_local_normalizations_kap_pos model (M - k))
        (aux_lem_local_normalizations_kap_pos model M)) (Real.exp_pos _)
    have hGc : aux_lem_local_normalizations_Gc H k omega z =
        (H omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z := by
      simp only [aux_lem_local_normalizations_Gc, ContinuousMap.add_apply, ContinuousMap.coe_sum, Finset.sum_apply]
    have hscaleN : ∀ g : SpatialCoordinates d → ℝ,
        sInf (aux_lem_local_normalizations_Lset z r hr aN g) =
          r ^ ((d : ℝ) - 2) * sN *
            sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUN
              (g ∘ cubeDilation z 0 r)) := by
      intro g
      have hl := hscale N hkN g
      rw [hGc] at hl
      calc
        sInf (aux_lem_local_normalizations_Lset z r hr aN g) =
            (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) *
              (aux_lem_local_normalizations_kap model (N - k) /
                aux_lem_local_normalizations_kap model N) *
              Real.exp ((H omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z) *
              sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUN
                (g ∘ aux_lem_local_normalizations_T k z)) := hl
        _ = r ^ ((d : ℝ) - 2) * sN *
              sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUN
                (g ∘ cubeDilation z 0 r)) := by
              dsimp [r, sN, kappa, thetaOmega, aux_lem_local_normalizations_T]
              rw [← aux_lem_local_normalizations_rscale_rpow d k]
              congr 1
              ring
    have hscaleM : ∀ g : SpatialCoordinates d → ℝ,
        sInf (aux_lem_local_normalizations_Lset z r hr aM g) =
          r ^ ((d : ℝ) - 2) * sM *
            sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUM
              (g ∘ cubeDilation z 0 r)) := by
      intro g
      have hl := hscale M hkM g
      rw [hGc] at hl
      calc
        sInf (aux_lem_local_normalizations_Lset z r hr aM g) =
            (3 : ℝ) ^ (-((d : ℝ) - 2) * (k : ℝ)) *
              (aux_lem_local_normalizations_kap model (M - k) /
                aux_lem_local_normalizations_kap model M) *
              Real.exp ((H omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z) *
              sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUM
                (g ∘ aux_lem_local_normalizations_T k z)) := hl
        _ = r ^ ((d : ℝ) - 2) * sM *
              sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUM
                (g ∘ cubeDilation z 0 r)) := by
              dsimp [r, sM, kappa, thetaOmega, aux_lem_local_normalizations_T]
              rw [← aux_lem_local_normalizations_rscale_rpow d k]
              congr 1
              ring
    have hClauseAextN : ∀ (hP' : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
        ‖(w : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) w‖),
        ∀ (b : weakSobolevGraph Q) (G : SpatialCoordinates d → ℝ),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn ((1 / 2 + alpha) / 2)
          (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        ∀ c : ℝ, dirichletResponse (killedResponseSpace hP') aN b ≤
          Aext * r ^ ((d : ℝ) - 2) * sN *
            (cAlphaNorm ((1 / 2 + alpha) / 2)
              (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
                Set (SpatialCoordinates d))) (fun x => G (z + r • x) - c)) ^ 2 := by
      exact hClauseN
    have hClauseAextM : ∀ (hP' : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Q,
        ‖(w : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) w‖),
        ∀ (b : weakSobolevGraph Q) (G : SpatialCoordinates d → ℝ),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn ((1 / 2 + alpha) / 2)
          (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        ∀ c : ℝ, dirichletResponse (killedResponseSpace hP') aM b ≤
          Aext * r ^ ((d : ℝ) - 2) * sM *
            (cAlphaNorm ((1 / 2 + alpha) / 2)
              (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
                Set (SpatialCoordinates d))) (fun x => G (z + r • x) - c)) ^ 2 := by
      exact hClauseM
    have htestFrom
        (qN qM : Seminorm ℝ (SpatialCoordinates d → ℝ))
        (hqN1 : ∀ g : SpatialCoordinates d → ℝ,
          IsCellBoundaryClass ((1 / 2 + alpha) / 2) 0 1 g →
            (qN g) ^ 2 = sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUN g))
        (hqM1 : ∀ g : SpatialCoordinates d → ℝ,
          IsCellBoundaryClass ((1 / 2 + alpha) / 2) 0 1 g →
            (qM g) ^ 2 = sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUM g))
        (hR : ∀ g : SpatialCoordinates d → ℝ,
          IsCellBoundaryClass ((1 / 2 + alpha) / 2) 0 1 g →
            (qN g) ^ 2 ≤ Aext * (cellBoundaryQuotientNorm ((1 / 2 + alpha) / 2) 0 1 g) ^ 2 ∧
            (qM g) ^ 2 ≤ Aext * (cellBoundaryQuotientNorm ((1 / 2 + alpha) / 2) 0 1 g) ^ 2) :
        ∀ h ∈ Hs, |(qN h) ^ 2 - (qM h) ^ 2| ≤ eta / 2 := by
      intro h hh
      let S : Set (SpatialCoordinates d) :=
        frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      have hclass : IsCellBoundaryClass ((1 / 2 + alpha) / 2) 0 1 h :=
        aux_lem_local_normalizations_smooth_class ((1 / 2 + alpha) / 2)
          (by linarith only [hd, halpha_lower, halpha_upper, hBc, hbeta, hba, hlog2, hBreg, hCresp, hdelta0, hAext, haD, hlog3, hpMoment, hpMargin, hpqMoment, hdeltaTrace, haMoment, hAMomentEq, hdeltamin, hetapos, hRmBankC, hdeltaCell, hdeltaStep4, hCarrierNull, hCmom, hCband, hR0, hBank, hetaRamp, hH0pos, hkN, hkM, hmN, hmM, hWtnUnion, hnotTrace, hnotW, hnotWNreg, hnotWMreg, hnotWNtest, hnotWMtest, hmkN, hmkM, hr, hsN, hsM, hGc, halpha_upper]) 0 1 h (hHsSmooth h hh)
      by_cases hnonconst : ∃ x ∈ S, ∃ y ∈ S, h x ≠ h y
      · have hmem : h ∈ testCarrier := Finset.mem_filter.mpr ⟨hh, hnonconst⟩
        let t : T := some ⟨h, hmem⟩
        have htestOf : testOf t = h := by rfl
        have hdir : ∀ L : ℕ,
            dirichletResponse (killedResponseSpace hPunit)
              (cutoffPositiveCoefficient model H (thetaOmega) L 0 one_pos) (bOf t) =
            sInf (aux_lem_local_normalizations_Lset 0 1 one_pos
              (cutoffPositiveCoefficient model H thetaOmega L 0 one_pos) h) := by
          intro L
          have hres := Paper.aux_lfsgs_normalized_Aext_seminorm_dirichletResponse_eq_sInf hd
            (0 : SpatialCoordinates d) 1 one_pos hPunit
            (cutoffPositiveCoefficient model H thetaOmega L 0 one_pos)
            (bOf t) (testOf t) (testOf t)
            (htestSmooth t).continuous.continuousOn (hbOf t) (fun _ _ => rfl)
          simpa only [htestOf] using hres
        have hqNresp : (qN h) ^ 2 = R0 t (N - k) thetaOmega := by
          calc
            (qN h) ^ 2 = sInf (aux_lem_local_normalizations_Lset 0 1 one_pos
                (cutoffPositiveCoefficient model H thetaOmega (N - k) 0 one_pos) h) :=
              hqN1 h hclass
            _ = dirichletResponse (killedResponseSpace hPunit)
                (cutoffPositiveCoefficient model H thetaOmega (N - k) 0 one_pos) (bOf t) :=
              (hdir (N - k)).symm
            _ = R0 t (N - k) thetaOmega := rfl
        have hqMresp : (qM h) ^ 2 = R0 t (M - k) thetaOmega := by
          calc
            (qM h) ^ 2 = sInf (aux_lem_local_normalizations_Lset 0 1 one_pos
                (cutoffPositiveCoefficient model H thetaOmega (M - k) 0 one_pos) h) :=
              hqM1 h hclass
            _ = dirichletResponse (killedResponseSpace hPunit)
                (cutoffPositiveCoefficient model H thetaOmega (M - k) 0 one_pos) (bOf t) :=
              (hdir (M - k)).symm
            _ = R0 t (M - k) thetaOmega := rfl
        have hdevN := hRampN' t
        have hdevM := hRampM' t
        change |R0 t (N - k) thetaOmega - Rlim0 t thetaOmega| ≤ eta / 4 at hdevN
        change |R0 t (M - k) thetaOmega - Rlim0 t thetaOmega| ≤ eta / 4 at hdevM
        rw [hqNresp, hqMresp]
        exact SubdiffusiveProcess.FiniteStopping.responses_two_sided_eta4 hdevN hdevM
      · have hconst : ∀ x ∈ S, h x = h xAffine := by
          intro x hx
          by_contra hne
          exact hnonconst ⟨x, hx, xAffine, hxAffine, hne⟩
        have hxyAffine : xAffine ≠ yAffine := by
          intro heq
          apply hneAffine
          rw [heq]
        have hzero : cellBoundaryQuotientNorm ((1 / 2 + alpha) / 2) 0 1 h = 0 := by
          unfold cellBoundaryQuotientNorm
          rw [SubdiffusiveProcess.FiniteStopping.rescaledDatum_unit]
          exact Paper.aux_lfsgs_trace_witness_trace_quotient_zero_of_boundary_const ((1 / 2 + alpha) / 2)
            S h (h xAffine) ⟨xAffine, hxAffine⟩ ⟨xAffine, hxAffine, yAffine, hyAffine, hxyAffine⟩ hconst
        have hqNzero := (hR h hclass).1
        have hqMzero := (hR h hclass).2
        rw [hzero] at hqNzero hqMzero
        norm_num at hqNzero hqMzero
        rw [hqNzero, hqMzero]
        simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_self, abs_zero, ge_iff_le] using (le_of_lt (half_pos hetapos))
    have hclose : TraceClose N M k z omega := by
      dsimp [TraceClose]
      intro hP u G hGc hGclass hGrep
      have hGbeta : IsHolderOn ((1 / 2 + alpha) / 2)
          (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G := by
        have hunit := SubdiffusiveProcess.FiniteStopping.isHolderOn_beta_of_alpha (le_of_lt hba)
          (rescaledDatum z r G) hGclass.1
        have hlift := Paper.aux_lfsgs_normalized_Aext_seminorm_isHolderOn_dilation_transfer ((1 / 2 + alpha) / 2)
          z r hr (rescaledDatum z r G) hunit
        have hident : (rescaledDatum z r G) ∘ cubeDilation 0 z r⁻¹ = G := by
          funext x
          rw [Function.comp_apply]
          change G (fun i => z i + r * (cubeDilation 0 z r⁻¹ x) i) = G x
          have hdil : (fun i => z i + r * (cubeDilation 0 z r⁻¹ x) i) =
              cubeDilation z 0 r (cubeDilation 0 z r⁻¹ x) := by
            funext i
            simp only [cubeDilation, Pi.zero_apply, zero_add, sub_zero]
          rw [hdil, aux_lem_local_normalizations_dil_inv z hr]
        rw [hident] at hlift
        exact hlift
      obtain ⟨qN, qM, hqN1, hqM1, hR⟩ :=
        Paper.lfsgs_step3_hR hd Sf z r hr aN aM aUN aUM sN sM Aext hsN hsM hAext
          ((1 / 2 + alpha) / 2) ⟨hbeta, lt_trans hba halpha_upper⟩
          hscaleN hscaleM hP hP (hClauseAextN hP) (hClauseAextM hP)
      have htest := htestFrom qN qM hqN1 hqM1 hR
      exact (Paper.lfsgs_step7_close hd alpha ((1 / 2 + alpha) / 2)
        hbeta hba halpha_upper Aext eta hAext.le hetapos
        z r hr sN sM hsN hsM aN aM aUN aUM hP hP qN qM
        hscaleN hscaleM hqN1 hqM1 hR Hs hHsMain htest) u G hGc hGclass hGrep
    exact hnotTrace hclose
  exact ⟨m0, TraceClose, (fun N M k z omega => Iff.rfl), hTW⟩

end Paper
