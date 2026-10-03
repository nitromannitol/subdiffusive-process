module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane3.Forms
public import SubdiffusiveProcess.Lane3.Subdivision
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Lane4.Carriers
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.cell_catalogue
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_deterministic
public import SubdiffusiveProcess.Paper.affine_cell_assembly
public import SubdiffusiveProcess.Paper.goodext_catalog_grid_coefficient_bound
public import SubdiffusiveProcess.Paper.goodext_reference_inverse_from_cell_cap
public import SubdiffusiveProcess.Analysis.RatioLimitInMeasure
public import SubdiffusiveProcess.Paper.lem_affine_gap_stmt
public import SubdiffusiveProcess.Paper.lem_affine_stmt_cge
public import SubdiffusiveProcess.Paper.lem_affine_events

@[expose] public section

/-! # Assembly of the model-level statement of the affine gap core (gamma-route)

Given the constants supplied by `candidate_good_estimates`, `goodext_represented_local_trace`,
`affine_comparison_poincare_event` and `lem_affine_gcn_competitor_l2`, the model-level statement
`lem_affine_gap_stmt` follows from `affine_cell_assembly`: the comparison cube of the good event has side
`m = 3^(-(k - floor(gamma H1) - 4))`, concentric with `q`; with `Lt = L / 27^(1/gamma)` one has
`Lt^gamma r <= m/729 <= Cin Lt^gamma r` (`Cin >= 3`) and `27 m <= L r` (`floor(gamma H1) + 7 <= H1`). -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

universe u

/-- The side of the chosen comparison cube of the gamma-route: `3^{-(k - a - 4)} = 3^(a+4) r`, `a = floor(gamma H1)`. -/
theorem aux_lem_affine_gap_model_cmp_side (H1 k a : ℕ) (ha : a + 7 ≤ H1) (S : ℝ)
    (hS : S = (3 : ℝ) ^ (-(((k : ℤ)) - (a : ℤ) - 4))) :
    S = (3 : ℝ) ^ (a + 4) * (3 : ℝ) ^ (-(k : ℤ)) ∧
      27 * S ≤ (3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ)) ∧
      81 * (3 : ℝ) ^ (-(k : ℤ)) ≤ S ∧
      S / 9 = (3 : ℝ) ^ (a + 2) * (3 : ℝ) ^ (-(k : ℤ)) := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hk : 0 < (3 : ℝ) ^ (-(k : ℤ)) := by positivity
  have hEq : S = (3 : ℝ) ^ (a + 4) * (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [hS, show -(((k : ℤ)) - (a : ℤ) - 4) = ((a : ℤ) + 4) + (-(k : ℤ)) by ring,
      zpow_add₀ h3]
    congr 1
  refine ⟨hEq, ?_, ?_, ?_⟩
  · rw [hEq]
    have h1 : (27 : ℝ) * (3 : ℝ) ^ (a + 4) ≤ (3 : ℝ) ^ H1 := by
      calc (27 : ℝ) * (3 : ℝ) ^ (a + 4) = (3 : ℝ) ^ (a + 7) := by ring
        _ ≤ (3 : ℝ) ^ H1 := pow_le_pow_right₀ (by norm_num) ha
    nlinarith only [h1, hk]
  · rw [hEq]
    have h1 : (81 : ℝ) ≤ (3 : ℝ) ^ (a + 4) := by
      calc (81 : ℝ) = (3 : ℝ) ^ 4 := by norm_num
        _ ≤ (3 : ℝ) ^ (a + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith only [h1, hk]
  · rw [hEq]
    have : (3 : ℝ) ^ (a + 4) / 9 = (3 : ℝ) ^ (a + 2) := by
      rw [show a + 4 = (a + 2) + 2 by ring, pow_add]; norm_num
    rw [← this]; ring

/-- Scalar geometry of the comparison window: `R = m/729`, `Lt = L / 27^(1/gamma)`, `Lt^gamma = L^gamma / 27`. -/
theorem aux_lem_affine_gap_model_Lt (gamma : ℝ) (hg : 0 < gamma) (H1 a : ℕ) (r m Cin : ℝ)
    (hr : 0 < r) (ha1 : (a : ℝ) ≤ gamma * (H1 : ℝ)) (ha2 : gamma * (H1 : ℝ) < (a : ℝ) + 1)
    (hm : m = (3 : ℝ) ^ (a + 4) * r) (hCin : 3 ≤ Cin) :
    ((3 : ℝ) ^ H1 / (27 : ℝ) ^ (1 / gamma)) ^ gamma * r ≤ m / 729 ∧
      m / 729 ≤ Cin * ((3 : ℝ) ^ H1 / (27 : ℝ) ^ (1 / gamma)) ^ gamma * r ∧
      (3 : ℝ) ^ H1 / ((3 : ℝ) ^ H1 / (27 : ℝ) ^ (1 / gamma)) = (27 : ℝ) ^ (1 / gamma) ∧
      0 < (3 : ℝ) ^ H1 / (27 : ℝ) ^ (1 / gamma) ∧
      (3 : ℝ) ^ H1 / (27 : ℝ) ^ (1 / gamma) ≤ (3 : ℝ) ^ H1 := by
  have h27 : (0 : ℝ) < (27 : ℝ) ^ (1 / gamma) := Real.rpow_pos_of_pos (by norm_num) _
  have hL : (0 : ℝ) < (3 : ℝ) ^ H1 := by positivity
  have hLt : 0 < (3 : ℝ) ^ H1 / (27 : ℝ) ^ (1 / gamma) := div_pos hL h27
  have hpow : ((3 : ℝ) ^ H1 / (27 : ℝ) ^ (1 / gamma)) ^ gamma = (3 : ℝ) ^ (gamma * (H1 : ℝ)) / 27 := by
    rw [Real.div_rpow hL.le h27.le, ← Real.rpow_natCast (3 : ℝ) H1, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num)]
    have : 1 / gamma * gamma = 1 := by field_simp
    rw [this, Real.rpow_one, mul_comm (H1 : ℝ) gamma]
  have h3a : (3 : ℝ) ^ (gamma * (H1 : ℝ)) ≤ (3 : ℝ) ^ ((a : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2.le
  have h3b : (3 : ℝ) ^ (a : ℝ) ≤ (3 : ℝ) ^ (gamma * (H1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
  have e1 : (3 : ℝ) ^ ((a : ℝ) + 1) = 3 * (3 : ℝ) ^ a := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one]; ring
  have e2 : (3 : ℝ) ^ (a : ℝ) = (3 : ℝ) ^ a := Real.rpow_natCast _ _
  have hposP : 0 < (3 : ℝ) ^ (gamma * (H1 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hm729 : m / 729 = 3 ^ a / 9 * r := by
    rw [hm, pow_add]; ring
  refine ⟨?_, ?_, ?_, hLt, ?_⟩
  · rw [hpow, hm729]
    have : (3 : ℝ) ^ (gamma * (H1 : ℝ)) ≤ 3 * 3 ^ a := by rw [← e1]; exact h3a
    have : (3 : ℝ) ^ (gamma * (H1 : ℝ)) / 27 ≤ 3 ^ a / 9 := by linarith only [this]
    exact mul_le_mul_of_nonneg_right this hr.le
  · rw [hpow, hm729]
    have h1 : (3 : ℝ) ^ a ≤ (3 : ℝ) ^ (gamma * (H1 : ℝ)) := by rw [← e2]; exact h3b
    have h2 : (3 : ℝ) ^ a / 9 ≤ Cin * ((3 : ℝ) ^ (gamma * (H1 : ℝ)) / 27) := by
      have : (0 : ℝ) ≤ (3 : ℝ) ^ (gamma * (H1 : ℝ)) := hposP.le
      nlinarith only [h1, hCin, this]
    exact mul_le_mul_of_nonneg_right h2 hr.le
  · field_simp
  · exact div_le_self hL.le (Real.one_le_rpow (by norm_num) (by positivity))

/-- Assembly of the model-level statement of the affine gap core (`lem_affine_gap_stmt`) from the supplier
constants and `affine_cell_assembly`. -/
theorem lem_affine_gap_model
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I) (Cp : Lane4.CampanatoInput d)
    (beta alpha gamma zeta rho s sigma cell : ℝ) (cbuf k0 H1 : ℕ)
    (epshom Cbound eps0 lam0 delta0 : ℝ)
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) (hba : beta < alpha) (hgamma : 0 < gamma)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) (hfloor : Nat.floor (gamma * (H1 : ℝ)) + 6 < H1)
    (hCbound1 : 1 ≤ Cbound) (hepshom : 0 < epshom) (hepshomHalf : epshom ≤ 1 / 2)
    (deltaCGE Csharp deltaSharp deltaPoinc Cin src0 : ℝ)
    (hd1 : delta0 ≤ deltaCGE) (hd2 : delta0 ≤ deltaSharp) (hd3 : delta0 ≤ deltaPoinc)
    (hd4 : delta0 ≤ aux_lem_affine_events_growthDelta d hd I Pin _X _MeyersMorrey Cp _Sob beta
      ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hbeta, hbeta1⟩)
    (hCGEi : lem_affine_stmt_cge.{0} d hd I alpha beta s sigma cell epshom Cbound eps0 lam0
      deltaCGE)
    (hTri : aux_lem_affine_gap_stmt_trace d hd I beta Csharp deltaSharp)
    (hPoi : aux_lem_affine_gap_stmt_poinc d hd I Pin deltaPoinc)
    (hCin1 : 1 ≤ Cin) (hCin3 : 3 ≤ Cin)
    (hCinC : Real.sqrt (d : ℝ) ^ alpha *
      (Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))) ≤ Cin)
    (hCinE : Csharp * (2 * cell⁻¹) ≤ Cin)
    (hCinP : 729 * Real.sqrt (2 * (Pin.C ^ 2 * ((Homogenization.Book.Ch02.geometricDiscount s 2 /
      Homogenization.Book.Ch02.geometricDiscount 1 1) * (1 / 5 : ℝ))⁻¹)) *
      ((27 : ℝ) ^ (1 / gamma)) ^ (((d : ℝ) + zeta) / 2) ≤ Cin)
    (hsrc0 : 0 < src0)
    (hInst : aux_affine_gap_cell_gcnInstance d alpha beta gamma zeta rho Cin
      ((3 : ℝ) ^ H1 / (27 : ℝ) ^ (1 / gamma)) epshom src0) :
    lem_affine_gap_stmt.{u} d hd I beta alpha gamma zeta rho s sigma cell cbuf k0 H1 epshom Cbound
      eps0 lam0 delta0 := by
  have hAlphaPos : 0 < alpha := lt_trans (by norm_num) (lt_trans hbeta hba)
  have hKP0 : 0 ≤ Pin.C ^ 2 * ((Homogenization.Book.Ch02.geometricDiscount s 2 /
      Homogenization.Book.Ch02.geometricDiscount 1 1) * (1 / 5 : ℝ))⁻¹ :=
    aux_lem_affine_KP_nonneg s Pin.C hs
  have hCtotal0 : 0 ≤ Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) := by
    have : 0 ≤ Cbound := by linarith only [hCbound1]
    positivity
  unfold lem_affine_gap_stmt
  intro L
  refine @fun M H hMH Rm Sreg _It Ω hΩ P hP field hfieldMeas hfieldLaw env hEnvMeas hEnvLaw
    hEnvConv hdisorder Qcentre Qside hQside S hS GN hGN phi hphi RootIndex _ _ root0 zCat rCat
    hrCat SCat DCat _ fCat TCat _ thetaCat thetaH1Cat usrc srcRep ucell Cext etaCat t orders
    Index _ resp respLim constants Gcat coercivityKey extensionKey lambdaKey
    sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
    cellGrowthKey cellHolderKey Grid _ origin gridRoot gridKey hRootCatalogue
    hRep GE hGE E hE GammaE eRef heRefPos heRefLim c hc => ?_
  intro Q
  refine @fun J gridChoice hGridChoice => ?_
  intro origins
  classical
  have hGridCap := goodext_catalog_grid_coefficient_bound d hd M H Ω P phi
    (fun n => env PUnit.unit n) RootIndex root0 zCat rCat hrCat SCat DCat
    fCat TCat thetaCat thetaH1Cat
    (fun j => usrc PUnit.unit j) (fun j g => srcRep PUnit.unit j g)
    (fun j h => ucell PUnit.unit j h) Cext beta alpha etaCat t orders I Index
    (resp PUnit.unit) (respLim PUnit.unit) (constants PUnit.unit) Gcat
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
    sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot
    gridKey (hRep PUnit.unit) J gridChoice hGridChoice
  have hGcat : ∀ᵐ om ∂P, om ∈ Gcat := by
    have hRepUnit := hRep PUnit.unit
    unfold conv_represented_estimates at hRepUnit
    rcases hRepUnit with ⟨_, _, _, _, _, _, _, _, _, hSequence, _⟩
    rcases hSequence with ⟨_, _, hGcatNull, _, _⟩
    rw [ae_iff]
    simpa only [Set.mem_compl_iff, not_not] using! hGcatNull
  have hetaCat2 : etaCat < 2 := by
    rcases (hRep PUnit.unit).2.1 with ⟨ha, heta, hetaAlpha⟩
    linarith only [hetaAlpha, ha]
  have hCBeq : ∀ om (hom : om ∈ Gcat), (fun om => if h : om ∈ Gcat then
      Classical.choose (hGridCap om h) else (0 : ℝ)) om = Classical.choose (hGridCap om hom) :=
    fun om hom => dif_pos hom
  have hmeshEx : ∀ (om : Ω) (f : SpatialCoordinates d → ℝ), ∃ r0 : ℝ, 0 < r0 ∧
      ∀ r : ℝ, 0 < r → r ≤ r0 →
        ((2 * (Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))) *
          ((3 : ℝ) ^ (Nat.floor (gamma * (H1 : ℝ)) + 2)) ^ 2 + 1) * sSup {v : ℝ | ∃ x ∈ closure
          (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), v = |f x|} *
          Real.sqrt ((fun om => if h : om ∈ Gcat then
            Classical.choose (hGridCap om h) else (0 : ℝ)) om * cell⁻¹)) *
          r ^ (1 - etaCat / 2) ≤ src0 * Real.sqrt c := by
    intro om f
    have hfsup : 0 ≤ sSup {v : ℝ | ∃ x ∈ closure
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), v = |f x|} := by
      apply Real.sSup_nonneg
      rintro v ⟨x, -, rfl⟩
      exact abs_nonneg _
    refine aux_lem_affine_events_mesh_exists _ etaCat _ ?_ hetaCat2 (by positivity)
    positivity
  refine ⟨fun om f => Classical.choose (hmeshEx om f),
    Filter.Eventually.of_forall (fun om f _ => (Classical.choose_spec (hmeshEx om f)).1), ?_⟩
  refine @fun n z zP gridIndex parentIndex idx => ?_
  intro k r q parentCell
  refine @fun hParentGrid hChildCenter
    hParentCell qside hqside qcenter hqcenter Enl Shift Cmp instFintypeEnl instFintypeShift
    instFintypeCmp selfE selfShift qRoot hqRoot factor hfactor padE hpadE shift hshift
    rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos hGridCover
    parent depth word cmpCentre hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos
    chosen hcmpChosenCentre hcmpChosenLevel hcmpChosenPad
    observationCentre hObservationCentre eta hEta F Praw Rraw Draw Z rawGood
    eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN
    ellLoN ellHiN hEllLoN hEllHiN AEN hAEN errN ratioN hErrN hRatioN
    sE sCmp hsE hsCmp
    prefixZLim prefixDLim ellLoLim ellHiLim AE_Lim errLim ratioLim
    hPrefixZLim hPrefixDLim hEllLoLim hEllHiLim hAELim hErrLim hRatioLim hRootsQ => ?_
  intro Good
  have hrpos : 0 < r := by simp only [r]; positivity
  have hLpos : 0 < L := by simp only [L]; positivity
  have hgrid := aux_lem_affine_events_cell_grid H1 r L hrpos rfl
    (origin (gridChoice gridIndex)) zP z parentIndex idx hParentGrid hChildCenter
  have ha7 : Nat.floor (gamma * (H1 : ℝ)) + 7 ≤ H1 := by omega
  have hcmp := aux_lem_affine_gap_model_cmp_side H1 k (Nat.floor (gamma * (H1 : ℝ))) ha7
    (cmpSide chosen) (by rw [hcmpSide chosen, hcmpChosenLevel])
  have hmpos : 0 < cmpSide chosen := cmpPos chosen
  have hgeo1 : 27 * cmpSide chosen ≤ L * r := hcmp.2.1
  have hgeo22 : Metric.ball z (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) :=
    Metric.ball_subset_closedBall.trans
      ((Metric.closedBall_subset_closedBall (by linarith only [hcmp.2.2.1, hrpos])).trans
        hcmpChosenPad)
  have hLtf := aux_lem_affine_gap_model_Lt gamma hgamma H1 (Nat.floor (gamma * (H1 : ℝ))) r
    (cmpSide chosen) Cin hrpos (Nat.floor_le (by positivity)) (Nat.lt_floor_add_one _) hcmp.1 hCin3
  have hG1 : ∀ om ∈ Good, errLim chosen om ≤ epshom * cdet := fun om hom => hom.2.2.1
  have hG2 : ∀ om ∈ Good, ∀ U : Enl × Shift, ellHiLim U om ≤ cell⁻¹ :=
    fun om hom U => (hom.2.1 U).2
  have hG3 : ∀ om ∈ Good, ∀ c' : Cmp, ratioLim c' om ∈ Set.Ioo (1 / 2 : ℝ) 2 :=
    fun om hom c' => hom.2.2.2 c'
  have hsE1 := hsE.1
  have hbank := lem_affine_events d hd I Pin _X _MeyersMorrey Cp _Sob beta hbeta hbeta1
    M Rm Sreg _It H hMH (hdisorder.trans hd4) Ω P (fun n => env PUnit.unit n)
    (fun n => hEnvMeas PUnit.unit n) (fun n => hEnvLaw PUnit.unit n) phi Qcentre Qside hQside
    S hS GN hGN GE hGE
  have hsCmp1 : ∀ᵐ om ∂P, 0 < sCmp chosen om ∧ Tendsto
      (fun n => sN (phi n) (cmpLevel chosen) (cmpCentre chosen) (env PUnit.unit n om)) atTop
      (𝓝 (sCmp chosen om)) := by
    filter_upwards [hsCmp] with om h
    exact h chosen
  have hratio := ae_inv_le_two_mul_inv_of_ratio_mem_Ioo Good
    (fun n om => sN (phi n) (k : ℤ) z (env PUnit.unit n om))
    (fun n om => sN (phi n) (cmpLevel chosen) (cmpCentre chosen) (env PUnit.unit n om))
    sE (sCmp chosen) (ratioLim chosen) hsE1 hsCmp1
    (by
      have h := hRatioLim chosen
      simp only [hRatioN, hqcenter] at h
      exact h)
    (fun om hom => hG3 om hom chosen)
  have hCandidateEst := hCGEi cbuf k0 M Rm Sreg _It H hMH Ω P field hfieldMeas hfieldLaw
    (fun _ n => env PUnit.unit n) (fun _ n => hEnvMeas PUnit.unit n)
    (fun _ n => hEnvLaw PUnit.unit n)
    (by filter_upwards [hEnvConv] with om h a; exact h PUnit.unit)
    k z qside hqside qcenter hqcenter
    Enl Shift Cmp selfE selfShift qRoot hqRoot factor hfactor padE hpadE shift hshift
    rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos hGridCover
    parent depth word cmpCentre hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos
    chosen observationCentre hObservationCentre eta hEta F Praw Rraw Draw Z rawGood
    eps heps hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds
    hcdet hcdetSmall hlamSmall (hdisorder.trans hd1) prefixZ prefixD hPrefixZ hPrefixD
    hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN AEN hAEN errN ratioN
    hErrN hRatioN phi hphi prefixZLim prefixDLim ellLoLim ellHiLim AE_Lim errLim
    ratioLim hPrefixZLim hPrefixDLim hEllLoLim hEllHiLim hAELim hErrLim hRatioLim
    Qcentre Qside hQside hRootsQ S hS GN hGN GE hGE E hE GammaE sE sCmp
    hsE1 hsCmp
  have hcubeP := aux_lem_affine_events_cube_le z zP (cmpCentre chosen) (cmpSide chosen)
    (L * r / 2) hmpos Qcentre Qside hQside hcmpChosenCentre hcmpChosenPad hParentCell
  have hcontP : ∀ᵐ om ∂P, ∀ f : DomainL2 (centeredCube Qcentre Qside hQside),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
        (GE om f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
          U x = 0 := by
    filter_upwards [hbank] with om h f hf
    obtain ⟨fc, hfc, -, -, hfae⟩ := hf
    exact h fc hfc f hfae
  have hscale : ∀ (n : ℕ) (om : Ω),
      0 < sN (phi n) (cmpLevel chosen) (cmpCentre chosen) (env PUnit.unit n om) :=
    fun n om => aux_in_deterministic_regularity_sN_pos M H sN hsN _ _ _ _
  have hPoincE := hPoi M Rm Sreg _It H hMH (hdisorder.trans hd3) Qcentre Qside hQside S hS
    phi hphi Ω P (fun n => env PUnit.unit n) (fun n => hEnvMeas PUnit.unit n)
    (fun n => hEnvLaw PUnit.unit n) GN hGN GE hGE E hE GammaE hcontP (cmpCentre chosen)
    (cmpSide chosen) (cmpPos chosen) hcubeP.1 parentCell Metric.isOpen_ball hcubeP.2 s hs
    (by linarith only [hsSmall])
    (fun n om => sN (phi n) (cmpLevel chosen) (cmpCentre chosen) (env PUnit.unit n om)) hscale
    (sCmp chosen) hsCmp1 (errLim chosen)
    (by
      have h := hErrLim chosen
      simp only [hErrN] at h
      exact h)
  have hcz : rootCentre qRoot = z := by
    rw [hqRoot, hrootCentre, hshift, smul_zero, add_zero, hqcenter]
  have hlz : rootLevel qRoot = (k : ℤ) := by
    rw [hqRoot, hrootLevel, hfactor]; simp only [Nat.cast_zero, sub_zero]
  have hsz : rootSide qRoot = (3 : ℝ) ^ (-(k : ℤ)) := by rw [hrootSide, hlz]
  have hNorm := aux_lem_affine_events_norm_transport I M H P phi (fun n => env PUnit.unit n) sN
    ((beta - 1 / 2) / 4) (ellHiLim qRoot) (rootCentre qRoot) z (rootSide qRoot) (rootPos qRoot)
    (rootLevel qRoot) k hcz hsz hlz hrpos
    (by
      have h := hEllHiLim qRoot
      simp only [hEllHiN] at h
      rw [hsigma_eq] at h
      exact h)
  have hExtE := hTri M Rm Sreg _It H hMH (hdisorder.trans hd2) Qcentre Qside hQside S hS k z
    phi hphi Ω P (fun n => env PUnit.unit n) (fun n => hEnvMeas PUnit.unit n)
    (fun n => hEnvLaw PUnit.unit n) GN hGN GE hGE E hE GammaE hcontP
    (fun n om => sN (phi n) (k : ℤ) z (env PUnit.unit n om)) sE (ellHiLim qRoot) hsE1 hNorm
    (cell⁻¹) (inv_pos.2 hcell.1)
  have hsubRoot : (centeredCube z r hrpos : Set (SpatialCoordinates d)) ⊆
      (centeredCube (zCat root0) (rCat root0) (hrCat root0) : Set (SpatialCoordinates d)) := by
    rw [← aux_lem_affine_events_cube_congr Qcentre (zCat root0) Qside (rCat root0) hQside
      (hrCat root0) hRootCatalogue.1.symm hRootCatalogue.2.symm, centeredCube_coe_eq_ball]
    exact (Metric.ball_subset_ball (by linarith only [hrpos])).trans (hgeo22.trans hParentCell)
  have hcapRoot : ∀ᵐ om ∂P, 0 ≤ (fun om => if h : om ∈ Gcat then
        Classical.choose (hGridCap om h) else (0 : ℝ)) om ∧ ∀ᶠ n in atTop,
      I.Lam z r hrpos (cutoffPositiveCoefficient M H (env PUnit.unit n om) (phi n) z hrpos)
        z r ((beta - 1 / 2) / 4) 2 +
      (I.lam z r hrpos (cutoffPositiveCoefficient M H (env PUnit.unit n om) (phi n) z hrpos)
        z r ((beta - 1 / 2) / 4) 2)⁻¹ ≤ (fun om => if h : om ∈ Gcat then
        Classical.choose (hGridCap om h) else (0 : ℝ)) om * r ^ (-etaCat) := by
    filter_upwards [hGcat] with om hom
    have hK := Classical.choose_spec (hGridCap om hom)
    rw [← hCBeq om hom] at hK
    exact ⟨hK.1, aux_lem_affine_events_hcap I M H phi hphi (fun n => env PUnit.unit n)
      (zCat root0) (rCat root0) (hrCat root0) J (fun i => origin (gridChoice i)) etaCat
      ((beta - 1 / 2) / 4) _ om hK.2 k gridIndex z hgrid.1 hrpos hsubRoot⟩
  have hsigma' : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := by rw [← hsigma_eq]; exact hsigma
  have hEV0 := goodext_reference_inverse_from_cell_cap I P z r hrpos
    (fun n om => cutoffPositiveCoefficient M H (env PUnit.unit n om) (phi n) z hrpos)
    ((beta - 1 / 2) / 4) hsigma' (fun n om => sN (phi n) (k : ℤ) z (env PUnit.unit n om)) sE
    (ellHiLim qRoot) (fun om => if h : om ∈ Gcat then
        Classical.choose (hGridCap om h) else (0 : ℝ)) etaCat (cell⁻¹) hsE1 hcapRoot hNorm
  have hcdet1 : cdet ≤ 1 := hcdetSmall.trans (inv_le_one_of_one_le₀ hCbound1)
  have hlt1 : epshom * cdet < 1 := by nlinarith only [hepshomHalf, hcdet1, hcdet, hepshom]
  have hfsupNN : ∀ f : SpatialCoordinates d → ℝ, 0 ≤ sSup {v : ℝ | ∃ x ∈ closure
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), v = |f x|} := by
    intro f
    apply Real.sSup_nonneg
    rintro v ⟨x, -, rfl⟩
    exact abs_nonneg _
  exact affine_cell_assembly d hd alpha beta gamma zeta rho hAlphaPos Cin
    ((3 : ℝ) ^ H1 / (27 : ℝ) ^ (1 / gamma)) epshom src0 hepshom.le hsrc0.le hInst Ω P Qcentre Qside
    hQside GE E GammaE Good (fun om f => Classical.choose (hmeshEx om f)) z zP (cmpCentre chosen)
    hcmpChosenCentre r (cmpSide chosen) L hrpos hmpos hLtf.1 hLtf.2.1 hcmpChosenPad hParentCell
    hgeo1 hLtf.2.2.2.1 hLtf.2.2.2.2 c hc sE (sCmp chosen)
    (Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))))
    (Pin.C ^ 2 * ((Homogenization.Book.Ch02.geometricDiscount s 2 /
      Homogenization.Book.Ch02.geometricDiscount 1 1) * (1 / 5 : ℝ))⁻¹)
    (Csharp * (2 * cell⁻¹)) hCtotal0 hKP0 hCinC hCinE (by rw [hLtf.2.2.1]; exact hCinP) hbank
    (by filter_upwards [hsE1] with om h; exact h.1)
    (by filter_upwards [hsCmp1] with om h; exact h.1) hratio
    (by
      filter_upwards [hCandidateEst] with om h hG f hf fL2 hfL2
      exact (h hG).1 f hf fL2 hfL2)
    (by
      filter_upwards [hPoincE] with om h hG fL2 U hU
      have h1 := h (lt_of_le_of_lt (hG1 om hG) hlt1) fL2 U hU
      rw [hcmpChosenCentre] at h1
      refine h1.trans (le_of_eq ?_)
      ring)
    (by
      filter_upwards [hExtE] with om h hG g hgc hgH
      have hsub3 : Metric.ball z (r / 2) ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) :=
        (Metric.ball_subset_ball (by linarith only [hrpos])).trans (hgeo22.trans hParentCell)
      obtain ⟨v, V, hv, hVc, hVae, hVb, hbd⟩ := h (hG2 om hG qRoot) (hgeo22.trans hParentCell) g
        (hgc.mono (frontier_subset_closure.trans (closure_mono hsub3))) hgH
      exact ⟨v, V, hv, hVc, hVae, hVb, hbd.trans (le_of_eq (by ring))⟩)
    (by
      filter_upwards [hEV0, hratio, hsE1, hcapRoot] with om hE0 hrat hsEom hcap
      intro hG f hf hmesh
      have hE0' := hE0 (hG2 om hG qRoot)
      have hmeshspec := (Classical.choose_spec (hmeshEx om f)).2 r hrpos hmesh
      refine aux_lem_affine_events_src (Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))))
        ((3 : ℝ) ^ (Nat.floor (gamma * (H1 : ℝ)) + 2)) _ ((fun om => if h : om ∈ Gcat then
          Classical.choose (hGridCap om h) else (0 : ℝ)) om * cell⁻¹) c etaCat src0 r
        (cmpSide chosen) (sE om) ((sCmp chosen om)⁻¹) hCtotal0 (hfsupNN f)
        (mul_nonneg hcap.1 (inv_nonneg.2 hcell.1.le)) hc hetaCat2 hrpos hsEom.1
        hcmp.2.2.2 (hrat hG)
        (hE0'.trans (le_of_eq (by ring))) hmeshspec)


end Paper
end
