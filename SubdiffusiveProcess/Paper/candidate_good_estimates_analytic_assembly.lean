module

public import SubdiffusiveProcess.Paper.candidate_good_estimates_analytic_contract
public import SubdiffusiveProcess.Paper.candidate_good_estimates_trace_support
public import SubdiffusiveProcess.Paper.candidate_harmonic_represented_passage
public import SubdiffusiveProcess.Sobolev.HarmonicErrorCalibration

@[expose] public section

/-! The trace estimate and the represented harmonic passage give the full analytic source input.
This assembly keeps the deterministic constant before the accuracy parameter and does not assert the trace supplier.
-/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper
universe uCge

/-- Enlarge the trace constant once and combine its representative with the actual represented harmonic window. -/
theorem candidate_good_estimates_analytic_assembly
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Poincare : Paper.in_poincare d hd I)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (_Step : Paper.cutoff_good_scale_input d)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (alpha beta s sigma cell : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (hTrace : aux_candidate_good_estimates_analytic_contract_trace.{uCge} d hd I _X _Sob _Poincare _MeyersMorrey _Step D Cp alpha beta s sigma cell halpha hbeta hs hsSmall hsigma_eq hsigma hcell) :
    candidate_good_estimates_analytic_contract.{uCge} d hd I _X _Sob _Poincare _MeyersMorrey _Step D Cp alpha beta s sigma cell halpha hbeta hs hsSmall hsigma_eq hsigma hcell  := by
  obtain ⟨CA, hCA, hCAlo, hCAhi, hCAdim, hTrace⟩ := hTrace
  obtain ⟨Charm, E0, hCharm, hE0, hWindow⟩ :=
    aux_in_deterministic_core_harm_window_holds d hd I D alpha s halpha hs hsSmall
  obtain ⟨deltaG, hdeltaG, hGrowth⟩ :=
    candidate_good_estimates_trace_support d hd I _Poincare _X
      _MeyersMorrey Cp _Sob beta
      ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hbeta.1, hbeta.2⟩
  let Cbound := max CA (max Charm (2 / E0))
  have hCAC : CA ≤ Cbound := le_max_left _ _
  have hC : 1 ≤ Cbound := hCA.trans hCAC
  have hCApos : 0 < CA := zero_lt_one.trans_le hCA
  have hCpos : 0 < Cbound := zero_lt_one.trans_le hC
  have hInv : Cbound⁻¹ ≤ CA⁻¹ := (inv_le_inv₀ hCpos hCApos).mpr hCAC
  have hCharmC : Charm ≤ Cbound := (le_max_left _ _).trans (le_max_right _ _)
  have hEC : 2 / E0 ≤ Cbound := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Cbound, hC, hInv.trans hCAlo, hCAhi.trans hCAC,
    hCAdim.trans (mul_le_mul_of_nonneg_right hCAC (sq_nonneg cell)), ?_⟩
  intro epshom hepshom hepshom_le
  obtain ⟨eps0, lam0, deltaA, heps0, hlam0, hdeltaA, hSourceA⟩ :=
    hTrace epshom hepshom hepshom_le
  refine ⟨eps0, lam0, min deltaA deltaG, heps0, hlam0, lt_min hdeltaA hdeltaG, ?_⟩
  intro cbuf k0 M _Rm Sreg _It H hMH Ω _instΩ P _instP field hfieldMeas hfieldLaw
    env hEnvMeas hEnvLaw hEnvConv k z qside hqside qcenter hqcenter Enl Shift Cmp
    _instEnl _instShift _instCmp selfE selfShift qRoot hqRoot factor hfactor padE hpad
    shift hshift rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos
    hGridCover parent depth word cmpCentre hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide
    cmpPos chosen observationCentre hObservationCentre eta hEta F Praw Rraw Draw Z rawGood
    eps heps hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet
    hcdetSmall hlamSmall hdisorder prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN
    ellLoN ellHiN hEllLoN hEllHiN AEN hAEN errN ratioN hErrN hRatioN phi hphi prefixZLim
    prefixDLim ellLoLim ellHiLim AE_Lim errLim ratioLim hPrefixZLim hPrefixDLim hEllLoLim
    hEllHiLim hAELim hErrLim hRatioLim Qcentre Qside hQside hRootsQ S hS GN hGN GE hGE E hE
    GammaE sE sCmp hsE hsCmp
  have hcdetA : cdet ≤ CA⁻¹ := hcdetSmall.trans hInv
  have hdisorderA : M.delta ≤ deltaA := hdisorder.trans (min_le_left _ _)
  have hAnalyticA := @hSourceA cbuf k0 M _Rm Sreg _It H hMH Ω _instΩ P _instP field hfieldMeas hfieldLaw env hEnvMeas hEnvLaw hEnvConv k z qside hqside qcenter hqcenter Enl Shift Cmp _instEnl _instShift _instCmp selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetA hlamSmall hdisorderA prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN AEN hAEN errN ratioN hErrN hRatioN phi hphi prefixZLim prefixDLim ellLoLim ellHiLim AE_Lim errLim ratioLim hPrefixZLim hPrefixDLim hEllLoLim hEllHiLim hAELim hErrLim hRatioLim Qcentre Qside hQside hRootsQ S hS GN hGN GE hGE E hE GammaE sE sCmp hsE hsCmp
  obtain ⟨K, Cmoment, _hCmoment, hKmem, hKnorm, _, hKsource⟩ :=
    hGrowth M _Rm Sreg _It H hMH (hdisorder.trans (min_le_right _ _)) Qcentre Qside hQside
  let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
  have hCtotal : Charm ≤ Ctotal := hCharmC.trans
    (le_exponential_scale_factor hCpos.le (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have hsNpos := aux_in_deterministic_regularity_sN_pos M H sN hsN
  have hErrConv : TendstoInMeasure P
      (fun n omega => I.err (cmpCentre chosen) (cmpSide chosen) (cmpPos chosen)
        (cutoffPositiveCoefficient M H (env PUnit.unit n omega) (phi n)
          (cmpCentre chosen) (cmpPos chosen))
        (cmpCentre chosen) (cmpSide chosen)
        (sN (phi n) (cmpLevel chosen) (cmpCentre chosen) (env PUnit.unit n omega)) s 2)
      atTop (errLim chosen) := by
    simpa only [hErrN] using hErrLim chosen
  have hB := candidate_harmonic_represented_passage hd _Sob I alpha beta s Charm E0
    halpha hbeta hCharm hWindow M H P (env PUnit.unit) (hEnvMeas PUnit.unit)
    (hEnvLaw PUnit.unit) phi Qcentre Qside hQside S hS GN hGN GE hGE
    K Cmoment.toNNReal hKmem hKnorm hKsource
    (cmpCentre chosen) (cmpSide chosen) (cmpPos chosen) (cmpLevel chosen) (hcmpSide chosen)
    (fun n omega => sN (phi n) (cmpLevel chosen) (cmpCentre chosen) (env PUnit.unit n omega))
    (sCmp chosen) (fun n omega => hsNpos _ _ _ _) (hsCmp.mono fun _ h => h chosen)
    (errLim chosen) hErrConv epshom Ctotal hCtotal
  have hFactors : CA * (3 : ℝ) ^ (CA * ((k0 : ℝ) + (cbuf : ℝ))) ≤ Ctotal :=
    exponential_scale_factor_mono hCApos.le hCAC (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  filter_upwards [hAnalyticA, hB, hsE] with omega hA hB hsE
  intro hGood f hf fL2 hfL2
  obtain ⟨U, hUc, hUr, hUb, hUh, cq, hUcq⟩ := hA hGood f hf fL2 hfL2
  refine ⟨U, hUc, hUr, hUb, hUh, ⟨cq, hUcq.trans ?_⟩, ?_⟩
  · apply mul_le_mul_of_nonneg_right hFactors
    exact add_nonneg (Section6Iteration.normalizedL2On_nonneg _ _)
      (mul_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hsE.1.le))
        (Real.sSup_nonneg (by rintro v ⟨x, hx, rfl⟩; exact abs_nonneg _)))
  · have hSmall := harmonic_error_calibration hC hCharm hCharmC hE0 hEC
      hepshom hepshom_le hcdetSmall hGood.2.2.1
    exact hB hSmall.1 hSmall.2 f hf fL2 hfL2 U hUc hUr

end Paper
