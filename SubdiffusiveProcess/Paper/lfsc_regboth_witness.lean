module

public import SubdiffusiveProcess.Paper.lfsgs_hRegWitness_of_arbitrary_Rm
public import SubdiffusiveProcess.FiniteStopping.LayerWindowWitness

@[expose] public section

/-! Layer windows for the regularity predicate `Reg` of BOTH infrared coefficients (`H` and the infrared-free
coefficient `0`) with COMMON constants `Cfin, pad`: the `infrared = true` and `infrared = false` branches of one
application of `lem_finite_good_cell` (paper `\label{mfd:lem-finite-good-cell}`: "The conclusions hold simultaneously
for `A_N` and `A_N^0`"). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.FiniteStopping
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.Paper

theorem lfsc_regboth_witness
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Sobolev : SobolevFoundationalInput d hd)
    (MeyersMorrey : SmallPerturbationInput d)
    (Cp : CampanatoInput d)
    (Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Dbase : _root_.SubdiffusiveProcess.Paper.sum_errors_baseline_input d)
    (alpha beta rate : ℝ) (hbeta : 1 / 2 < beta)
    (hba : beta < alpha) (halpha : alpha < 1) (hrate : 0 < rate)
    (H1 : ℕ) (hH1 : 0 < H1) (hH4 : 4 ≤ H1) :
    ∃ Cfin pad delta0 sigma eps : ℝ, 0 < Cfin ∧ ∃ hpad : (1 : ℝ) < pad, pad ≤ 3 ∧ 0 < delta0 ∧
      sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ eps ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization model H),
        model.delta ≤ delta0 →
        ∀ (N k : ℕ) (z : SpatialCoordinates d), k ≤ N →
          has_layer_windows (chaosSampleLaw model).toMeasure k rate
            (Reg model H alpha H1 pad Cfin hpad N k z) ∧
          has_layer_windows (chaosSampleLaw model).toMeasure k rate
            (Reg model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) alpha H1 pad Cfin hpad N k z) := by
  classical
  obtain ⟨C0, hC0pos, hbank⟩ := _root_.SubdiffusiveProcess.Paper.paper_responses_bank d hd
  obtain ⟨sigma, eps, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _,
      hsigma, heps, _, _, _, _, _, _, _, _, _, _, _,
      delta0, Cfin, _, pad,
      hdelta0, hCfin, _,
      hpad,
      hpadL, hpad3, _, hinner⟩ :=
    _root_.SubdiffusiveProcess.Paper.lem_finite_good_cell d hd I Poincare Extension Sobolev MeyersMorrey Cp Step D Dbase
      C0 hC0pos alpha beta rate hbeta hba halpha hrate H1 hH1
  refine ⟨Cfin, pad, delta0, sigma, eps, hCfin, hpad, hpad3, hdelta0, hsigma, heps, ?_⟩
  intro model Rm Sreg It H hH hdelta N k z hkN
  obtain ⟨Rm', hRmC, -, -⟩ :=
    hbank model Rm.ahom_ordering Rm.ahom_le_one Rm.ahom_lower
      (_root_.SubdiffusiveProcess.Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect model)
      (_root_.SubdiffusiveProcess.Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect_nonneg model)
      (_root_.SubdiffusiveProcess.Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect_isGreatest model)
  have hRmCresp : Rm'.C ≤ C0 := le_of_eq hRmC
  obtain ⟨eta0, F0, Praw0, Rraw0, Draw0, Z0, rawGood0, hEta0, hprim0⟩ :=
    _root_.SubdiffusiveProcess.Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_primitive_scores_exists model sigma eps hsigma heps
  obtain ⟨Good, Carrier, hCarrierMeas, hCarrierNull, hGoodIff, hGoodMeasW, hClause⟩ :=
    hinner model Rm' hRmCresp Sreg It H hH hdelta eta0 hEta0
      F0 Praw0 Rraw0 Draw0 Z0 rawGood0 hprim0
  obtain ⟨_, W, hWmeas, hWdecay, hWcover⟩ := hGoodMeasW (N - k) k z
  have hcarr : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, omega ∈ Carrier := by
    rw [ae_iff]; simpa only using! hCarrierNull
  have hmk : N - k + k = N := Nat.sub_add_cancel hkN
  refine ⟨⟨W, hWmeas, hWdecay, ?_⟩, ⟨W, hWmeas, hWdecay, ?_⟩⟩
  · filter_upwards [hcarr] with omega homega hnReg
    by_contra hnotin
    have hgmem : omega ∈ Good (N - k) k z := by
      by_contra hcon
      exact hnotin (hWcover hcon)
    apply hnReg
    have hgoodclause := (hClause omega homega (N - k) k z hgmem true).1
    simp only [hmk, ite_true] at hgoodclause
    first
      | exact hgoodclause
      | exact hgoodclause hH4
  · filter_upwards [hcarr] with omega homega hnReg
    by_contra hnotin
    have hgmem : omega ∈ Good (N - k) k z := by
      by_contra hcon
      exact hnotin (hWcover hcon)
    apply hnReg
    have hgoodclause := (hClause omega homega (N - k) k z hgmem false).1
    simp only [hmk, Bool.false_eq_true, ite_false] at hgoodclause
    first
      | exact hgoodclause
      | exact hgoodclause hH4

end SubdiffusiveProcess.Paper
