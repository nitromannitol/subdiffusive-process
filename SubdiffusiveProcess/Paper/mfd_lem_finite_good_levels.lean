import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.finite_interval_packing_generic
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.lem_finite_good_cell
import SubdiffusiveProcess.Paper.lfsgs_hRegWitness_of_arbitrary_Rm
import SubdiffusiveProcess.Paper.lfsgs_primitive_scores_exists
import SubdiffusiveProcess.Paper.lfsgs_trace_witness
import SubdiffusiveProcess.Paper.paper_responses_bank
import SubdiffusiveProcess.Paper.sum_errors_baseline_input
import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison
import SubdiffusiveProcess.FiniteStopping.CellExtension
import SubdiffusiveProcess.FiniteStopping.CellRegularity
import SubdiffusiveProcess.FiniteStopping.ObservationTree
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization


set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff
noncomputable section

namespace Paper

/-- **Interval covers for the good-cell conclusions (ii) and (iii)** (`\label{mfd:lem-finite-good-cell}`, part (i)
of the lemma applied to both conclusions): for the constants `Cfin`, `Aext`, the padding `pad` and the disorder
threshold of `lem_finite_good_cell`, the event that the Hölder estimate `Reg` or the extension estimate `Ext`
fails for the cell of side `3^{-k}` at `z` at cutoff `N` is contained, almost surely, in a union of events
measurable with respect to the layers `-k-2h,…,-k+h` with probabilities at most `e^{-rate·h}`. -/
theorem aux_mfd_lem_finite_good_levels_regext_both_infrared
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d)
    (Poincare : Paper.in_poincare d hd I)
    (Extension : Paper.in_extension d hd I)
    (Sobolev : SobolevFoundationalInput d hd)
    (MeyersMorrey : SmallPerturbationInput d)
    (Cp : CampanatoInput d)
    (Step : Paper.cutoff_good_scale_input d)
    (D : Paper.lane4_deterministic_good_scale_input d)
    (Dbase : Paper.sum_errors_baseline_input d)
    (alpha beta rate : ℝ) (hbeta : 1 / 2 < beta)
    (hba : beta < alpha) (halpha : alpha < 1) (hrate : 0 < rate)
    (H1 : ℕ) (hH1 : 0 < H1) (hH1four : 4 ≤ H1) :
    ∃ Cfin Aext pad delta0 sigma eps : ℝ, 0 < Cfin ∧ 0 < Aext ∧ ∃ hpad : (1 : ℝ) < pad, pad ≤ 3 ∧
      0 < delta0 ∧ sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ eps ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : Paper.in_responses d model)
        (Sreg : Paper.in_6_16 d model) (_It : Paper.in_iteration d model I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization model H),
        model.delta ≤ delta0 →
        ∀ (N k : ℕ) (z : SpatialCoordinates d), k ≤ N →
          ∃ Wt : ℕ+ → Set (BilateralField d),
            (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
              ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).restrict)
              (inferInstance : MeasurableSpace
                ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
                  C(SpatialCoordinates d, ℝ)))] (Wt h)) ∧
            (∀ h : ℕ+, (chaosSampleLaw model).toMeasure (Wt h) ≤
              ENNReal.ofReal (Real.exp (-rate * (h : ℝ)))) ∧
            (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
              ¬(∀ infrared : Bool,
                let Hused : BilateralField d → C(SpatialCoordinates d, ℝ) :=
                  if infrared then H else 0
                SubdiffusiveProcess.FiniteStopping.Reg model Hused alpha H1 pad Cfin hpad N k z omega ∧
                SubdiffusiveProcess.FiniteStopping.Ext model Hused beta Aext N k z omega) →
                omega ∈ ⋃ h : ℕ+, Wt h) := by
  classical
  obtain ⟨C0, hC0pos, hbank⟩ := Paper.paper_responses_bank d hd
  obtain ⟨sigma, eps, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _,
      hsigma, heps, _, _, _, _, _, _, _, _, _, _, _,
      delta0, Cfin, Aext, pad,
      hdelta0, hCfin, hAext,
      hpad,
      hpadL, hpad3, _, hinner⟩ :=
    Paper.lem_finite_good_cell d hd I Poincare Extension Sobolev MeyersMorrey Cp Step D Dbase
      C0 hC0pos alpha beta rate hbeta hba halpha hrate H1 hH1
  refine ⟨Cfin, Aext, pad, delta0, sigma, eps, hCfin, hAext, hpad, hpad3, hdelta0, hsigma, heps, ?_⟩
  intro model Rm Sreg It H hH hdelta N k z hkN
  obtain ⟨Rm', hRmC, -, -⟩ :=
    hbank model Rm.ahom_ordering Rm.ahom_le_one Rm.ahom_lower
      (Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect model)
      (Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect_nonneg model)
      (Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_canonicalDefect_isGreatest model)
  have hRmCresp : Rm'.C ≤ C0 := le_of_eq hRmC
  obtain ⟨eta0, F0, Praw0, Rraw0, Draw0, Z0, rawGood0, hEta0, hprim0⟩ :=
    Paper.aux_lfsgs_hRegWitness_of_arbitrary_Rm_primitive_scores_exists model sigma eps hsigma heps
  obtain ⟨Good, Carrier, hCarrierMeas, hCarrierNull, hGoodIff, hGoodMeasW, hClause⟩ :=
    hinner model Rm' hRmCresp Sreg It H hH hdelta eta0 hEta0
      F0 Praw0 Rraw0 Draw0 Z0 rawGood0 hprim0
  obtain ⟨_, W, hWmeas, hWdecay, hWcover⟩ := hGoodMeasW (N - k) k z
  refine ⟨W, hWmeas, hWdecay, ?_⟩
  have hcarr : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, omega ∈ Carrier := by
    rw [ae_iff]; simpa only using hCarrierNull
  filter_upwards [hcarr] with omega homega hn
  by_contra hnotin
  have hgmem : omega ∈ Good (N - k) k z := by
    by_contra hcon
    exact hnotin (hWcover hcon)
  apply hn
  intro infrared
  have hgoodclause := hClause omega homega (N - k) k z hgmem infrared
  have hmk : N - k + k = N := Nat.sub_add_cancel hkN
  simp only [hmk] at hgoodclause
  exact ⟨hgoodclause.1 hH1four, hgoodclause.2⟩

section
open SubdiffusiveProcess.FiniteStopping

/-- One bad event controls Reg/Ext for both coefficient choices at both
cutoffs. The source trace comparison is for H; the zero-infrared weighted
comparison is transferred downstream, as in the paper. -/
theorem mfd_lem_finite_good_levels
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Step : @cutoff_good_scale_input d ⟨by omega⟩)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (Dbase : @sum_errors_baseline_input d ⟨by omega⟩ _ _)
    (alpha beta : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha1 : alpha < 1)
    (a b theta : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (htheta : 0 < theta)
    (H1 : ℕ) (hH1 : 4 ≤ H1) :
    haveI instNeZeroDimension : NeZero d := ⟨by omega⟩
    ∃ (Cfin Aext pad delta0 : ℝ) (hpad : (1 : ℝ) < pad), 0 < Cfin ∧ 0 < Aext ∧ pad ≤ 3 ∧ 0 < delta0 ∧
    ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d model)
      (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ delta0 →
    ∀ (zroot : SpatialCoordinates d) (jroot : ℤ),
    ∀ eta : ℝ, 0 < eta →
    ∃ (Ceta ceta : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < ceta ∧
    ∀ N M : ℕ, N0 ≤ N → N ≤ M →
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤
        ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ))) ∧
      ∀ omega ∉ Bad, ∀ w : ℕ → OddGridIndex d (subdivisionHalfWidth H1),
        let k : ℕ → ℤ := fun n => (H1 : ℤ) * (n : ℤ) - jroot
        let z : ℕ → SpatialCoordinates d := fun n =>
          descendantCenter (subdivisionHalfWidth H1) zroot ((3 : ℝ) ^ jroot) n
            (fun i : Fin n => w i)
        (Nat.card {n : ℕ // a * (N : ℝ) ≤ (k n : ℝ) ∧ (k n : ℝ) ≤ b * (N : ℝ) ∧
          ¬((∀ infrared : Bool,
            let Hused : BilateralField d → C(SpatialCoordinates d, ℝ) :=
              if infrared then H else 0
            (Reg model Hused alpha H1 pad Cfin hpad N (k n).toNat (z n) omega ∧
              Ext model Hused beta Aext N (k n).toNat (z n) omega) ∧
            (Reg model Hused alpha H1 pad Cfin hpad M (k n).toNat (z n) omega ∧
              Ext model Hused beta Aext M (k n).toNat (z n) omega)) ∧
            trace_close model H alpha eta N M (k n).toNat (z n) omega)} : ℝ) ≤
          theta * (N : ℝ) / (H1 : ℝ) :=
 by
  classical
  haveI instNeZeroDimension : NeZero d := ⟨by omega⟩
  have hH1pos : 0 < H1 := by omega
  have halpha0 : 1 / 2 < alpha := lt_trans hbeta hba
  let theta' : ℝ := min theta ((b - a) / 2)
  have hba' : 0 < b - a := sub_pos.2 hab
  have htheta' : 0 < theta' := lt_min htheta (by linarith)
  have hthetab : theta' < b - a := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hthetale : theta' ≤ theta := min_le_left _ _
  let B : ℝ := 2000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / theta'
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hbase : 0 < 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / theta' := by
    have : (0 : ℝ) < H1 := by exact_mod_cast hH1pos
    positivity
  have hB : B > 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / theta' := by
    dsimp only [B]
    calc 2000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / theta' =
          2 * (1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / theta') := by ring
      _ > 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / theta' := by linarith
  have hBpos : 0 < B := by linarith
  obtain ⟨Cfin, Aext, pad, deltaReg, sigmaReg, epsReg, hCfin, hAext, hpad, hpadle3, hdeltaReg, -, -,
      hRegExt⟩ :=
    aux_mfd_lem_finite_good_levels_regext_both_infrared d hd Jc Pc Xc Sf W Cp Step D Dbase alpha beta B
      hbeta hba halpha1 hBpos H1 hH1pos hH1
  obtain ⟨deltaTrace, hdeltaTrace, hTraceSup⟩ :=
    Paper.lfsgs_trace_witness d hd Jc Pc Xc Sf W Cp Step D hES Dbase alpha halpha0 halpha1 B hBpos
  refine ⟨Cfin, Aext, pad, min deltaReg deltaTrace, hpad, hCfin, hAext, hpadle3,
    lt_min hdeltaReg hdeltaTrace, ?_⟩
  intro model Rm Sreg It H hH hdelta zroot jroot eta heta
  have hdReg : model.delta ≤ deltaReg := hdelta.trans (min_le_left _ _)
  have hdTr : model.delta ≤ deltaTrace := hdelta.trans (min_le_right _ _)
  obtain ⟨m0, TraceClose, hTC, hTW⟩ := hTraceSup model Rm Sreg It H hH hdTr eta heta
  obtain ⟨Ceta, ceta, N0, hCeta, hceta, hmain⟩ :=
    finite_interval_packing_generic d hd a b theta' ha hab hb htheta' hthetab H1 hH1pos B hB model
      zroot jroot
      (fun N k z omega => ∀ infrared : Bool,
        let Hused : BilateralField d → C(SpatialCoordinates d, ℝ) :=
          if infrared then H else 0
        Reg model Hused alpha H1 pad Cfin hpad N k z omega ∧
          Ext model Hused beta Aext N k z omega)
      (fun N k zc hkN => hRegExt model Rm Sreg It H hH hdReg N k zc hkN) m0 TraceClose hTW
  refine ⟨Ceta, ceta, N0, hCeta, hceta, fun N M hN hNM => ?_⟩
  obtain ⟨-, Bad, hBadm, hBadp, hBad⟩ := hmain N M hN hNM
  refine ⟨Bad, hBadm, hBadp, fun omega hω w => ?_⟩
  have h1 := hBad omega hω w
  dsimp only at h1 ⊢
  have hH1r : (0 : ℝ) < H1 := by exact_mod_cast hH1pos
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [hTC, forall_and, and_assoc] at h1 ⊢
  exact h1.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hthetale hN0) hH1r.le)

end

end Paper
