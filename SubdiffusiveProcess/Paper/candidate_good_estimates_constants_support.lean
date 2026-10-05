module

public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.EstimateLimits
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.OneStepDatum
public import SubdiffusiveProcess.Paper.killed_continuous_boundary_zero
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.candidate_good_event
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.cor_energy_measures
public import SubdiffusiveProcess.Paper.candidate_good_estimates_trace_passage
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.in_deterministic
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.lem_primitive
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.WeakGraphMaxPrinciple
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import SubdiffusiveProcess.Paper.lem_prefix_limit
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input

public import SubdiffusiveProcess.Paper.candidate_good_estimates_finite_bank_support


@[expose] public section

/-! Uniform deterministic constants for the candidate trace proof. This module supplies thresholds and campanato constants before the approximation tolerance. It does not assert the candidate theorem. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff


noncomputable section
namespace SubdiffusiveProcess.Paper

section CgeConstantsStepSection
open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
attribute [local instance] Classical.propDecidable
/-- The deterministic window proof with its constants chosen before epshom.
Adapted from aux_in_deterministic_onestep_repaired_of_window: only the
unused tolerance binder is moved after the three existential constants. -/
theorem aux_candidate_good_estimates_constants_support_onestep_uniform
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hE0 : 0 < E0) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∃ eAn dAn : ℝ, 0 < eAn ∧ 0 < dAn ∧
      ∀ (epshom Cbound eps0 lam0 delta0 : ℝ), eps0 ≤ eAn → delta0 ≤ dAn →
        aux_in_deterministic_regularity_onestep d I alpha beta s sigma cell epshom
          Cbound eps0 lam0 delta0 h theta C2 := by
  obtain ⟨Cg, dg, hCg, hdg, hGST⟩ := in_deterministic_good_scale_transfer d I s hs hsSmall
  have hc0 : 0 < E0 / (2 * Cg) := by positivity
  have hcap : 0 < E0 / (4 * Cg) := by positivity
  have hr3 : (3 : ℝ) ^ (-alpha) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [halpha.1])
  have hden : 0 < 1 - (3 : ℝ) ^ (-alpha) := by linarith
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨C2, hC2def⟩ : ∃ C2 : ℝ, C2 = max (max (11 + (E0 / (2 * Cg))⁻¹) (2 * Ceps * Cg))
      (max (3 * Cdel / (1 - (3 : ℝ) ^ (-alpha))) (((d : ℝ) + 3) / Real.log 3)) := ⟨_, rfl⟩
  have hC2a : 11 + (E0 / (2 * Cg))⁻¹ ≤ C2 := by
    rw [hC2def]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hC2b : 2 * Ceps * Cg ≤ C2 := by
    rw [hC2def]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hC2c : 3 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C2 := by
    rw [hC2def]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hC2d : ((d : ℝ) + 3) / Real.log 3 ≤ C2 := by
    rw [hC2def]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hC20 : 0 ≤ C2 := (by positivity : (0 : ℝ) ≤ 11 + (E0 / (2 * Cg))⁻¹).trans hC2a
  obtain ⟨C3, hC3def⟩ : ∃ C3 : ℝ, C3 = max (max (9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2)
      (Ceps * 5 * (9 * (d : ℝ) / 2)))
      (max (9 * Cdel / (1 - (3 : ℝ) ^ (-alpha))) ((2 * (d : ℝ) + 4) / Real.log 3)) := ⟨_, rfl⟩
  have hC3card : 9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2 ≤ C3 := by
    rw [hC3def]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hC3eps : Ceps * 5 * (9 * (d : ℝ) / 2) ≤ C3 := by
    rw [hC3def]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hC3a : 9 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C3 := by
    rw [hC3def]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hC3b : (2 * (d : ℝ) + 4) / Real.log 3 ≤ C3 := by
    rw [hC3def]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hC30 : 0 ≤ C3 := (by
    have : (0 : ℝ) < min 1 (E0 / 5) := lt_min one_pos (by positivity)
    positivity : (0 : ℝ) ≤ 9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2).trans hC3card
  refine ⟨C2 + C3 + 0, by linarith, min 1 (E0 / (4 * Cg)), min (min 1 dg) (E0 / (4 * Cg)),
    lt_min one_pos hcap, lt_min (lt_min one_pos hdg) hcap, ?_⟩
  intro epshom Cbound eps0 lam0 delta0 heps0 hdelta0
  have hCsub : (0 : ℝ) ≤ 0 := le_rfl
  intro cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth cword cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ
    Q q qp Ctotal psource N hkkN hcmp harmonicComparison traceEstimate
  have hkN : k ≤ N := by omega
  have hdel0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hdel1 : M.delta ≤ 1 :=
    hdisorder.trans (hdelta0.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hdelg : M.delta ≤ dg :=
    hdisorder.trans (hdelta0.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hdelc : M.delta ≤ E0 / (4 * Cg) := hdisorder.trans (hdelta0.trans (min_le_right _ _))
  have hepsc : eps ≤ E0 / (4 * Cg) := hepsSmall.trans (heps0.trans (min_le_right _ _))
  have hcapE : Cg * (M.delta ^ 2 + eps ^ 8) + Cg * (E0 / (2 * Cg)) ≤ E0 := by
    have h1 : M.delta ^ 2 ≤ E0 / (4 * Cg) := by nlinarith
    have h2 : eps ^ 8 ≤ E0 / (4 * Cg) := by
      have : eps ^ 8 ≤ eps := by
        calc eps ^ 8 ≤ eps ^ 1 := pow_le_pow_of_le_one heps.1.le heps.2.le (by norm_num)
          _ = eps := pow_one eps
      linarith
    have h3 : Cg * (M.delta ^ 2 + eps ^ 8) ≤ Cg * (2 * (E0 / (4 * Cg))) :=
      mul_le_mul_of_nonneg_left (by linarith) hCg.le
    have h4 : Cg * (2 * (E0 / (4 * Cg))) + Cg * (E0 / (2 * Cg)) = E0 := by
      field_simp; ring
    linarith
  have hG_ae := hGST M H hMH hdelg eps heps eta F Praw Rraw Draw Z rawGood hEta hPrimitive sN hsN
  have hrl : rootLevel qRoot = (k : ℤ) := by rw [hqRoot, hrootLevel, hfactor]; simp
  have hrs : rootSide qRoot = qside := by rw [hrootSide, hrl, hqside]
  have hrc : rootCentre qRoot = qcenter := by
    rw [hqRoot, hrootCentre, hshift, smul_zero, add_zero]
  have h3q : (3 : ℝ) ^ ((1 : ℤ) - k) / 2 = 3 * qside / 2 := by
    rw [hqside, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one, _root_.zpow_neg]; ring
  have hqp : Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
    rw [h3q]
    exact aux_in_deterministic_regularity_qp_subset k qside hqside qcenter Enl Shift
      selfShift padE factor hpad shift hshift rootLevel hrootLevel rootSide hrootSide rootCentre
      hrootCentre rootPos Qcentre Qside hQside hRootsQ
  have hlam0 : 0 ≤ lambdaCut := hThresholds.1.le
  have hlamlt : lambdaCut ≤ lambdaDet := (hThresholds.2.1.trans hThresholds.2.2.1).le
  have hobs : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1),
      observationCentre qRoot DA (Sum.inl dword) = descendantCenter 1 qcenter qside DA dword := by
    intro DA dword
    rw [hObservationCentre]; simp only [Sum.elim_inl]; rw [hrc, hrs]
  have hsk : sN N (k : ℤ) qcenter = fun omega =>
      aux_in_deterministic_onestep_sref M H omega N k qcenter := by
    funext omega; rw [hsN, ite_eq_left (by exact_mod_cast hkN)]; rfl
  filter_upwards [hEta, hPrimitive, hFiniteScoreGuard, hMH.2, hG_ae] with
    omega hEtaomega hPomega hFinomega hIRomega hGomega
  intro horizon hev hb f hf fL2 hfL2 fNorm u hu U hU huU D hD1 hDh x hx
  have hG' : ∀ (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
      Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega ≠ ⊤ →
      Z N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega N j w) s 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega).toReal) := by
    intro j w hj hD hZ
    have := hGomega N j w hj hD hZ
    rw [hsN, ite_eq_left hj] at this
    exact this
  have hpreAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k0 ≤ DA → DA ≤ horizon →
      k + DA ≤ N →
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          Z N ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) omega < lambdaCut * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          (Draw N ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) omega).toReal <
        lambdaCut * DA := by
    intro DA dword hk0 hDAh hkDA
    have hlev : rootLevel qRoot + (DA : ℤ) ≤ (N : ℤ) := by rw [hrl]; omega
    obtain ⟨hZp, hDp⟩ := hev.1 qRoot DA hk0 hDAh hlev (Sum.inl dword)
    rw [hPrefixZ, ite_eq_left hlev, hobs, hrl] at hZp
    rw [hPrefixD, ite_eq_left hlev, hobs, hrl] at hDp
    constructor
    · refine lt_of_eq_of_lt ?_ hZp
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [ite_eq_left (by omega)]
    · refine lt_of_eq_of_lt ?_ hDp
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [ite_eq_left (by omega)]
  have hfinAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k + DA ≤ N →
      ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
        Draw N ((N : ℤ) - l).toNat
          (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) omega ≠ ⊤ := by
    intro DA dword hkDA l hl
    have hlev : rootLevel qRoot + (DA : ℤ) ≤ (N : ℤ) := by rw [hrl]; omega
    have := hFinomega N qRoot DA (Sum.inl dword) hlev l (by rw [hrl]; exact hl)
    rwa [hobs] at this
  have hfN : 0 ≤ fNorm qp := div_nonneg ENNReal.toReal_nonneg
    (Real.rpow_nonneg measureReal_nonneg _)
  have hFq : (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal =
      fNorm qp * ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))) := by
    rw [h3q]
    show _ = (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
        (volume.restrict (Metric.ball qcenter (3 * qside / 2)))).toReal /
        (volume.real (Metric.ball qcenter (3 * qside / 2))) ^ (1 / ((d : ℝ) / (1 - alpha))) *
        ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha)))
    rw [aux_in_deterministic_onestep_volume_qp qcenter qside hqpos]
    have hpos : 0 < ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))) := by positivity
    rw [div_mul_cancel₀ _ hpos.ne']
  have hpadAll : k0 ≤ N - k → N - k + 1 ≤ horizon →
      ∀ pword : Fin (N - k + 1) → OddGridIndex d 1,
      Draw N 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) omega ≠ ⊤ ∧
      (Draw N 0 (((3 : ℝ) ^ N) •
        descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) omega).toReal ≤
        lambdaCut * ((N - k + 1 : ℕ) : ℝ) := by
    intro hreg hDph pword
    have hrlp : rootLevel (padE, selfShift) = (k : ℤ) - 1 := by
      rw [hrootLevel, hpad]; push_cast; ring
    have hrsp : rootSide (padE, selfShift) = 3 * qside := by
      rw [hrootSide, hrlp, hqside, show -((k : ℤ) - 1) = 1 + -(k : ℤ) by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    have hrcp : rootCentre (padE, selfShift) = qcenter := by
      rw [hrootCentre, hshift, smul_zero, add_zero]
    have hobsp : observationCentre (padE, selfShift) (N - k + 1) (Sum.inl pword) =
        descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword := by
      rw [hObservationCentre]; simp only [Sum.elim_inl]; rw [hrcp, hrsp]
    have hlevp : rootLevel (padE, selfShift) + ((N - k + 1 : ℕ) : ℤ) ≤ (N : ℤ) := by
      rw [hrlp]; omega
    obtain ⟨_, hDp⟩ := hev.1 (padE, selfShift) (N - k + 1) (by omega) hDph hlevp (Sum.inl pword)
    rw [hPrefixD, ite_eq_left hlevp, hobsp, hrlp] at hDp
    have hNmem : (N : ℤ) ∈ Finset.Icc ((k : ℤ) - 1 - (cbuf : ℤ))
        ((k : ℤ) - 1 + ((N - k + 1 : ℕ) : ℤ)) := by
      rw [Finset.mem_Icc]; constructor <;> omega
    have hfinp := hFinomega N (padE, selfShift) (N - k + 1) (Sum.inl pword) hlevp (N : ℤ)
      (by rw [hrlp]; exact hNmem)
    rw [hobsp, sub_self, Int.toNat_zero] at hfinp
    refine ⟨hfinp, ?_⟩
    have hterm := Finset.single_le_sum (f := fun j : ℤ => if 0 ≤ (N : ℤ) - j then
        (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) •
          descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) omega).toReal else 0)
      (fun j _ => by
        show 0 ≤ (if 0 ≤ (N : ℤ) - j then _ else 0)
        split_ifs
        · exact ENNReal.toReal_nonneg
        · exact le_rfl) hNmem
    simp only [sub_self, le_refl, ite_true, Int.toNat_zero] at hterm
    exact hterm.trans hDp.le
  exact aux_in_deterministic_onestep_at_point2 d I alpha s halpha hs h theta Ceps Cdel E0
    hCeps hCdel hOS Cg (E0 / (2 * Cg)) C2 0 hCg.le hc0 hC20 hC2a hC2b hC2c hC2d hCsub
    C3 hE0 hC3card hC3eps hC3a hC3b
    M H omega N (eta N omega) (hEtaomega N) hIRomega eps heps
    (fun m y => F N m y omega) (fun m y => Praw N m y omega) (fun m y => Rraw N m y omega)
    (fun m y => Draw N m y omega) (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)
    (hPomega N) hG' hcapE hdel0 hdel1 k cbuf k0 horizon hkN qside hqpos hqside qcenter
    lambdaCut lambdaDet hlam0 hlamlt hpreAll hfinAll Qcentre Qside hQside hqp f hf fL2 hfL2
    u hu U hU huU (sN N (k : ℤ) qcenter omega) (fNorm qp) (by rw [hsk]) hfN hFq hpadAll D hDh x hx
    (fun _ hc' => absurd hc' (by omega))


end CgeConstantsStepSection

section CgeConstantsSection
open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
/-- Select a uniform Campanato constant and approximation caps from the deterministic one-step supplier. -/
theorem aux_candidate_good_estimates_constants_support_camp_uniform
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hh : 0 < h) (htheta : theta ∈ Set.Ioo (0 : ℝ) 1)
    (hthetah : theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5))
    (hE0 : 0 < E0) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∃ eAn dAn : ℝ, 0 < eAn ∧ 0 < dAn ∧
      ∀ (epshom Cbound eps0 lam0 delta0 : ℝ), eps0 ≤ eAn → delta0 ≤ dAn →
        aux_in_deterministic_regularity_camp d I alpha beta s sigma cell epshom
          Cbound eps0 lam0 delta0 C1 := by
  obtain ⟨Cit, hCit, hcamp⟩ := aux_in_deterministic_regularity_camp_of_onestep d
  obtain ⟨C2, hC2, eAn, dAn, heAn, hdAn, hone⟩ :=
    aux_candidate_good_estimates_constants_support_onestep_uniform d I alpha beta s sigma cell halpha hs
      hsSmall h theta Ceps Cdel E0 hE0 hCeps hCdel hOS
  exact ⟨aux_in_deterministic_regularity_campConst d Cit h C2,
    aux_in_deterministic_regularity_campConst_nonneg d Cit h C2, eAn, dAn, heAn, hdAn,
    fun epshom Cbound eps0 lam0 delta0 he hd => hcamp I alpha beta s sigma cell epshom Cbound eps0 lam0
      delta0 h theta C2 hh htheta hthetah hC2 (hone epshom Cbound eps0 lam0 delta0 he hd)⟩


/-- The R1 and R2 windows admit one constant uniform in the homogeneity tolerance. -/
theorem aux_candidate_good_estimates_constants_support_R12_uniform_windows
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hh : 0 < h) (htheta : theta ∈ Set.Ioo (0 : ℝ) 1)
    (hthetah : theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5))
    (hE0 : 0 < E0) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (Charm Eh : ℝ) (hCharm : 0 ≤ Charm) (hEh : 0 < Eh)
    (hHW : aux_in_deterministic_core_harm_window d I alpha s Charm Eh) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ Cbound : ℝ, C1 ≤ Cbound →
      ∀ epshom : ℝ, 0 < epshom → epshom ≤ 1 →
      ∃ e1 l1 d1 : ℝ, 0 < e1 ∧ 0 < l1 ∧ 0 < d1 ∧
      ∀ eps0 lam0 delta0 : ℝ, 0 < eps0 → eps0 ≤ e1 → 0 < lam0 → lam0 ≤ l1 →
        0 < delta0 → delta0 ≤ d1 →
        aux_in_deterministic_regularity_R1 d I alpha beta s sigma cell epshom
          Cbound eps0 lam0 delta0 ∧
        aux_in_deterministic_regularity_R2 d I alpha beta s sigma cell epshom
          Cbound eps0 lam0 delta0 := by
  obtain ⟨Cc, hCc, eAn, dAn, heAn, hdAn, hcamp⟩ :=
    aux_candidate_good_estimates_constants_support_camp_uniform d I alpha beta s sigma cell halpha hs hsSmall
      h theta Ceps Cdel E0 hh htheta hthetah hE0 hCeps hCdel hOS
  set Ch := aux_in_deterministic_regularity_holderConst d alpha with hChdef
  have hCh0 : 0 ≤ Ch := aux_in_deterministic_regularity_holderConst_nonneg d halpha.1
  refine ⟨max 1 (max Cc (max (2 * Ch * Cc) (max Charm (1 / Eh)))), le_max_left _ _,
    fun Cbound hCb epshom hepshom hepshom_le => ?_⟩
  have hb1 : Cc ≤ Cbound := ((le_max_left _ _).trans (le_max_right _ _)).trans hCb
  have hb2 : 2 * Ch * Cc ≤ Cbound :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hCb
  have hb3 : Charm ≤ Cbound :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hCb
  have hb4a : 1 / Eh ≤ Cbound :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hCb
  have hb4 : epshom / Eh ≤ Cbound :=
    (div_le_div_of_nonneg_right hepshom_le hEh.le).trans hb4a
  refine ⟨eAn, 1, dAn, heAn, one_pos, hdAn, fun eps0 lam0 delta0 _ he0 _ _ _ hd0 => ?_⟩
  have hcore := aux_in_deterministic_regularity_core_of_parts d I alpha beta s sigma cell epshom
    Cbound eps0 lam0 delta0 Cc
    (aux_in_deterministic_regularity_cont_of_mem_Ioo d hd I alpha beta s sigma cell epshom
      Cbound eps0 lam0 delta0 halpha)
    (hcamp epshom Cbound eps0 lam0 delta0 he0 hd0)
    (aux_in_deterministic_core_harm_of_window d I alpha beta s sigma cell epshom hepshom
      Charm Eh hCharm hEh hHW Cbound eps0 lam0 delta0 hb3 hb4)
  exact ⟨aux_in_deterministic_regularity_R1_of_core d I alpha beta s sigma cell epshom
      Cbound eps0 lam0 delta0 Cc hCc hb1 hcore,
    aux_in_deterministic_regularity_R2_of_core d I alpha beta s sigma cell epshom
      Cbound eps0 lam0 delta0 halpha Cc hCc hb1 hb2 hcore⟩

/-- The actual deterministic suppliers with the candidate's constant order:
the large regularity constant is independent of the approximation tolerance. -/
theorem aux_candidate_good_estimates_constants_support_R12_uniform
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
    (alpha beta s sigma cell : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ)) :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ Cbound : ℝ, C1 ≤ Cbound →
      ∀ epshom : ℝ, 0 < epshom → epshom ≤ 1 →
      ∃ e1 l1 d1 : ℝ, 0 < e1 ∧ 0 < l1 ∧ 0 < d1 ∧
      ∀ eps0 lam0 delta0 : ℝ, 0 < eps0 → eps0 ≤ e1 → 0 < lam0 → lam0 ≤ l1 →
        0 < delta0 → delta0 ≤ d1 →
        aux_in_deterministic_R1 d I alpha beta s sigma cell epshom
          Cbound eps0 lam0 delta0 ∧
        aux_in_deterministic_R2 d I alpha beta s sigma cell epshom
          Cbound eps0 lam0 delta0 := by
  obtain ⟨h, theta, Ceps, Cdel, E0, hh, htheta, hthetah, hE0, hCeps, hCdel, hOS⟩ :=
    aux_in_deterministic_core_onestep_window_holds d hd I D alpha s halpha hs hsSmall
  obtain ⟨Charm, Eh, hCharm, hEh, hHW⟩ :=
    aux_in_deterministic_core_harm_window_holds d hd I D alpha s halpha hs hsSmall
  exact aux_candidate_good_estimates_constants_support_R12_uniform_windows d hd I alpha beta s sigma cell
    halpha hs hsSmall h theta Ceps Cdel E0 hh htheta hthetah hE0 hCeps hCdel hOS
    Charm Eh hCharm hEh hHW


end CgeConstantsSection

/-- The fixed Campanato constant and all trace coercivity constants are selected before the homogeneity tolerance. -/
theorem candidate_good_estimates_constants_support
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
    (Cg : ℝ) (_hCg : 0 < Cg)
    (alpha beta s sigma cell : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Cbound Ccamp : ℝ,
      1 ≤ Cbound ∧ Cg ≤ Cbound ∧ Cbound⁻¹ ≤ cell ∧ cell⁻¹ ≤ Cbound ∧
      (d : ℝ) ≤ Cbound * cell ^ 2 ∧
      0 ≤ Ccamp ∧ Ccamp ≤ Cbound ∧
      2 * aux_in_deterministic_regularity_holderConst d alpha * Ccamp ≤ Cbound ∧
      ∀ (epshom : ℝ) (_hepshom : 0 < epshom), epshom ≤ 1 →
        ∃ eps0 lam0 delta0 : ℝ,
          0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
          ∀ eps' lam' delta' : ℝ, 0 < eps' → eps' ≤ eps0 →
            0 < lam' → lam' ≤ lam0 → 0 < delta' → delta' ≤ delta0 →
            aux_in_deterministic_regularity_R1 d I alpha beta s sigma cell epshom
              Cbound eps' lam' delta' ∧
            aux_in_deterministic_regularity_camp d I alpha beta s sigma cell epshom
              Cbound eps' lam' delta' Ccamp ∧
            aux_in_deterministic_regularity_camp d I alpha beta s sigma cell (2 * epshom)
              Cbound eps' lam' delta' Ccamp := by
  obtain ⟨h, theta, Ceps, Cdel, E0, hh, htheta, hthetah, hE0, hCeps, hCdel, hOS⟩ :=
    aux_in_deterministic_core_onestep_window_holds d hd I D alpha s halpha hs hsSmall
  obtain ⟨Cc, hCc, eAn, dAn, heAn, hdAn, hcamp⟩ :=
    aux_candidate_good_estimates_constants_support_camp_uniform d I alpha beta s sigma cell halpha hs hsSmall
      h theta Ceps Cdel E0 hh htheta hthetah hE0 hCeps hCdel hOS
  obtain ⟨Charm, Eh, hCharm, hEh, hHW⟩ :=
    aux_in_deterministic_core_harm_window_holds d hd I D alpha s halpha hs hsSmall
  obtain ⟨Cdet, hCdet, hR12⟩ :=
    aux_candidate_good_estimates_constants_support_R12_uniform_windows d hd I alpha beta s sigma cell halpha hs hsSmall
      h theta Ceps Cdel E0 hh htheta hthetah hE0 hCeps hCdel hOS Charm Eh hCharm hEh hHW
  let Ch := aux_in_deterministic_regularity_holderConst d alpha
  let Cbase := max 1 (max Cdet (max Cc (max (2 * Ch * Cc) (max Charm (2 / Eh)))))
  let Cbound := max Cg (max Cbase (max cell⁻¹ ((d : ℝ) / cell ^ 2)))
  have hCbase : Cbase ≤ Cbound := by
    calc
      Cbase ≤ max Cbase (max cell⁻¹ ((d : ℝ) / cell ^ 2)) := le_max_left _ _
      _ ≤ Cbound := le_max_right _ _
  have hCdet' : Cdet ≤ Cbound := by
    calc
      Cdet ≤ max Cdet (max Cc (max (2 * Ch * Cc) (max Charm (2 / Eh)))) := le_max_left _ _
      _ ≤ Cbase := le_max_right _ _
      _ ≤ Cbound := hCbase
  have hCcamp : Cc ≤ Cbound := by
    calc
      Cc ≤ max Cc (max (2 * Ch * Cc) (max Charm (2 / Eh))) := le_max_left _ _
      _ ≤ max Cdet (max Cc (max (2 * Ch * Cc) (max Charm (2 / Eh)))) := le_max_right _ _
      _ ≤ Cbase := le_max_right _ _
      _ ≤ Cbound := hCbase
  have hCcampHolder : 2 * Ch * Cc ≤ Cbound := by
    calc
      2 * Ch * Cc ≤ max (2 * Ch * Cc) (max Charm (2 / Eh)) := le_max_left _ _
      _ ≤ max Cc (max (2 * Ch * Cc) (max Charm (2 / Eh))) := le_max_right _ _
      _ ≤ max Cdet (max Cc (max (2 * Ch * Cc) (max Charm (2 / Eh)))) := le_max_right _ _
      _ ≤ Cbase := le_max_right _ _
      _ ≤ Cbound := hCbase
  have hCcell : cell⁻¹ ≤ Cbound := by
    calc
      cell⁻¹ ≤ max cell⁻¹ ((d : ℝ) / cell ^ 2) := le_max_left _ _
      _ ≤ max Cbase (max cell⁻¹ ((d : ℝ) / cell ^ 2)) := le_max_right _ _
      _ ≤ Cbound := le_max_right _ _
  have hCdim' : (d : ℝ) / cell ^ 2 ≤ Cbound := by
    calc
      (d : ℝ) / cell ^ 2 ≤ max cell⁻¹ ((d : ℝ) / cell ^ 2) := le_max_right _ _
      _ ≤ max Cbase (max cell⁻¹ ((d : ℝ) / cell ^ 2)) := le_max_right _ _
      _ ≤ Cbound := le_max_right _ _
  have hCbound : 1 ≤ Cbound := by
    calc
      1 ≤ Cbase := le_max_left _ _
      _ ≤ max Cbase (max cell⁻¹ ((d : ℝ) / cell ^ 2)) := le_max_left _ _
      _ ≤ Cbound := le_max_right _ _
  have hCgC : Cg ≤ Cbound := le_max_left _ _
  have hCbound_pos : 0 < Cbound := lt_of_lt_of_le zero_lt_one hCbound
  have hprod : 1 ≤ cell * Cbound := by
    have hinv : 1 / cell ≤ Cbound := by simpa only [one_div] using hCcell
    have hp := (div_le_iff₀ hcell.1).1 hinv
    simpa only [mul_comm] using hp
  have hClo : Cbound⁻¹ ≤ cell := by
    have hp : 1 / Cbound ≤ cell := (div_le_iff₀ hCbound_pos).2 hprod
    simpa only [one_div] using hp
  have hcellSq : 0 < cell ^ 2 := sq_pos_of_pos hcell.1
  have hCdim : (d : ℝ) ≤ Cbound * cell ^ 2 := by
    calc
      (d : ℝ) = ((d : ℝ) / cell ^ 2) * cell ^ 2 := by
        symm
        exact div_mul_cancel₀ _ hcellSq.ne'
      _ ≤ Cbound * cell ^ 2 := mul_le_mul_of_nonneg_right hCdim' (sq_nonneg cell)
  refine ⟨Cbound, Cc, hCbound, hCgC, hClo, hCcell, hCdim, hCc,
    hCcamp, hCcampHolder, ?_⟩
  intro epshom hepshom hepshom_le
  obtain ⟨e1, l1, d1, he1, hl1, hd1, hR12caps⟩ :=
    hR12 Cbound hCdet' epshom hepshom hepshom_le
  refine ⟨min e1 eAn, min l1 1, min d1 dAn,
    lt_min he1 heAn, lt_min hl1 one_pos, lt_min hd1 hdAn, ?_⟩
  intro eps' lam' delta' heps' heps'le hlam' hlam'le hdelta' hdelta'le
  have hR1R2 := hR12caps eps' lam' delta' heps'
    (heps'le.trans (min_le_left _ _)) hlam' (hlam'le.trans (min_le_left _ _))
    hdelta' (hdelta'le.trans (min_le_left _ _))
  have hcamp' := hcamp epshom Cbound eps' lam' delta'
    (heps'le.trans (min_le_right _ _)) (hdelta'le.trans (min_le_right _ _))
  have hcampWide := hcamp (2 * epshom) Cbound eps' lam' delta'
    (heps'le.trans (min_le_right _ _)) (hdelta'le.trans (min_le_right _ _))
  exact ⟨hR1R2.1, hcamp', hcampWide⟩

end SubdiffusiveProcess.Paper
end
