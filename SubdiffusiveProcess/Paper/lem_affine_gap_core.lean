module

public import SubdiffusiveProcess.ResponseMoments.Forms
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.candidate_good_estimates
public import SubdiffusiveProcess.Paper.goodext_represented_local_trace
public import SubdiffusiveProcess.Paper.affine_comparison_poincare_event
public import SubdiffusiveProcess.Paper.inputs_classical_e4_cube_norms
public import SubdiffusiveProcess.Paper.lem_affine_gcn_competitor_l2
public import SubdiffusiveProcess.Paper.lem_affine_events
public import SubdiffusiveProcess.Paper.lem_affine_stmt_cge
public import SubdiffusiveProcess.Paper.lem_affine_gap_stmt
public import SubdiffusiveProcess.Paper.lem_affine_gap_model

@[expose] public section

/-! # The constants layer of the affine gap core (gamma-route)

`lem_affine_gap_core` is the closed form of `aux_lem_affine_gap_core_needs` of the installed `lem_affine`
with a scale threshold: for the fixed constants (`beta, alpha, gamma, zeta, rho, s, sigma, cell, cbuf, k0`) there is
`H0` such that for every `H1 ≥ H0` with `floor(gamma H1) + 6 < H1` (the gap facts of `lem_affine`) the constants
`epshom, Cbound, eps0, lam0, delta0` exist and the model-level statement `lem_affine_gap_stmt` holds.
The constants come from named suppliers only: `Cbound` from `candidate_good_estimates`, `Csharp/deltaSharp` from
`goodext_represented_local_trace`, `deltaPoinc` from `affine_comparison_poincare_event`, the growth threshold from
`lem_affine_events`, `Cin` from their combination (`Cin ≥ 3`), and `L0, eps0, src0` from
`lem_affine_gcn_competitor_l2` at `Lt = 3^H1 / 27^(1/gamma)`; `H0` is the exponent with `3^H0 > L0 * 27^(1/gamma)`. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

universe u

/-- Large `H1` makes the comparison scale `L / 27^(1/gamma)` exceed the threshold `L0`. -/
theorem aux_lem_affine_gap_core_scale (L0 gamma : ℝ) (n0 H1 : ℕ)
    (hn0 : L0 * (27 : ℝ) ^ (1 / gamma) < (3 : ℝ) ^ n0) (hH1 : n0 ≤ H1) (h27 : 0 < (27 : ℝ) ^ (1 / gamma)) :
    L0 ≤ (3 : ℝ) ^ H1 / (27 : ℝ) ^ (1 / gamma) := by
  rw [le_div_iff₀ h27]
  exact hn0.le.trans (pow_le_pow_right₀ (by norm_num) hH1)

/-- The affine gap core: constants, then the model-level statement (see the module docstring). -/
theorem lem_affine_gap_core
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d) (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (beta : ℝ) (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1)
    (alpha gamma zeta rho s sigma cell : ℝ)
    (hba : beta < alpha) (halpha : alpha < 1)
    (hgamma : 0 < gamma) (hgamma1 : gamma < 1) (hzeta : 0 < zeta) (hrho : 0 < rho)
    (hneg : affineExponent (d : ℝ) alpha beta gamma zeta < 0)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1) (cbuf k0 : ℕ) :
    ∃ H0 : ℕ, ∀ H1 : ℕ, H0 ≤ H1 → Nat.floor (gamma * (H1 : ℝ)) + 6 < H1 →
      ∃ epshom : ℝ, ∃ (_hepshom : 0 < epshom),
      ∃ Cbound eps0 lam0 delta0 : ℝ,
        (1 : ℝ) ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
        lem_affine_gap_stmt.{u} d hd I beta alpha gamma zeta rho s sigma cell cbuf k0 H1 epshom
          Cbound eps0 lam0 delta0 := by
  have hAlphaPos : 0 < alpha := lt_trans (by norm_num) (lt_trans hbeta hba)
  have hbetaI : beta ∈ Set.Ioo (1 / 2 : ℝ) 1 := ⟨hbeta, hbeta1⟩
  obtain ⟨Cbase, hCbase1, hCGEdata⟩ := candidate_good_estimates.{0} d hd I _X _Sob Pin
    _MeyersMorrey _Step D Cp alpha beta s sigma cell ⟨hAlphaPos, halpha⟩ hbetaI hs hsSmall
    hsigma_eq hsigma hcell
  obtain ⟨Csharp, deltaSharp, hCsharp, hdeltaSharp, hTrace⟩ :=
    goodext_represented_local_trace d hd I Pin _X _MeyersMorrey Cp _Sob
      (inputs_classical_e4_cube_norms d hd) ((d : ℝ) - 1 / 2) alpha beta (by linarith)
      (by linarith) hAlphaPos halpha hbetaI
  obtain ⟨deltaPoinc, hdeltaPoinc, hPoincEv⟩ :=
    affine_comparison_poincare_event d hd I Pin _X _MeyersMorrey Cp _Sob
      (inputs_classical_e4_cube_norms d hd) ((d : ℝ) - 1 / 2) alpha beta (by linarith)
      (by linarith) hAlphaPos halpha hbetaI
  obtain ⟨Cin, hCin1, hCinC, hCinE, hCinP, hCin3⟩ := aux_lem_affine_exists_Cin
    (Real.sqrt (d : ℝ) ^ alpha * (Cbase * (3 : ℝ) ^ (Cbase * ((k0 : ℝ) + (cbuf : ℝ)))))
    (Csharp * (2 * cell⁻¹))
    (729 * Real.sqrt (2 * (Pin.C ^ 2 * ((Homogenization.Book.Ch02.geometricDiscount s 2 /
      Homogenization.Book.Ch02.geometricDiscount 1 1) * (1 / 5 : ℝ))⁻¹)) *
      ((27 : ℝ) ^ (1 / gamma)) ^ (((d : ℝ) + zeta) / 2)) 3
  obtain ⟨L0, hL01, hGCN⟩ := lem_affine_gcn_competitor_l2 d hd alpha beta gamma zeta rho hbeta hba
    halpha hgamma hgamma1 hzeta hrho hneg Cin hCin1
  have h27 : (0 : ℝ) < (27 : ℝ) ^ (1 / gamma) := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨n0, hn0⟩ := pow_unbounded_of_one_lt (L0 * (27 : ℝ) ^ (1 / gamma))
    (by norm_num : (1 : ℝ) < 3)
  refine ⟨n0, fun H1 hH1 hfloor => ?_⟩
  obtain ⟨eps0G, heps0G, hGCN2⟩ := hGCN ((3 : ℝ) ^ H1 / (27 : ℝ) ^ (1 / gamma))
    (aux_lem_affine_gap_core_scale L0 gamma n0 H1 hn0 hH1 h27)
  obtain ⟨epshom, hepshom, hepshomG, hepshomHalf⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ eps0G ∧ e ≤ 1 / 2 :=
    ⟨min eps0G (1 / 2), lt_min heps0G (by norm_num), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨src0, hsrc0, hInst⟩ := hGCN2 epshom hepshom hepshomG
  obtain ⟨eps0, lam0, deltaCGE, heps0, hlam0, hdeltaCGE, hCGEinst⟩ :=
    hCGEdata epshom hepshom (by linarith only [hepshomHalf])
  obtain ⟨delta0, hdelta0, hd1, hd2, hd3, hd4⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ deltaCGE ∧ δ ≤ deltaSharp ∧
      δ ≤ deltaPoinc ∧ δ ≤ aux_lem_affine_events_growthDelta d hd I Pin _X _MeyersMorrey Cp _Sob beta
        ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hbeta, hbeta1⟩ :=
    ⟨min (min deltaCGE deltaSharp) (min deltaPoinc (aux_lem_affine_events_growthDelta d hd I Pin _X
      _MeyersMorrey Cp _Sob beta ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hbeta, hbeta1⟩)),
      lt_min (lt_min hdeltaCGE hdeltaSharp) (lt_min hdeltaPoinc
        (aux_lem_affine_events_growthDelta_pos d hd I Pin _X _MeyersMorrey Cp _Sob beta
          ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hbeta, hbeta1⟩)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  exact ⟨epshom, hepshom, Cbase, eps0, lam0, delta0, hCbase1, heps0, hlam0, hdelta0,
    lem_affine_gap_model d hd I _X _Sob _MeyersMorrey Pin Cp beta alpha gamma zeta rho s sigma cell
      cbuf k0 H1 epshom Cbase eps0 lam0 delta0 hbeta hbeta1 hba hgamma hs hsSmall hsigma_eq hsigma
      hcell hfloor hCbase1 hepshom hepshomHalf deltaCGE Csharp deltaSharp deltaPoinc Cin src0 hd1
      hd2 hd3 hd4 hCGEinst hTrace hPoincEv hCin1 hCin3 hCinC hCinE hCinP hsrc0 hInst⟩

end SubdiffusiveProcess.Paper
end
