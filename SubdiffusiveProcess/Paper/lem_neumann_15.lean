module

public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Paper.lem_15
public import SubdiffusiveProcess.Paper.lem_neumann_error
public import SubdiffusiveProcess.Paper.prop_neumann_growth
public import SubdiffusiveProcess.Paper.neumann_centered_response

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section NeumannUniform
open Filter
open scoped Topology



theorem aux_lem_neumann_15_uniform
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (t p : ℝ) (ht_lower : (d : ℝ) - 1 < t) (hp : 2 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (B : ℝ), 0 ≤ B →
      ∀ (S : ResponseSpace (centeredCube z r hr)) (dir : Bool)
        (bd : weakSobolevGraph (centeredCube z r hr)) (L : S.space →L[ℝ] ℝ)
        (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
          (_G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
          (_G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw),
          let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map forget
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
          ∀ (kappa : ℕ → ℝ)
            (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
            (∀ N omega,
              (aN N omega).val =ᵐ[volume.restrict
                (centeredCube z r hr : Set (SpatialCoordinates d))]
                (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
          ∀ (K : ℕ → BilateralField d → ℝ),
            (∀ N, AEStronglyMeasurable (K N) P) →
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (aux_lem_15_u_grad S dir bd L (aN N omega)) ≤ K N omega * rho ^ t) →
            ∀ (N j : ℕ), j ≤ N →
            eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B →
            eLpNorm (fun omega => aux_lem_15_u_resp S dir bd L (aN N omega))
              (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B →
              eLpNorm
                (fun pair : BilateralField d × BilateralField d =>
                  aux_lem_15_u_resp S dir bd L (aN N pair.1) -
                    aux_lem_15_u_resp S dir bd L (aN N
                      (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ))))))
                (ENNReal.ofReal p) (P.prod P) ≤
              ENNReal.ofReal
                (A * B * delta *
                  (3 : ℝ) ^
                  (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                      (8 * Real.log 3)) * (j : ℝ))) := by
  have hd1 : 1 ≤ d := by omega
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  have hgeo := aux_lem_15_u_geom d hd1 (2 * Real.sqrt d) (by positivity)
  obtain ⟨Cd, hCd, hgeo⟩ := hgeo
  have hgeo2 := hgeo t ht_lower
  obtain ⟨hbpos, r0, hr0, _, hgeoR⟩ := hgeo2
  have hp0 : 0 < p := by linarith
  have hgam : 0 < t * (t - (d : ℝ) + 1) / (t + 1) / 12 := by positivity
  have hQne := aux_lem_15_u_Qt_nonempty z hr
  have hRt : 0 ≤ ‖z‖ + (r / 2 + 1) := by positivity
  have hQR := aux_lem_15_u_Qt_bound z r
  -- the uniform layer-moment bank
  have hLexp := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR p ((0 : ℕ) : ℝ) 2 _ hp0 (by norm_num) (by norm_num) hgam
  obtain ⟨Cexp, _, hLexp⟩ := hLexp
  have hLdel := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((1 : ℕ) : ℝ) 4 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Cdel, hCdel, hLdel⟩ := hLdel
  have hLa := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((0 : ℕ) : ℝ) 7 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Ca, hCa, hLa⟩ := hLa
  have hLb := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((1 : ℕ) : ℝ) 7 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Cb, hCb, hLb⟩ := hLb
  have hLc := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR 1 ((0 : ℕ) : ℝ) 8 _ (by norm_num) (by norm_num) (by norm_num) hgam
  obtain ⟨Cc, hCc, hLc⟩ := hLc
  have hLe := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR 1 ((2 : ℕ) : ℝ) 8 _ (by norm_num) (by norm_num) (by norm_num) hgam
  obtain ⟨Ce, hCe, hLe⟩ := hLe
  have hL7 := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (4 * p) ((1 : ℕ) : ℝ) 1 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨C7, hC7, hL7⟩ := hL7
  have hL8 := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (4 * p) ((0 : ℕ) : ℝ) 1 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨C8, hC8, hL8⟩ := hL8
  -- the Efron–Stein constant (BBLM, proved in `aux_lem_15_bblm`)
  have hIES := in_efron_stein aux_lem_15_bblm p hp
  obtain ⟨Cp, hCp, hCpall⟩ := hIES
  have hCpall' : ∀ (m : ℕ) (mu : Fin m → Measure C(SpatialCoordinates d, ℝ))
      [∀ i, IsProbabilityMeasure (mu i)], aux_lem_15_u_ESProp mu p Cp := by
    intro m mu _
    exact (hCpall m (fun _ => C(SpatialCoordinates d, ℝ)) mu).1
  -- the initial scales
  have hj0 := exists_pow_lt_of_lt_one hr0 (by norm_num : (1 / 3 : ℝ) < 1)
  obtain ⟨j0, hj0⟩ := hj0
  refine ⟨(4 * Cd * (max 1 r) ^ d * Cdel +
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
        (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb)) +
      2 * (C7 * C8) * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0),
    by positivity, ?_⟩
  intro B hB S dir bd L delta hdelta hdelta1 Praw hG1 hG2 forget nu P H hHmeas hHconv kappa aN
    haN K hKm hKnn hgrowth N j hjN hmomK hmomR
  have hAB : ((4 * Cd * (max 1 r) ^ d * Cdel +
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
        (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb)) +
      2 * (C7 * C8) * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0)) * B =
      (4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) +
      2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0) := by ring
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha0 : 0 ≤ t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) := by positivity
  have hrs : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hY0 : 0 ≤ (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  by_cases hj : j0 ≤ j
  · -- masking case
    have hrsr0 : (3 : ℝ) ^ (-(j : ℝ)) ≤ r0 := by
      have h1 : (3 : ℝ) ^ (-(j : ℝ)) = (1 / 3 : ℝ) ^ j := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
      rw [h1]
      exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj).trans hj0.le
    have hgeom := hgeoR z r hr _ hrs hrsr0
    have hM1 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLexp delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM2 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hLdel delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM3 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLa delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM4 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hLb delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM5 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLc delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM6 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 2
      (hLe delta hdelta hdelta1 Praw hG1 hG2 j)
    simp only [pow_zero, one_mul, pow_one, Real.rpow_natCast, ENNReal.ofReal_one,
      mul_one] at hM1 hM2 hM3 hM4 hM5 hM6
    have hmask := aux_lem_15_u_mask_case d hd z r hr S dir bd L t p B hp hB Cd hCd hbpos
      Cp hCp hCpall' _ Cdel Ca Cb Cc Ce hCdel.le hCa.le hCb.le hCc.le hCe.le delta hdelta
      hdelta1 Praw hG1 hG2 H hHmeas hHconv kappa aN haN K hKm hKnn hgrowth N j hjN hmomK
      hmomR _ rfl hgeom hM1 hM2 hM3 hM4 hM5 hM6
    refine hmask.trans (ENNReal.ofReal_le_ofReal ?_)
    have hexp := aux_lem_15_u_exponent (t * (t - (d : ℝ) + 1) / (t + 1)) hbpos.le j
    have hrw : ((3 : ℝ) ^ (-(j : ℝ))) ^ (3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) =
        (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
    rw [hrw]
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hKi : 0 ≤ 2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0) := by positivity
    calc (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ))
        ≤ (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) := by
          gcongr
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hdelta.le) hY0
          rw [hAB]; linarith
  · -- initial scales
    push_neg at hj
    have hM7 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hL7 delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM8 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hL8 delta hdelta hdelta1 Praw hG1 hG2 j)
    simp only [pow_zero, one_mul, pow_one, Real.rpow_natCast, mul_one] at hM7 hM8
    have hinit := aux_lem_15_u_init_case d hd z r hr S dir bd L t p B hp delta hdelta
      hdelta1 Praw hG1 hG2 H hHmeas hHconv kappa aN haN K hKnn hgrowth N j hjN hmomR _ _
      (by positivity) (by positivity) hM7 hM8
    refine hinit.trans (ENNReal.ofReal_le_ofReal ?_)
    have hnum := aux_lem_15_u_init_numeric C7 C8 B delta
      (t * (t - (d : ℝ) + 1) / (t + 1) / 12)
      (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) j j0 hj.le hC7.le hC8.le hB
      hdelta.le hgam.le ha0
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hd0 : 0 ≤ delta := hdelta.le
    refine hnum.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hd0) hY0
    rw [hAB]; linarith

/-- Local energy only sees the part of the set inside the domain. -/
theorem aux_lem_neumann_15_localEnergy_inter {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (hsΩ : MeasurableSet (s ∩ (Ω : Set (SpatialCoordinates d)))) (g : HilbertGradient Ω) :
    localGradientEnergy a hsΩ g = localGradientEnergy a hs g := by
  rw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.restrict_restrict hsΩ, Measure.restrict_restrict hs, Set.inter_assoc,
    Set.inter_self]

/-- The deterministic normalization of the actual cutoff coefficient. -/
def aux_lem_neumann_15_kappa {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) : ℝ :=
  SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
    Real.exp ((N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)

/-- The actual normalized cutoff coefficient is the exponential of the cutoff
potential minus a deterministic logarithmic normalization. -/
theorem aux_lem_neumann_15_coeff_ae {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (cutoffPositiveCoefficient M H omega N z hr).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))]
      (fun x => Real.exp (cutoffPotential H omega N x -
        Real.log (aux_lem_neumann_15_kappa M N))) := by
  have hcoe := @normalizedContinuousPositiveCoefficient_coeFn d (centeredCube z r hr)
    (closedCube z r hr) ⟨centeredCube_subset_closedCube z hr⟩
    (cutoffCoefficientCM M H omega N z hr) (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [hcoe, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
    with x hx hxQ
  have hval := hx hxQ
  unfold cutoffPositiveCoefficient
  rw [hval]
  change cutoffCoefficient M H omega N x / 1 = _
  have hah := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  unfold cutoffCoefficient aux_lem_neumann_15_kappa
  rw [div_one, Real.log_mul hah.ne' (Real.exp_pos _).ne', Real.log_exp,
    show cutoffPotential H omega N x -
        (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
          (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      (cutoffPotential H omega N x - (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) -
        Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) by ring,
    Real.exp_sub (cutoffPotential H omega N x - _), Real.exp_log hah]
  field_simp

end NeumannUniform



theorem lem_neumann_15 :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (rho : ℝ → ℝ),
    ContDiff ℝ ∞ rho →
    (∀ tau, 0 ≤ rho tau) →
    (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
    (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ),
      (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
          Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖),
      let Q := unitNeumannCube d
      let S := meanZeroResponseSpace hP
      let L0 : S.space →L[ℝ] ℝ :=
        (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph Q))
      ∀ (fL2 : ℝ → DomainL2 Q),
        (∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
          ((fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (Q : Set (SpatialCoordinates d))]
            faceBump rho pvec eps)) →
        let Leps : ℝ → S.space →L[ℝ] ℝ := fun eps =>
          (sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL
        ∀ (t p B : ℝ),
          ((d : ℝ) - 1 < t ∧ t < (d : ℝ) ∧ 2 ≤ p ∧ 0 ≤ B) →
          ∃ C : ℝ, 0 < C ∧
            ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
              (0 < M.delta ∧ M.delta ≤ 1) →
              ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
                InfraredCharacterization M H →
                let P : Measure (BilateralField d) :=
                  (chaosSampleLaw M).toMeasure
                let aN : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
                  cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
                let yN : ℕ → BilateralField d → ℝ := fun N om =>
                  inverseResponse S (aN N om) L0
                let yeps : ℝ → ℕ → BilateralField d → ℝ := fun eps N om =>
                  inverseResponse S (aN N om) (Leps eps)
                let ueps : ℝ → ℕ → BilateralField d → S.space := fun eps N om =>
                  responseSolution S (aN N om) (Leps eps)
                ∀ (K : ℕ → BilateralField d → ℝ),
                  (∀ N, AEStronglyMeasurable (K N) P) →
                  (∀ᵐ om ∂P, ∀ N, 0 ≤ K N om) →
                  (∀ᵐ om ∂P,
                    ∀ (N : ℕ) (eps : ℝ),
                      (0 < eps ∧ eps < 1 / 8) →
                      ∀ (x : SpatialCoordinates d) (rad : ℝ),
                        x ∈ Q → (0 < rad ∧ rad ≤ 1) →
                        localGradientEnergy (aN N om)
                            (s := Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d)))
                            (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                            (subspaceGradient S.space (ueps eps N om)) ≤
                          K N om * eps ^ (-2 : ℝ) * rad ^ t) →
                  (∀ N,
                    MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    MemLp (yeps eps N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (yeps eps N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N,
                    MemLp (yN N) (ENNReal.ofReal (4 * p)) P ∧
                      eLpNorm (yN N) (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    eLpNorm (fun om => yN N om - yeps eps N om)
                      (ENNReal.ofReal p) P ≤
                      ENNReal.ofReal (B * eps ^ (1 / 4 : ℝ))) →
                  ∀ (eps : ℝ), (0 < eps ∧ eps < 1 / 8) →
                    ∀ (N j : ℕ), j ≤ N →
                      eLpNorm
                        (fun pair : BilateralField d × BilateralField d =>
                          yeps eps N pair.1 -
                            yeps eps N
                              (Function.update pair.1 (-(j : ℤ))
                                (pair.2 (-(j : ℤ)))))
                        (ENNReal.ofReal p) (P.prod P) ≤
                        ENNReal.ofReal
                          (C * M.delta * eps ^ (-2 : ℝ) *
                            (3 : ℝ) ^
                              (-((t * (t - (d : ℝ) + 1) / (t + 1) /
                                (8 * Real.log 3)) * (j : ℝ)))) := by
  intro d hd _ _ rho _ _ _ _ pvec _ hP Q S L0 fL2 _ Leps t p B htpB
  obtain ⟨ht_lower, _, hp, hB⟩ := htpB
  obtain ⟨A, hA, hmain⟩ := aux_lem_neumann_15_uniform d hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
    t p ht_lower hp
  refine ⟨A * B + 1, by positivity, ?_⟩
  intro M hMdelta H hH P aN yN yeps ueps K hKm hKnn hgrowth hKmom hyeps _ _ eps heps N j hjN
  have hc1 : 1 ≤ eps ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos heps.1 (by linarith [heps.2]) (by norm_num)
  have hc0 : 0 ≤ eps ^ (-2 : ℝ) := zero_le_one.trans hc1
  have hK'm : ∀ N, AEStronglyMeasurable (fun om => K N om * eps ^ (-2 : ℝ)) P :=
    fun N => (hKm N).mul_const _
  have hK'nn : ∀ᵐ om ∂P, ∀ N, 0 ≤ K N om * eps ^ (-2 : ℝ) := by
    filter_upwards [hKnn] with om hom N
    exact mul_nonneg (hom N) hc0
  have hgrowth' : ∀ᵐ om ∂P, ∀ N, ∀ x ∈ (Q : Set (SpatialCoordinates d)),
      ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
        localGradientEnergy (aN N om)
          (s := Metric.ball x rad) Metric.isOpen_ball.measurableSet
          (aux_lem_15_u_grad S false 0 (Leps eps) (aN N om)) ≤
          K N om * eps ^ (-2 : ℝ) * rad ^ t := by
    filter_upwards [hgrowth] with om hom N x hx rad hrad0 hrad1
    have h := hom N eps heps x rad hx ⟨hrad0, hrad1⟩
    rw [aux_lem_neumann_15_localEnergy_inter (aN N om) Metric.isOpen_ball.measurableSet] at h
    exact h
  have hmomK : eLpNorm (fun om => K N om * eps ^ (-2 : ℝ)) (ENNReal.ofReal (3 * p)) P ≤
      ENNReal.ofReal (eps ^ (-2 : ℝ) * B) := by
    have hfun : (fun om => K N om * eps ^ (-2 : ℝ)) = eps ^ (-2 : ℝ) • K N := by
      funext om; simp [mul_comm]
    rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal hc0, ENNReal.ofReal_mul hc0]
    gcongr
    exact (hKmom N).2
  have hmomR : eLpNorm (fun om => aux_lem_15_u_resp S false 0 (Leps eps) (aN N om))
      (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal (eps ^ (-2 : ℝ) * B) := by
    refine ((hyeps N eps heps).2).trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith
  have hbound := hmain (eps ^ (-2 : ℝ) * B) (by positivity) S false 0 (Leps eps)
    M.delta hMdelta.1 hMdelta.2 M.P M.G1 M.G2 H hH.1 hH.2 (aux_lem_neumann_15_kappa M) aN
    (fun N om => aux_lem_neumann_15_coeff_ae M H om N _ one_pos)
    (fun N om => K N om * eps ^ (-2 : ℝ)) hK'm hK'nn hgrowth' N j hjN hmomK hmomR
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have hY : 0 ≤ (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  rw [show -((t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) =
      -(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ) by ring]
  have hdel : 0 ≤ M.delta := hMdelta.1.le
  have hkey : A * (eps ^ (-2 : ℝ) * B) ≤ (A * B + 1) * eps ^ (-2 : ℝ) := by
    nlinarith
  calc A * (eps ^ (-2 : ℝ) * B) * M.delta *
        (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ))
      ≤ (A * B + 1) * eps ^ (-2 : ℝ) * M.delta *
        (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) := by
        gcongr
    _ = (A * B + 1) * M.delta * eps ^ (-2 : ℝ) *
        (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) := by
        ring

end Paper
