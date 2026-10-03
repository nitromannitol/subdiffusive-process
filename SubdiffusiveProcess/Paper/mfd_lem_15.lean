module

public import SubdiffusiveProcess.Section9LiveRate.Exponents
public import SubdiffusiveProcess.Paper.lem_15

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Lane3

noncomputable section
namespace Paper

theorem aux_mfd_lem_15_uniform
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
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
            forget
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
                      8) * (j : ℝ))) := by
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
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / 8 * j0),
    by positivity, ?_⟩
  intro B hB S dir bd L delta hdelta hdelta1 Praw hG1 hG2 forget nu P H hHmeas hHconv kappa aN
    haN K hKm hKnn hgrowth N j hjN hmomK hmomR
  have hAB : ((4 * Cd * (max 1 r) ^ d * Cdel +
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
        (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb)) +
      2 * (C7 * C8) * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / 8 * j0)) * B =
      (4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) +
      2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / 8 * j0) := by ring
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha0 : 0 ≤ t * (t - (d : ℝ) + 1) / (t + 1) / 8 := by positivity
  have hrs : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hY0 : 0 ≤ (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 8) * (j : ℝ)) :=
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
    have hexp := SubdiffusiveProcess.Section9LiveRate.masking_decay_le_influence_decay (t * (t - (d : ℝ) + 1) / (t + 1)) hbpos.le j
    have hrw : ((3 : ℝ) ^ (-(j : ℝ))) ^ (3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) =
        (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
    rw [hrw]
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hKi : 0 ≤ 2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / 8 * j0) := by positivity
    calc (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ))
        ≤ (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 8) * (j : ℝ)) := by
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
      (t * (t - (d : ℝ) + 1) / (t + 1) / 8) j j0 hj.le hC7.le hC8.le hB
      hdelta.le hgam.le ha0
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hd0 : 0 ≤ delta := hdelta.le
    refine hnum.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hd0) hY0
    rw [hAB]; linarith

theorem mfd_lem_15
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f)
    (hfsupp : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hf0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0)
    (fL2 : DomainL2 (centeredCube z r hr))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (t p B : ℝ) (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ))
    (hp : 2 ≤ p) (hB : 0 ≤ B) (dirichlet : Bool) :
    let S := killedResponseSpace hP
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    ∃ C : ℝ, 0 < C ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
          (_G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
          (_G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw),
          let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
            forget
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
          ∀ (kappa : ℕ → ℝ), (∀ N, 0 < kappa N) →
          ∀ (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
            (∀ N omega,
              (aN N omega).val =ᵐ[volume.restrict
                (centeredCube z r hr : Set (SpatialCoordinates d))]
                (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
          let RN : ℕ → BilateralField d → ℝ :=
            fun N omega =>
              if dirichlet then
                dirichletResponse S (aN N omega) b
              else
                inverseResponse S (aN N omega) L
          let gN : ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
            fun N omega =>
              if dirichlet then
                sobolevGradient (dirichletMinimizer S (aN N omega) b).val
              else
                subspaceGradient S.space (responseSolution S (aN N omega) L)
          ∀ (K : ℕ → BilateralField d → ℝ),
            ((∀ N, AEStronglyMeasurable (K N) P) ∧
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega)) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (gN N omega) ≤ K N omega * rho ^ t) →
            (∀ N,
              MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
              MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
              eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B ∧
              eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
            ∀ (N j : ℕ), j ≤ N →
              eLpNorm
                (fun pair : BilateralField d × BilateralField d =>
                  RN N pair.1 -
                    RN N
                      (Function.update pair.1 (-(j : ℤ))
                        (pair.2 (-(j : ℤ)))))
                (ENNReal.ofReal p) (P.prod P) ≤
              ENNReal.ofReal
                (C * delta *
                  (3 : ℝ) ^
                  (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                      8) * (j : ℝ)))
    := by
  intro S L
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
  refine ⟨(4 * Cd * (max 1 r) ^ d * Cdel * B +
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
        (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) +
      2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / 8 * j0) + 1,
    by positivity, ?_⟩
  intro delta hdelta hdelta1 Praw hG1 hG2 forget nu P H hHmeas hHconv kappa _ aN haN RN gN K
    hKmn hgrowth hmom N j hjN
  obtain ⟨hKm, hKnn⟩ := hKmn
  have hmomN := hmom N
  obtain ⟨_, _, hmomK, hmomR⟩ := hmomN
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha0 : 0 ≤ t * (t - (d : ℝ) + 1) / (t + 1) / 8 := by positivity
  have hrs : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hY0 : 0 ≤ (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 8) * (j : ℝ)) :=
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
    have hmask := aux_lem_15_u_mask_case d hd z r hr S dirichlet b L t p B hp hB Cd hCd hbpos
      Cp hCp hCpall' _ Cdel Ca Cb Cc Ce hCdel.le hCa.le hCb.le hCc.le hCe.le delta hdelta
      hdelta1 Praw hG1 hG2 H hHmeas hHconv kappa aN haN K hKm hKnn hgrowth N j hjN hmomK
      hmomR _ rfl hgeom hM1 hM2 hM3 hM4 hM5 hM6
    refine hmask.trans (ENNReal.ofReal_le_ofReal ?_)
    have hexp := SubdiffusiveProcess.Section9LiveRate.masking_decay_le_influence_decay (t * (t - (d : ℝ) + 1) / (t + 1)) hbpos.le j
    have hrw : ((3 : ℝ) ^ (-(j : ℝ))) ^ (3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) =
        (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
    rw [hrw]
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hKi : 0 ≤ 2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / 8 * j0) := by positivity
    calc (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ))
        ≤ (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 8) * (j : ℝ)) := by
          gcongr
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hdelta.le) hY0
          linarith
  · -- initial scales
    push_neg at hj
    have hM7 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hL7 delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM8 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hL8 delta hdelta hdelta1 Praw hG1 hG2 j)
    simp only [pow_zero, one_mul, pow_one, Real.rpow_natCast, mul_one] at hM7 hM8
    have hinit := aux_lem_15_u_init_case d hd z r hr S dirichlet b L t p B hp delta hdelta
      hdelta1 Praw hG1 hG2 H hHmeas hHconv kappa aN haN K hKnn hgrowth N j hjN hmomR _ _
      (by positivity) (by positivity) hM7 hM8
    refine hinit.trans (ENNReal.ofReal_le_ofReal ?_)
    have hnum := aux_lem_15_u_init_numeric C7 C8 B delta
      (t * (t - (d : ℝ) + 1) / (t + 1) / 12)
      (t * (t - (d : ℝ) + 1) / (t + 1) / 8) j j0 hj.le hC7.le hC8.le hB
      hdelta.le hgam.le ha0
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hd0 : 0 ≤ delta := hdelta.le
    refine hnum.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hd0) hY0
    linarith

end Paper
