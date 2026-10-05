module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_translated_two_branch_envelope
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_bank_family_tail
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_chart_response_transfer
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_retained_bank_algebra

@[expose] public section

open MeasureTheory Set Filter Metric
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper




/-- A comparison rate admits a strictly smaller retained fraction. -/
theorem aux_lem_as_coarse_shallow_grid_translated_cell_bridge_theta (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
      (d : ℝ) * theta < c * (1 - theta) / 2 := by
  let D : ℝ := 2 * ((d : ℝ) + c + 1)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨c / D, div_pos hc hD, ?_, ?_⟩
  · apply (div_lt_iff₀ hD).2
    dsimp [D]
    linarith
  · have hthetaD : (c / D) * D = c := div_mul_cancel₀ c (ne_of_gt hD)
    dsimp [D] at hthetaD ⊢
    nlinarith [mul_pos hc hc]

/-- The chart-transfer cell factor is the two-branch factor. -/
theorem aux_lem_as_coarse_shallow_grid_translated_cell_bridge_transfer_factor_eq {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)) (withIR : Bool) (N n : ℕ)
    (ω : BilateralField d) (y : SpatialCoordinates d) :
    Real.exp (sSup {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * ((3 : ℝ)^(-(n : ℤ)) / 2)),
        ∃ x' ∈ Metric.closedBall y (3 * ((3 : ℝ)^(-(n : ℤ)) / 2)),
          v = |((if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω +
                ∑ j ∈ Finset.range n, ω (-(j : ℤ))) x -
              ((if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω +
                ∑ j ∈ Finset.range n, ω (-(j : ℤ))) x'|}) *
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (((if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω +
            ∑ j ∈ Finset.range n, ω (-(j : ℤ))) y -
              (n : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (((if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω +
            ∑ j ∈ Finset.range n, ω (-(j : ℤ))) y -
              (n : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))⁻¹) =
    aux_lem_as_coarse_shallow_grid_two_branch_factor M Hir withIR N n ω y := by
  simp only [aux_lem_as_coarse_shallow_grid_two_branch_factor, ContinuousMap.add_apply,
    ContinuousMap.coe_sum, Finset.sum_apply]

/-- A retained finite bank coordinate outside the bad tail event is at most
`(1 + Cg + Ce)(1 + Z)`. -/
theorem aux_lem_as_coarse_shallow_grid_translated_cell_bridge_bank_le (F Z Cg Ce ce t : ℝ) (hZ : 0 ≤ Z) (hCg : 0 ≤ Cg) (hCe : 0 ≤ Ce)
    (ht : 0 ≤ t) (hce : 0 ≤ ce)
    (hgood : ¬(Cg * 1 * Z + Ce * (3 : ℝ) ^ (-(ce * t)) < |F - Z|)) :
    F ≤ (1 + Cg + Ce) * (1 + Z) := by
  have hle : |F - Z| ≤ Cg * 1 * Z + Ce * (3 : ℝ) ^ (-(ce * t)) := not_lt.mp hgood
  have hpow : (3 : ℝ) ^ (-(ce * t)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith)
  have hF : F - Z ≤ |F - Z| := le_abs_self _
  have hCe' : Ce * (3 : ℝ) ^ (-(ce * t)) ≤ Ce := by
    calc Ce * (3 : ℝ) ^ (-(ce * t)) ≤ Ce * 1 := mul_le_mul_of_nonneg_left hpow hCe
      _ = Ce := mul_one Ce
  nlinarith [mul_nonneg hCg hZ, mul_nonneg hCe hZ]



theorem lem_as_coarse_shallow_grid_translated_cell_bridge
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M) (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M Hir → M.delta ≤ delta0 →
      ∃ thetaP : ℝ, 0 < thetaP ∧ thetaP < 1 ∧
      ∀ (cen : ℕ → Finset (SpatialCoordinates d)) (Cc : ℝ),
        (∀ n : ℕ, ((cen n).card : ℝ) ≤ Cc * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ))) →
      ∀ (z : SpatialCoordinates d) (L : ℝ), (∀ n : ℕ, ∀ y ∈ cen n, dist y z ≤ L) →
      ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ,
        ∀ withIR : Bool,
          let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
            if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
          ∀ N : ℕ, N0 ≤ N → ∀ n : ℕ, n ≤ ⌊thetaP * (N : ℝ)⌋₊ → ∀ y ∈ cen n,
            coarseBMatrixNorm (originCube d 0)
                (Jc.chart y ((3 : ℝ)^(-(n : ℤ))) (by positivity)
                  (cutoffPositiveCoefficient M Hc ω N y (by positivity)) y
                  ((3 : ℝ)^(-(n : ℤ)))) +
              coarseSigmaStarInvMatrixNorm (originCube d 0)
                (Jc.chart y ((3 : ℝ)^(-(n : ℤ))) (by positivity)
                  (cutoffPositiveCoefficient M Hc ω N y (by positivity)) y
                  ((3 : ℝ)^(-(n : ℤ)))) ≤
              K * (3 : ℝ) ^ (rho * (n : ℝ)) := by
  classical
  -- moment order and envelope rate, chosen from `d, ρ` only
  let q : ℝ := 4 * (d : ℝ) / rho + 1
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hq : 1 ≤ q := by
    have : 0 ≤ 4 * (d : ℝ) / rho := div_nonneg (by positivity) hrho.le
    dsimp [q]; linarith
  have heta : 0 < rho / 2 := half_pos hrho
  have hetarho : rho / 2 < rho := half_lt_self hrho
  have hrate : (d : ℝ) < q * (rho - rho / 2) := by
    have hq' : q * (rho - rho / 2) = 2 * (d : ℝ) + rho / 2 := by
      dsimp [q]; field_simp; ring
    rw [hq']; linarith
  obtain ⟨δF, CF, hδF, hCF, hF⟩ :=
    lem_as_coarse_shallow_grid_actual_bank_family_tail d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp q hq
  obtain ⟨δE, hδE, hδE1, hE⟩ :=
    lem_as_coarse_shallow_grid_translated_two_branch_envelope d hd (Bool × Fin d) q (rho / 2) rho hq heta
      hetarho hrate
  refine ⟨min δF δE, lt_min hδF hδE, (min_le_right _ _).trans hδE1, ?_⟩
  intro M Rm Sreg It Hir HI hMd
  obtain ⟨Z, hZprops, hZtail⟩ := hF M Rm Sreg It Hir HI (hMd.trans (min_le_left _ _))
  choose Cg hCg hCgtail using hZtail
  have h1 : ∀ u : Bool × Fin d, ∃ Ce ce : ℝ, ∃ Ne : ℕ, 0 < Ce ∧ 0 < ce ∧
      ∀ N : ℕ, Ne ≤ N →
        (chaosSampleLaw M).toMeasure
          {om | Cg u.1 * 1 * Z (u.1, u.2) om +
            Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
            |aux_matched_affine_finite_response M (Pi.single u.2 1) u.1 N om -
              Z (u.1, u.2) om|} ≤
          ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) :=
    fun u => hCgtail u.1 u.2 1 one_pos
  choose Ce ce Ne hCe hce htl using h1
  -- common tail constants over the finite bank
  have huniv : (Finset.univ : Finset (Bool × Fin d)).Nonempty :=
    ⟨(false, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩), Finset.mem_univ _⟩
  let CgA : ℝ := Cg false + Cg true
  let CeA : ℝ := ∑ u : Bool × Fin d, Ce u
  let ceA : ℝ := (Finset.univ : Finset (Bool × Fin d)).inf' huniv ce
  let NeA : ℕ := ∑ u : Bool × Fin d, Ne u
  have hCgA0 : 0 ≤ CgA := by
    dsimp [CgA]; linarith [hCg false, hCg true]
  have hCgb : ∀ b, Cg b ≤ CgA := by
    intro b; cases b
    · dsimp [CgA]; linarith [hCg true]
    · dsimp [CgA]; linarith [hCg false]
  have hCeu : ∀ u, Ce u ≤ CeA := by
    intro u
    exact Finset.single_le_sum (fun v _ => (hCe v).le) (Finset.mem_univ u)
  have hCeA : 0 < CeA := lt_of_lt_of_le (hCe (false, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩))
    (hCeu _)
  have hceu : ∀ u, ceA ≤ ce u := fun u => Finset.inf'_le _ (Finset.mem_univ u)
  have hceA : 0 < ceA := by
    rw [Finset.lt_inf'_iff]
    intro u _
    exact hce u
  have hNeu : ∀ u, Ne u ≤ NeA := by
    intro u
    exact Finset.single_le_sum (fun v _ => Nat.zero_le _) (Finset.mem_univ u)
  have htailA : ∀ (b : Bool) (i : Fin d) (n : ℕ), NeA ≤ n →
      (chaosSampleLaw M).toMeasure
        {om | CgA * 1 * Z (b, i) om +
          CeA * (3 : ℝ) ^ (-(ceA * (n : ℝ))) <
          |aux_matched_affine_finite_response M (Pi.single i 1) b n om - Z (b, i) om|} ≤
        ENNReal.ofReal (CeA * (3 : ℝ) ^ (-(ceA * (n : ℝ)))) := by
    intro b i n hn
    have hpow : Ce (b, i) * (3 : ℝ) ^ (-(ce (b, i) * (n : ℝ))) ≤
        CeA * (3 : ℝ) ^ (-(ceA * (n : ℝ))) := by
      apply mul_le_mul (hCeu _) _ (by positivity) hCeA.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have := hceu (b, i)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    calc (chaosSampleLaw M).toMeasure
          {om | CgA * 1 * Z (b, i) om +
            CeA * (3 : ℝ) ^ (-(ceA * (n : ℝ))) <
            |aux_matched_affine_finite_response M (Pi.single i 1) b n om - Z (b, i) om|} ≤
        (chaosSampleLaw M).toMeasure
          {om | Cg b * 1 * Z (b, i) om +
            Ce (b, i) * (3 : ℝ) ^ (-(ce (b, i) * (n : ℝ))) <
            |aux_matched_affine_finite_response M (Pi.single i 1) b n om - Z (b, i) om|} := by
          apply measure_mono
          intro om hom
          simp only [mem_ofPred_eq] at hom ⊢
          have hZ0 := (hZprops b i).2.1 om
          have : Cg b * 1 * Z (b, i) om ≤ CgA * 1 * Z (b, i) om := by
            have := hCgb b
            nlinarith
          linarith
      _ ≤ ENNReal.ofReal (Ce (b, i) * (3 : ℝ) ^ (-(ce (b, i) * (n : ℝ)))) :=
          htl (b, i) n ((hNeu _).trans hn)
      _ ≤ ENNReal.ofReal (CeA * (3 : ℝ) ^ (-(ceA * (n : ℝ)))) :=
          ENNReal.ofReal_le_ofReal hpow
  obtain ⟨thetaP, hθ0, hθ1, hθsmall⟩ := aux_lem_as_coarse_shallow_grid_translated_cell_bridge_theta d ceA hceA
  refine ⟨thetaP, hθ0, hθ1, ?_⟩
  intro cen Cc hcard z L hL
  -- the bank moment constant and the two almost-sure events
  let C : ℝ := 2 * volume.real
    (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) *
      (CF + 1)
  have hC : 0 ≤ C := by
    dsimp [C]
    have : 0 ≤ volume.real
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) :=
      measureReal_nonneg
    positivity
  have hG := lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual M (fun b i => Z (b, i)) thetaP CgA CeA ceA 1
    NeA hθ0.le hθ1 hCeA hceA hθsmall htailA cen Cc hcard
  have hEnv := hE C hC M Rm Hir HI (hMd.trans (min_le_right _ _)) Z
    (fun u => (hZprops u.1 u.2).2.2.2.1) (fun u => (hZprops u.1 u.2).2.2.2.2)
    cen Cc hcard z L hL
  filter_upwards [hG, hEnv] with ω hGω hEω
  obtain ⟨KE, hKE1, hKE⟩ := hEω
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hGω
  have hKpos : 0 < 2 * (d : ℝ) * (1 + CgA + CeA) * KE := by
    have hdpos : (0 : ℝ) < d := by
      have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
      exact_mod_cast this
    have : 0 < 1 + CgA + CeA := by linarith
    positivity
  refine ⟨2 * (d : ℝ) * (1 + CgA + CeA) * KE, hKpos, N0, ?_⟩
  intro withIR Hc N hN n hn y hy
  have hnN : n ≤ N := by
    have h1 : (⌊thetaP * (N : ℝ)⌋₊ : ℝ) ≤ thetaP * (N : ℝ) :=
      Nat.floor_le (mul_nonneg hθ0.le (Nat.cast_nonneg N))
    have h2 : thetaP * (N : ℝ) ≤ N := mul_le_of_le_one_left (Nat.cast_nonneg N) hθ1.le
    have h3 : (n : ℝ) ≤ N := (Nat.cast_le.mpr hn).trans (h1.trans h2)
    exact_mod_cast h3
  have hgood := hN0 N hN n hn y hy
  have htr := lem_as_coarse_shallow_grid_chart_response_transfer Jc M Hc ω N n hnN y
  dsimp only at htr
  have hpowpos : 0 ≤ (3 : ℝ) ^ (rho * (n : ℝ)) := by positivity
  have hs : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - n) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp ((Hc ω + ∑ j ∈ Finset.range n, ω (-(j : ℤ))) y -
        (n : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) :=
    mul_pos (div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)) (Real.exp_pos _)
  have hfac := aux_lem_as_coarse_shallow_grid_translated_cell_bridge_transfer_factor_eq M Hir withIR N n ω y
  have hbank : ∀ (b : Bool) (i : Fin d),
      aux_matched_affine_finite_response M (Pi.single i 1) b (N - n)
          (aux_lem_as_coarse_shallow_grid_scaleShift n y ω) ≤
        (1 + CgA + CeA) * (1 + Z (b, i) (aux_lem_as_coarse_shallow_grid_scaleShift n y ω)) := by
    intro b i
    exact aux_lem_as_coarse_shallow_grid_translated_cell_bridge_bank_le _ _ CgA CeA ceA _ ((hZprops b i).2.1 _) hCgA0 hCeA.le
      (Nat.cast_nonneg _) hceA.le (hgood b i)
  have halg := lem_as_coarse_shallow_grid_retained_bank_algebra d _ _ (1 + CgA + CeA)
    (KE * (3 : ℝ) ^ (rho * (n : ℝ))) _ _ hs (by linarith)
    (fun i => aux_matched_affine_finite_response M (Pi.single i 1) false (N - n)
      (aux_lem_as_coarse_shallow_grid_scaleShift n y ω))
    (fun i => aux_matched_affine_finite_response M (Pi.single i 1) true (N - n)
      (aux_lem_as_coarse_shallow_grid_scaleShift n y ω))
    (fun i => Z (false, i) (aux_lem_as_coarse_shallow_grid_scaleShift n y ω))
    (fun i => Z (true, i) (aux_lem_as_coarse_shallow_grid_scaleShift n y ω))
    (fun i => (hZprops false i).2.1 _) (fun i => (hZprops true i).2.1 _)
    (fun i => hbank false i) (fun i => hbank true i)
    (fun i => by
      rw [hfac]
      exact hKE withIR N n hnN y hy (false, i))
    (fun i => by
      rw [hfac]
      exact hKE withIR N n hnN y hy (true, i))
    htr.1 htr.2
  calc _ ≤ 2 * (d : ℝ) * (1 + CgA + CeA) * (KE * (3 : ℝ) ^ (rho * (n : ℝ))) := halg
    _ = 2 * (d : ℝ) * (1 + CgA + CeA) * KE * (3 : ℝ) ^ (rho * (n : ℝ)) := by ring

end SubdiffusiveProcess.Paper
