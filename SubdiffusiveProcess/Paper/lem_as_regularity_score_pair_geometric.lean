module

public import SubdiffusiveProcess.Paper.lem_as_regularity_score_pair_rate
public import SubdiffusiveProcess.Analysis.InitialLayerDecay

@[expose] public section

/-! The explicit score comparison has two geometric errors after absorbing
its affine initial-layer cost. The retained-depth entropy and remaining-cutoff
decay remain separate, for the subsequent choice of the two depth fractions.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A geometric envelope absorbs the polynomial factor in the retained response catalogue. -/
theorem aux_lem_as_regularity_score_pair_geometric_card (d h : ℕ) :
    ((aux_prefix_rraw_G d h).card : ℝ) ≤
      (3 : ℝ) ^ (((d : ℝ) + 1) * ((h + 1 : ℕ) : ℝ)) := by
  have hp : h + 1 ≤ 3 ^ (h + 1) := (Nat.lt_pow_self (show 1 < 3 by norm_num)).le
  have hg := (aux_lem_as_regularity_retained_atom_tail_card d h).trans
    (Nat.mul_le_mul_right ((3 ^ (h + 1)) ^ d) hp)
  have hid : 3 ^ (h + 1) * (3 ^ (h + 1)) ^ d = 3 ^ ((d + 1) * (h + 1)) := by
    rw [← pow_succ', ← pow_mul]
    congr 1
    ring
  rw [hid] at hg
  have hcast : (((d + 1) * (h + 1) : ℕ) : ℝ) =
      ((d : ℝ) + 1) * ((h + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [← hcast, Real.rpow_natCast]
  exact_mod_cast hg

/-- The raw comparison tail is bounded by two geometric errors with positive model constants. -/
theorem lem_as_regularity_score_pair_geometric
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (s eps q : ℝ) (hs : 0 < s) (heps : 0 < eps)
    (hq : 1 ≤ q) (hsq : 8 * (d : ℝ) < s * q) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ tol : ℝ, 0 < tol → tol ≤ 1 →
      ∃ A c : ℝ, ∃ N0 : ℕ, 0 < A ∧ 0 < c ∧
        ∀ eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d,
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
            omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ≥0∞)
          (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
          (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          primitive_scores d M s eps (eta N omega)
            (fun m y => F N m y omega) (fun m y => Praw N m y omega)
            (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
            (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
        ∀ (n : ℤ) (z : SpatialCoordinates d) (N K h : ℕ),
          N0 ≤ K → n + (h : ℤ) + (K : ℤ) ≤ (N : ℤ) →
          (3 : ℝ) ^ (-(s / 2) * ((h + 1 : ℕ) : ℝ)) ≤ tol →
          ∃ M0 : ℕ, N ≤ M0 ∧ ∀ N' : ℕ, M0 ≤ N' →
            (chaosSampleLaw M).toMeasure {omega |
              (2 * tol) * (1 + eps ^ 2) / (eps ^ 2 - eps ^ 2 / 4) <
                Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega -
                  Z N' ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) omega ∨
              Real.sqrt (2 * tol) + 2 * tol <
                (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal -
                  (Draw N' ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) omega).toReal} ≤
              ENNReal.ofReal (A *
                ((3 : ℝ) ^ (((d : ℝ) + 1) * ((h + 1 : ℕ) : ℝ) - c * (K : ℝ)) +
                  (3 : ℝ) ^ (-(s / 8 - (d : ℝ) / q) * ((h + 1 : ℕ) : ℝ)))) := by
  obtain ⟨delta0, hdelta0, hrate⟩ := lem_as_regularity_score_pair_rate
    d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp s eps q hs heps hq hsq
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hH hM tol htol htol1
  obtain ⟨C, c, B, N0, hC, hc, hB, htail⟩ := hrate M Rm Sreg It H hH hM tol htol htol1
  obtain ⟨T, hT, hTbound⟩ := exists_initial_layer_half_decay d (aux_psf_sigma M) s
    (aux_psf_sigma_pos M).le hs
  let c' : ℝ := min c (s / 16)
  let A : ℝ := C + B / tol + T / tol + 1
  have hc' : 0 < c' := lt_min hc (by positivity)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A, c', N0, hA, hc', ?_⟩
  intro eta hEta F Praw Rraw Draw Z rawGood hPrim n z N K h hK hN hgeom
  obtain ⟨M0, hNM0, hM0⟩ := htail eta hEta F Praw Rraw Draw Z rawGood hPrim
    n z N K h hK hN hgeom
  refine ⟨M0, hNM0, fun N' hN' => (hM0 N' hN').trans ?_⟩
  let x : ℝ := (3 : ℝ) ^ (((d : ℝ) + 1) * ((h + 1 : ℕ) : ℝ) - c' * (K : ℝ))
  let y : ℝ := (3 : ℝ) ^ (-(s / 8 - (d : ℝ) / q) * ((h + 1 : ℕ) : ℝ))
  have hx : 0 ≤ x := Real.rpow_nonneg (by norm_num) _
  have hy : 0 ≤ y := Real.rpow_nonneg (by norm_num) _
  have hresponse : ((aux_prefix_rraw_G d h).card : ℝ) * (C * (3 : ℝ) ^ (-c * K)) ≤ C * x := by
    have hcard := aux_lem_as_regularity_score_pair_geometric_card d h
    have hdecay : (3 : ℝ) ^ (-c * (K : ℝ)) ≤ (3 : ℝ) ^ (-c' * (K : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) (Nat.cast_nonneg K)
    have hh := mul_le_mul hcard (mul_le_mul_of_nonneg_left hdecay hC.le)
      (by positivity) (by positivity)
    refine hh.trans_eq ?_
    dsimp only [x]
    rw [mul_left_comm, ← Real.rpow_add (show (0 : ℝ) < 3 by norm_num)]
    congr 2
    ring
  have hresponseTail : B * aux_prefix_rraw_rho d s q ^ (h + 1) / tol = B / tol * y := by
    rw [aux_prefix_rraw_rho, ← Real.rpow_mul_natCast (show (0 : ℝ) ≤ 3 by norm_num)]
    dsimp only [y]
    ring
  have hinitial : (3 : ℝ) ^ (-(s / 8) * (((N : ℤ) - n).toNat : ℝ)) *
      (aux_psf_sigma M * (2 * (2 +
        ((d * (((N : ℤ) - n).toNat + 1) + 1 : ℕ) : ℝ) * Real.log 3))) / tol ≤
        T / tol * x := by
    have hKk : (K : ℝ) ≤ (((N : ℤ) - n).toNat : ℝ) := by exact_mod_cast (show K ≤ ((N : ℤ) - n).toNat by omega)
    have hprod := mul_le_mul (min_le_right c (s / 16)) hKk (Nat.cast_nonneg K) (by positivity : (0 : ℝ) ≤ s / 16)
    have hexp : -(s / 16) * (((N : ℤ) - n).toNat : ℝ) ≤
        ((d : ℝ) + 1) * ((h + 1 : ℕ) : ℝ) - c' * (K : ℝ) := by
      have hdim : 0 ≤ ((d : ℝ) + 1) * ((h + 1 : ℕ) : ℝ) := by positivity
      change c' * (K : ℝ) ≤ s / 16 * (((N : ℤ) - n).toNat : ℝ) at hprod
      linarith only [hprod, hdim]
    have hp : (3 : ℝ) ^ (-(s / 16) * (((N : ℤ) - n).toNat : ℝ)) ≤ x :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hh := (hTbound ((N : ℤ) - n).toNat).trans (mul_le_mul_of_nonneg_left hp hT.le)
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      div_le_div_of_nonneg_right hh htol.le
  have hsum := add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hresponse)
    (le_of_eq (congrArg ENNReal.ofReal hresponseTail))) (ENNReal.ofReal_le_ofReal hinitial)
  refine hsum.trans ?_
  rw [← ENNReal.ofReal_add (mul_nonneg hC.le hx) (mul_nonneg (div_nonneg hB htol.le) hy),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hC.le hx) (mul_nonneg (div_nonneg hB htol.le) hy))
      (mul_nonneg (div_nonneg hT.le htol.le) hx)]
  apply ENNReal.ofReal_le_ofReal
  change C * x + B / tol * y + T / tol * x ≤ A * (x + y)
  have hBx := mul_nonneg (div_nonneg hB htol.le) hx
  have hCy := mul_nonneg hC.le hy
  have hTy := mul_nonneg (div_nonneg hT.le htol.le) hy
  dsimp only [A]
  nlinarith only [hBx, hCy, hTy, hx, hy]

end SubdiffusiveProcess.Paper
