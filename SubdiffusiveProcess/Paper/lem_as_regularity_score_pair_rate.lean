module

public import SubdiffusiveProcess.Paper.lem_as_regularity_coordinate_pair_tail
public import SubdiffusiveProcess.Paper.lem_as_regularity_retained_atom_tail
public import SubdiffusiveProcess.Paper.lem_as_regularity_residual_tails

@[expose] public section

/-! Quantitative two-cutoff tails for both original physical primitive scores.
The estimate combines the retained response bank with the two explicit
residual tails; no growing spatial catalogue is hidden in the constants.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The actual bad and accumulated-error coordinates have an explicit quantitative comparison tail. -/
theorem lem_as_regularity_score_pair_rate
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
    (s eps q : ℝ) (hs : 0 < s) (heps : 0 < eps)
    (hq : 1 ≤ q) (hsq : 8 * (d : ℝ) < s * q) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ tol : ℝ, 0 < tol → tol ≤ 1 →
      ∃ C c B : ℝ, ∃ N0 : ℕ, 0 < C ∧ 0 < c ∧ 0 ≤ B ∧
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
              ENNReal.ofReal (((aux_prefix_rraw_G d h).card : ℝ) *
                (C * (3 : ℝ) ^ (-c * (K : ℝ)))) +
              ENNReal.ofReal (B * aux_prefix_rraw_rho d s q ^ (h + 1) / tol) +
              ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (((N : ℤ) - n).toNat : ℝ)) *
                (aux_psf_sigma M * (2 * (2 +
                  ((d * (((N : ℤ) - n).toNat + 1) + 1 : ℕ) : ℝ) * Real.log 3))) / tol) := by
  obtain ⟨da, hda, ha⟩ := lem_as_regularity_retained_atom_tail
    d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  obtain ⟨dr, hdr, hr⟩ := lem_as_regularity_residual_tails d s q hq hsq
  refine ⟨min da dr, lt_min hda hdr, ?_⟩
  intro M Rm Sreg It H hH hM tol htol htol1
  obtain ⟨C, c, N0, hC, hc, hretained⟩ :=
    ha M Rm Sreg It H hH (hM.trans (min_le_left _ _)) (tol / 2) (by positivity)
  obtain ⟨B, hB, hresidual⟩ := hr M (hM.trans (min_le_right _ _))
  refine ⟨C, c, B, N0, hC, hc, hB, ?_⟩
  intro eta hEta F Praw Rraw Draw Z rawGood hPrim n z N K h hK hN hgeom
  obtain ⟨M0, hNM0, hM0⟩ := hretained eta hEta n z N K h hK hN
  refine ⟨M0, hNM0, ?_⟩
  intro N' hN'
  have hres := hresidual eta hEta N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) h tol htol
  exact lem_as_regularity_coordinate_pair_tail M s eps hs heps eta hEta
    F Praw Rraw Draw Z rawGood hPrim n z N N' h (hNM0.trans hN') (by omega)
    tol htol.le htol1 hgeom _ _ _ (hM0 N' hN') hres.1 hres.2

end SubdiffusiveProcess.Paper
