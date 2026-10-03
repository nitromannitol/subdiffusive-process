module

public import SubdiffusiveProcess.Paper.lem_as_regularity_all_root_prefix
public import SubdiffusiveProcess.Paper.lem_as_regularity_countable_score_finite
public import SubdiffusiveProcess.Analysis.NativeScoreAllowance

@[expose] public section

/-! The actual finite native score allowance has one affine bound over every
padded mesh root and every cutoff. The conclusion supplies iteration budgets;
it does not assert the resulting solution regularity.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- A guarded physical score is nonnegative when the native bad score is nonnegative. -/
theorem aux_lem_as_regularity_native_allowance_nonneg {d : ℕ}
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (D : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ≥0∞)
    (N : ℕ) (omega : BilateralField d) (hZ : ∀ j w, 0 ≤ Z N j w omega)
    (k : ℤ) (w : SpatialCoordinates d) (tag : Bool) :
    0 ≤ aux_lem_as_regularity_mesh_transfer_value Z D N k w tag omega := by
  unfold aux_lem_as_regularity_mesh_transfer_value
  by_cases hk : k ≤ (N : ℤ)
  · rw [if_pos hk]
    cases tag
    · exact hZ _ _
    · exact ENNReal.toReal_nonneg
  · rw [if_neg hk]

/-- The physical prefix coordinate reflected about its root is the exact native score. -/
theorem aux_lem_as_regularity_native_allowance_value {d : ℕ}
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (D : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ≥0∞)
    (N : ℕ) (omega : BilateralField d) (k : ℤ) (hk : k ≤ (N : ℤ))
    (w : SpatialCoordinates d) (j : ℕ) (tag : Bool) :
    aux_lem_as_regularity_mesh_transfer_value Z D N
      (k + ((((N : ℤ) - k).toNat : ℤ) - j)) w tag omega =
      if tag then (D N j ((3 : ℝ) ^ N • w) omega).toReal
      else Z N j ((3 : ℝ) ^ N • w) omega := by
  have hnat : (((N : ℤ) - k).toNat : ℤ) = (N : ℤ) - k := Int.toNat_of_nonneg (by omega)
  have hlevel : k + ((((N : ℤ) - k).toNat : ℤ) - j) = (N : ℤ) - j := by rw [hnat]; omega
  unfold aux_lem_as_regularity_mesh_transfer_value
  rw [hlevel, if_pos (by omega : (N : ℤ) - j ≤ N)]
  have hindex : ((N : ℤ) - ((N : ℤ) - j)).toNat = j := by omega
  rw [hindex]

/-- The original prefix bank bounds the actual native score allowances uniformly in the cutoff. -/
theorem lem_as_regularity_native_allowance
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (s eps q lam A : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (hq : 1 ≤ q) (hsq : 8 * (d : ℝ) < s * q)
    (hlam : 0 < lam) (hA : 0 < A) (buffer J : ℕ) (rho xi : ℝ) (hrho : 0 ≤ rho)
    (hxi : 0 < xi) (hgap : (d : ℝ) * Real.log 3 < A * xi) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 → Rm.C ≤ Cresp →
      ∀ eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
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
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
        ∀ (N n : ℕ) (p : PrefixRootIndex d),
          p ∈ prefixRootCatalogue d rho J n → prefixRootLevel J p ≤ (N : ℤ) →
          (nativeScoreAllowance
            (fun j => Z N j ((3 : ℝ) ^ N • prefixRootCentre J p) omega)
            (fun j => Draw N j ((3 : ℝ) ^ N • prefixRootCentre J p) omega)
            ((N : ℤ) - prefixRootLevel J p).toNat lam : ℝ) ≤ xi * n + B := by
  obtain ⟨delta0, hd0, hprefix⟩ := lem_as_regularity_all_root_prefix d hd Jc Pc Xc Sf W Cp D hES
    Step Dbase Interp Cresp hCresp s eps q lam A hs heps hq hsq hlam hA
    buffer J rho xi hrho hxi hgap
  refine ⟨delta0, hd0, ?_⟩
  intro M Rm Sreg It H hIR hdelta hRm eta hEta F Praw Rraw Draw Z rawGood hPS
  have hfinite := lem_as_regularity_countable_score_finite M s eps hs.1 eta hEta
    F Praw Rraw Draw Z rawGood hPS (PrefixRootIndex d × ℕ)
    (fun ij _ => ij.2) (fun ij N => (3 : ℝ) ^ N • prefixRootCentre J ij.1)
  filter_upwards [hprefix M Rm Sreg It H hIR hdelta hRm eta hEta
    F Praw Rraw Draw Z rawGood hPS, hfinite, hPS] with omega hp hf hPSw
  obtain ⟨B, hB, hp⟩ := hp
  refine ⟨B + 27, by linarith only [hB], ?_⟩
  intro N n p hpMem hpN
  have hZ : ∀ j w, 0 ≤ Z N j w omega := fun j w =>
    aux_in_deterministic_onestep_Z_nonneg M s eps (eta N omega)
      _ _ _ _ _ _ (hPSw N) j w
  have hbound := nativeScoreAllowance_le
    (fun j => Z N j ((3 : ℝ) ^ N • prefixRootCentre J p) omega)
    (fun j => Draw N j ((3 : ℝ) ^ N • prefixRootCentre J p) omega)
    ((N : ℤ) - prefixRootLevel J p).toNat buffer lam (xi * n + B)
    (add_nonneg (mul_nonneg hxi.le (Nat.cast_nonneg _)) hB.le)
    (fun i => aux_lem_as_regularity_mesh_transfer_value Z Draw N
      (prefixRootLevel J p + i) (prefixRootCentre J p) false omega)
    (fun i => aux_lem_as_regularity_mesh_transfer_value Z Draw N
      (prefixRootLevel J p + i) (prefixRootCentre J p) true omega)
    (fun i => aux_lem_as_regularity_native_allowance_nonneg Z Draw N omega hZ _ _ false)
    (fun i => aux_lem_as_regularity_native_allowance_nonneg Z Draw N omega hZ _ _ true)
    (fun j _ => (aux_lem_as_regularity_native_allowance_value Z Draw N omega
      (prefixRootLevel J p) hpN (prefixRootCentre J p) j false).symm)
    (fun j _ => (aux_lem_as_regularity_native_allowance_value Z Draw N omega
      (prefixRootLevel J p) hpN (prefixRootCentre J p) j true).symm)
    (fun j _ => hf (p, j) N)
    (fun len hlen => ⟨hp N n len p hpMem hlen false, hp N n len p hpMem hlen true⟩)
  linarith only [hbound]

end Paper
