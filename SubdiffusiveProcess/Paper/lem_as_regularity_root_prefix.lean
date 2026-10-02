import SubdiffusiveProcess.Paper.lem_as_regularity_original_prefix_transfer
import SubdiffusiveProcess.Geometry.PrefixRootCatalogue

/-! The original prefix allowance on an explicit countable family of padded
triadic roots. Every root generation and every buffered prefix ending below
the chosen fraction of the cutoff is covered. This establishes the spatial
catalogue; it makes no deterministic regularity assertion.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal BigOperators Topology
noncomputable section
namespace Paper

/-- A common affine allowance controls both original prefixes on every shallow padded root. -/
theorem lem_as_regularity_root_prefix
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
      ∃ v : ℝ, (0 < v ∧ v < 1 / 4) ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
          ∀ᶠ N : ℕ in atTop, ∀ (n len : ℕ) (p : PrefixRootIndex d),
            p ∈ prefixRootCatalogue d rho J n → n ≤ ⌊v * N⌋₊ →
            prefixRootLevel J p + (len : ℤ) + buffer ≤ (⌊v * N⌋₊ : ℤ) →
            xi * (n : ℝ) + B ≤ (len : ℝ) → ∀ useD : Bool,
              (∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((len : ℤ) + buffer),
                aux_lem_as_regularity_mesh_transfer_value Z Draw N
                  (prefixRootLevel J p + j) (prefixRootCentre J p) useD omega) ≤
                lam * len := by
  classical
  obtain ⟨delta0, hdelta0, hbank⟩ := lem_as_regularity_original_prefix_transfer
    d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp Cresp hCresp s eps q lam A
      hs heps hq hsq hlam hA buffer d (Nat.cast_nonneg _)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hH hdelta hRm eta hEta F Praw Rraw Draw Z rawGood hPrim
  obtain ⟨v, hv, hroot⟩ := hbank M Rm Sreg It H hH hdelta hRm eta hEta
    F Praw Rraw Draw Z rawGood hPrim (PrefixRootIndex d)
      (prefixRootLevel J) (prefixRootCentre J)
  let roots := fun n => prefixRootCatalogue d rho J n
  let coords := fun N : ℕ => prefixCoordinateCatalogue d rho J buffer ⌊v * N⌋₊
  have hcoord (n : ℕ) : ((coords n).card : ℝ) ≤
      (prefixRootCountConstant d rho J * ((J : ℝ) + buffer + 1)) *
        ((n : ℝ) + 1) ^ 3 * (3 : ℝ) ^ (((d : ℝ) * v) * n) :=
    prefixCoordinateCatalogue_cutoff_card_le d rho hrho J buffer n v hv.1.le
      (by linarith only [hv.2])
  have hlevel (N : ℕ) (i : Fin (coords N).card) :
      ((prefixRootLevel J (finiteCatalogueEntry (coords N) i).1 +
        (finiteCatalogueEntry (coords N) i).2 : ℤ) : ℝ) ≤ v * N := by
    have hh := prefixCoordinateCatalogue_level rho J buffer ⌊v * N⌋₊ _
      (finiteCatalogueEntry_mem (coords N) i)
    have hhR : ((prefixRootLevel J (finiteCatalogueEntry (coords N) i).1 +
        (finiteCatalogueEntry (coords N) i).2 : ℤ) : ℝ) ≤ (⌊v * N⌋₊ : ℝ) := by
      exact_mod_cast hh
    exact hhR.trans (Nat.floor_le (mul_nonneg hv.1.le (Nat.cast_nonneg _)))
  have hB := hroot (fun n => (roots n).card) d 1 (prefixRootCountConstant d rho J) xi
    (prefixRootCountConstant_nonneg d rho J hrho) hxi hgap
    (prefixRootCatalogue_card_le_rpow d rho hrho J)
    (fun n => finiteCatalogueEntry (roots n))
    (fun N => (coords N).card) (fun N => finiteCatalogueEntry (coords N)) 3
    (prefixRootCountConstant d rho J * ((J : ℝ) + buffer + 1))
    (mul_nonneg (prefixRootCountConstant_nonneg d rho J hrho) (by positivity))
    hcoord hlevel
  refine ⟨v, hv, ?_⟩
  filter_upwards [hB] with omega homega
  obtain ⟨B, hBpos, hBbound⟩ := homega
  refine ⟨B, hBpos, ?_⟩
  filter_upwards [hBbound] with N hN
  intro n len p hp hn hend hlen useD
  obtain ⟨i, hi⟩ := finiteCatalogueEntry_surjective (roots n) p hp
  have hcover : ∀ j ∈ Finset.Icc (-(buffer : ℤ)) ((len : ℤ) + buffer),
      ∃ e : Fin (coords N).card,
        finiteCatalogueEntry (coords N) e = (finiteCatalogueEntry (roots n) i, j) := by
    intro j hj
    rw [hi]
    exact finiteCatalogueEntry_surjective (coords N) (p, j)
      (prefixCoordinateCatalogue_covers rho J buffer ⌊v * N⌋₊ n len p hp hn hend j hj)
  simpa only [hi] using hN n i len hlen hcover useD

end Paper
