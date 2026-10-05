module

public import SubdiffusiveProcess.Paper.lem_as_regularity_root_prefix
public import SubdiffusiveProcess.Probability.CutoffPrefixAllowance

@[expose] public section

/-! The common original prefix allowance holds on every padded triadic root
at every cutoff. The shallow transfer and the original exponential tails
cover complementary regions. No deterministic regularity estimate is asserted.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The two-score union absorbs both factors of two into the prescribed exponential rate. -/
theorem aux_lem_as_regularity_all_root_prefix_union
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (X : Bool → Omega → ℝ) (lam A : ℝ) (m : ℕ) (hA : 0 < A) (hm : 1 ≤ m)
    (ht : ∀ tag, mu {omega | lam * m < X tag omega} ≤
      ENNReal.ofReal (2 * Real.exp (-((2 * A + Real.log 2 + Real.log 2) * m)))) :
    mu ({omega | lam * m < X false omega} ∪ {omega | lam * m < X true omega}) ≤
      ENNReal.ofReal (Real.exp (-(2 * A * m))) := by
  have hrate : 0 < 2 * A + Real.log 2 :=
    add_pos_of_pos_of_nonneg (by linarith only [hA]) (Real.log_nonneg (by norm_num))
  have hfirst : 2 * Real.exp (-((2 * A + Real.log 2 + Real.log 2) * m)) ≤
      Real.exp (-((2 * A + Real.log 2) * m)) := by
    simpa only [Nat.cast_zero, zero_add, mul_one, add_zero] using
      buffered_prefix_tail_le (2 * A + Real.log 2) hrate 0 m hm
  have hsecond : 2 * Real.exp (-((2 * A + Real.log 2) * m)) ≤
      Real.exp (-(2 * A * m)) := by
    simpa only [Nat.cast_zero, zero_add, mul_one, add_zero] using
      buffered_prefix_tail_le (2 * A) (by linarith only [hA]) 0 m hm
  calc mu ({omega | lam * m < X false omega} ∪ {omega | lam * m < X true omega}) ≤
      mu {omega | lam * m < X false omega} + mu {omega | lam * m < X true omega} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-((2 * A + Real.log 2) * m))) +
        ENNReal.ofReal (Real.exp (-((2 * A + Real.log 2) * m))) :=
      add_le_add ((ht false).trans (ENNReal.ofReal_le_ofReal hfirst))
        ((ht true).trans (ENNReal.ofReal_le_ofReal hfirst))
    _ = ENNReal.ofReal (2 * Real.exp (-((2 * A + Real.log 2) * m))) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsecond

/-- Both original prefix banks admit one affine root-generation allowance for every cutoff. -/
theorem lem_as_regularity_all_root_prefix
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
    (Cresp : ℝ) (hCresp : 0 < Cresp) (s eps q lam A : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (hq : 1 ≤ q) (hsq : 8 * (d : ℝ) < s * q)
    (hlam : 0 < lam) (hA : 0 < A) (buffer J : ℕ) (rho xi : ℝ) (hrho : 0 ≤ rho)
    (hxi : 0 < xi) (hgap : (d : ℝ) * Real.log 3 < A * xi) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 → Rm.C ≤ Cresp →
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
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
        ∀ (N n len : ℕ) (p : PrefixRootIndex d),
          p ∈ prefixRootCatalogue d rho J n → xi * (n : ℝ) + B ≤ (len : ℝ) →
          ∀ useD : Bool,
            (∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((len : ℤ) + buffer),
              aux_lem_as_regularity_mesh_transfer_value Z Draw N
                (prefixRootLevel J p + j) (prefixRootCentre J p) useD omega) ≤
              lam * len := by
  classical
  obtain ⟨ds, hds, hshort⟩ := lem_as_regularity_root_prefix d hd Jc Pc Xc Sf W Cp D hES
    Step Dbase Interp Cresp hCresp s eps q lam A hs heps hq hsq hlam hA
      buffer J rho xi hrho hxi hgap
  have hrate : 0 < 2 * A + Real.log 2 + Real.log 2 := by
    have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith only [hh, hA]
  obtain ⟨dt, hdt, htail⟩ := prefix_physical_tail d s eps (4 * lam)
    (2 * A + Real.log 2 + Real.log 2) buffer hs heps (by positivity) hrate
  refine ⟨min ds dt, lt_min hds hdt, ?_⟩
  intro M Rm Sreg It H hH hdelta hRm eta hEta F Praw Rraw Draw Z rawGood hPrim
  obtain ⟨v, hv, hshort⟩ := hshort M Rm Sreg It H hH
    (hdelta.trans (min_le_left _ _)) hRm eta hEta F Praw Rraw Draw Z rawGood hPrim
  let roots := fun n => prefixRootCatalogue d rho J n
  let entry := fun n => finiteCatalogueEntry (roots n)
  let X := fun (N n : ℕ) (i : Fin (roots n).card) (m : ℕ) (tag : Bool) omega =>
    ∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((m : ℤ) + buffer),
      aux_lem_as_regularity_mesh_transfer_value Z Draw N
        (prefixRootLevel J (entry n i) + j) (prefixRootCentre J (entry n i)) tag omega
  let bad := fun (N n : ℕ) (i : Fin (roots n).card) (m : ℕ) =>
    {omega | lam * m < X N n i m false omega} ∪
      {omega | lam * m < X N n i m true omega}
  have hbad N n i m (hm : 1 ≤ m) :
      (chaosSampleLaw M).toMeasure (bad N n i m) ≤
        ENNReal.ofReal (Real.exp (-(2 * A * m))) := by
    apply aux_lem_as_regularity_all_root_prefix_union _ _ lam A m hA hm
    intro tag
    have ht := (htail M (hdelta.trans (min_le_right _ _)) eta hEta
      F Praw Rraw Draw Z rawGood hPrim N (prefixRootLevel J (entry n i)).toNat m hm
        (-(prefixRootLevel J (entry n i))).toNat (prefixRootCentre J (entry n i)) tag).1
    have heq omega : X N n i m tag omega =
        aux_prefix_physical_tail_sum N (prefixRootLevel J (entry n i)).toNat buffer m
          (-(prefixRootLevel J (entry n i))).toNat (prefixRootCentre J (entry n i))
            Z Draw tag omega :=
      aux_lem_as_regularity_limit_prefix_sum Z Draw N buffer m
        (prefixRootLevel J (entry n i)) (prefixRootCentre J (entry n i)) tag omega
    simpa only [heq, show 4 * lam * (m : ℝ) / 4 = lam * m by ring] using ht
  let covered := fun N n m : ℕ => n + m + buffer ≤ ⌊v * N⌋₊
  have hcomp N n m (hh : ¬ covered N n m) :
      (N : ℝ) ≤ v⁻¹ * ((n : ℝ) + m + buffer) := by
    have hf : ⌊v * (N : ℝ)⌋₊ < n + m + buffer := Nat.lt_of_not_ge hh
    have hfr : v * (N : ℝ) < (n : ℝ) + m + buffer := by
      exact_mod_cast Nat.lt_of_floor_lt hf
    have hh := mul_le_mul_of_nonneg_left hfr.le (inv_pos.mpr hv.1).le
    simpa only [← mul_assoc, inv_mul_cancel₀ hv.1.ne', one_mul] using hh
  have hsbank : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
      ∀ᶠ N : ℕ in atTop, ∀ (n : ℕ) (i : Fin (roots n).card) (m : ℕ),
        xi * (n : ℝ) + B ≤ (m : ℝ) →
        covered N n m → omega ∉ bad N n i m := by
    filter_upwards [hshort] with omega hB
    obtain ⟨B, hB, hbound⟩ := hB
    refine ⟨B, hB, ?_⟩
    filter_upwards [hbound] with N hN
    intro n i m hlen hcover
    have hmem := finiteCatalogueEntry_mem (roots n) i
    have hp := (mem_prefixRootCatalogue rho J n (entry n i)).mp hmem
    have hplevel : prefixRootLevel J (entry n i) ≤ (n : ℤ) := by
      dsimp only [prefixRootLevel]
      omega
    have hcover' : n + m + buffer ≤ ⌊v * (N : ℝ)⌋₊ := hcover
    have hh tag := hN n m (entry n i) hmem (by omega) (by omega) hlen tag
    exact fun hbad => hbad.elim
      (fun hh' => (not_lt_of_ge (hh false)) hh')
      (fun hh' => (not_lt_of_ge (hh true)) hh')
  have hB := ae_all_cutoff_prefix_allowance (chaosSampleLaw M).toMeasure
    (fun n => (roots n).card) d 1 buffer (prefixRootCountConstant d rho J) A xi v⁻¹
    (prefixRootCountConstant_nonneg d rho J hrho) hA hxi (inv_pos.mpr hv.1).le hgap
    (prefixRootCatalogue_card_le_rpow d rho hrho J) bad hbad covered hcomp hsbank
  filter_upwards [hB] with omega homega
  obtain ⟨B, hBpos, hbound⟩ := homega
  refine ⟨B, hBpos, ?_⟩
  intro N n len p hp hlen tag
  obtain ⟨i, hi⟩ := finiteCatalogueEntry_surjective (roots n) p hp
  have hh := hbound N n i len hlen
  change ¬ (_ ∨ _) at hh
  have htag : X N n i len tag omega ≤ lam * len := by
    cases tag
    · exact le_of_not_gt (not_or.mp hh).1
    · exact le_of_not_gt (not_or.mp hh).2
  simpa only [X, entry, hi] using htag

end SubdiffusiveProcess.Paper
