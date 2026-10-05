module

public import SubdiffusiveProcess.Paper.lem_as_regularity_mesh_transfer
public import SubdiffusiveProcess.Paper.lem_as_regularity_limit_prefix
public import SubdiffusiveProcess.Analysis.PrefixComparisonMargin

@[expose] public section

/-! The common limiting prefix allowance transfers to the actual original
finite-cutoff prefixes on a growing coordinate catalogue. Both bad and error
prefixes use one intercept. Coverage and cardinality of the concrete geometric
catalogues are explicit; this file does not construct the regularity mesh.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Every guarded original physical score coordinate is almost-everywhere strongly measurable. -/
theorem aux_lem_as_regularity_original_prefix_transfer_meas {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ)
    (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ≥0∞)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (N : ℕ) (n : ℤ) (z : SpatialCoordinates d) (useD : Bool) :
    AEStronglyMeasurable (aux_lem_as_regularity_mesh_transfer_value Z Draw N n z useD)
      (chaosSampleLaw M).toMeasure := by
  change AEStronglyMeasurable (fun omega => if n ≤ (N : ℤ) then
    if useD then (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal
    else Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega else 0)
    (chaosSampleLaw M).toMeasure
  by_cases hn : n ≤ (N : ℤ)
  · cases useD with
    | false =>
      simpa only [aux_lem_as_regularity_mesh_transfer_value, ite_eq_left hn,
        Bool.false_eq_true, ↓reduceIte] using
        (actual_Z_aemeas M s eps (chaosSampleLaw M).toMeasure eta
          (prefix_eta_aemeasurable M eta hEta) F Praw Rraw Draw Z rawGood hPrimitive
          N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)).aestronglyMeasurable
    | true =>
      simpa only [aux_lem_as_regularity_mesh_transfer_value, ite_eq_left hn, ↓reduceIte] using
        (dsc_raw_aemeas M s eps (chaosSampleLaw M).toMeasure eta
          (prefix_eta_aemeasurable M eta hEta) F Praw Rraw Draw Z rawGood hPrimitive
          N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z)).aestronglyMeasurable
  · simp only [ite_eq_right hn]
    exact aestronglyMeasurable_const

/-- One root-depth intercept controls the actual finite prefixes covered by an admissible growing catalogue. -/
theorem lem_as_regularity_original_prefix_transfer
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
    (hlam : 0 < lam) (hA : 0 < A) (buffer : ℕ) (g : ℝ) (hg : 0 ≤ g) :
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
      ∀ (Pos : Type) [Countable Pos] (level : Pos → ℤ) (centre : Pos → SpatialCoordinates d),
      ∃ v : ℝ, (0 < v ∧ v < 1 / 4) ∧
        ∀ (kr : ℕ → ℕ) (gr br : ℕ) (Cr xi : ℝ), 0 ≤ Cr → 0 < xi →
          (gr : ℝ) * Real.log 3 < A * xi →
          (∀ n, (kr n : ℝ) ≤ Cr * ((n : ℝ) + 1) ^ br * (3 : ℝ) ^ ((gr : ℝ) * n)) →
        ∀ roots : ∀ n, Fin (kr n) → Pos,
        ∀ (kc : ℕ → ℕ) (coords : ∀ N, Fin (kc N) → Pos × ℤ) (bc : ℕ) (Cc : ℝ),
          0 ≤ Cc →
          (∀ N, (kc N : ℝ) ≤ Cc * ((N : ℝ) + 1) ^ bc * (3 : ℝ) ^ ((g * v) * N)) →
          (∀ N i, ((level (coords N i).1 + (coords N i).2 : ℤ) : ℝ) ≤ v * N) →
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
            ∀ᶠ N in atTop, ∀ (n : ℕ) (i : Fin (kr n)) (len : ℕ),
              xi * (n : ℝ) + B ≤ (len : ℝ) →
              (∀ j ∈ Finset.Icc (-(buffer : ℤ)) ((len : ℤ) + buffer),
                ∃ e : Fin (kc N), coords N e = (roots n i, j)) →
              ∀ useD : Bool,
                (∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((len : ℤ) + buffer),
                  aux_lem_as_regularity_mesh_transfer_value Z Draw N
                    (level (roots n i) + j) (centre (roots n i)) useD omega) ≤ lam * len := by
  let loss : ℝ := lam / (4 * ((buffer : ℝ) + 1))
  have hloss : 0 < loss := div_pos hlam (by positivity)
  have hmargin : 2 * ((buffer : ℝ) + 1) * loss ≤ lam / 2 := by
    dsimp only [loss]
    have hbuf : (buffer : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring_nf
    norm_num
  obtain ⟨tol, htol, htol1, hZloss, hDloss⟩ := exists_score_comparison_tolerance eps loss hloss
  obtain ⟨dl, hdl, hlimit⟩ := lem_as_regularity_limit_prefix
    d hd Jc Pc Xc W Sf D Cresp hCresp s eps lam A buffer hs heps hlam hA
  obtain ⟨dt, hdt, htransfer⟩ := lem_as_regularity_mesh_transfer
    d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp s eps q hs.1 heps.1 hq hsq g hg
  refine ⟨min dl dt, lt_min hdl hdt, ?_⟩
  intro M Rm Sreg It H hH hM hRm eta hEta F Praw Rraw Draw Z rawGood hPrim
    Pos hPos level centre
  obtain ⟨phi, hphi, Vlim, hVm, hconv, _htail, hbank⟩ :=
    hlimit M (hM.trans (min_le_left _ _)) Rm hRm Sreg It H hH eta hEta
      F Praw Rraw Draw Z rawGood hPrim Pos level centre
  have hmeasure : ∀ (pos : Pos) (j : ℤ) (useD : Bool),
      TendstoInMeasure (chaosSampleLaw M).toMeasure
        (fun k => aux_lem_as_regularity_mesh_transfer_value Z Draw (phi k)
          (level pos + j) (centre pos) useD) atTop (Vlim pos j useD) := by
    intro pos j useD
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    simpa only [aux_lem_as_regularity_mesh_transfer_value, Pi.sub_apply] using! hconv pos j useD
  obtain ⟨u, v, _hu, hv, hmesh⟩ := htransfer M Rm Sreg It H hH
    (hM.trans (min_le_right _ _)) tol loss htol htol1 hZloss hDloss
  have hm := hmesh eta hEta F Praw Rraw Draw Z rawGood hPrim (Pos × ℤ)
    (fun p => level p.1 + p.2) (fun p => centre p.1) phi hphi
    (fun p useD => Vlim p.1 p.2 useD) (fun p useD => hmeasure p.1 p.2 useD)
  refine ⟨v, hv, ?_⟩
  intro kr gr br Cr xi hCr hxi hgap hrootcard roots kc coords bc Cc hCc hcard hlevel
  have hlimBank := hbank kr gr br Cr xi hCr hxi hgap hrootcard roots
  have hfinite := hm kc coords bc Cc hCc hcard hlevel
  filter_upwards [hlimBank, hfinite] with omega hB hfinite
  obtain ⟨B0, hB0, hB0bound⟩ := hB
  refine ⟨B0 + 1, by linarith only [hB0], ?_⟩
  filter_upwards [hfinite] with N hN
  intro n i len hlen hcover useD
  have hlen0 : 1 ≤ len := by
    have hxiN := mul_nonneg hxi.le (Nat.cast_nonneg (α := ℝ) n)
    have hlenreal : (0 : ℝ) < len := by linarith only [hlen, hB0, hxiN]
    exact_mod_cast (show (0 : ℕ) < len by exact_mod_cast hlenreal)
  apply buffered_prefix_le_of_comparison buffer len hlen0
    (fun j => aux_lem_as_regularity_mesh_transfer_value Z Draw N
      (level (roots n i) + j) (centre (roots n i)) useD omega)
    (fun j => Vlim (roots n i) j useD omega) lam loss hloss.le hmargin
  · intro j hj
    obtain ⟨e, he⟩ := hcover j hj
    have hp := hN e useD
    change aux_lem_as_regularity_mesh_transfer_value Z Draw N
      (level (coords N e).1 + (coords N e).2) (centre (coords N e).1) useD omega ≤
        Vlim (coords N e).1 (coords N e).2 useD omega + loss at hp
    simpa only [he] using hp
  · exact hB0bound n i len (by linarith only [hlen]) useD

end SubdiffusiveProcess.Paper
