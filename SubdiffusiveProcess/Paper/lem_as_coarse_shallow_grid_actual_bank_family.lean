import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_root_bank_limits
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_bank_coordinate_moment

open MeasureTheory SubdiffusiveProcess Homogenization Homogenization.Book.Ch02 Filter
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The actual root Dirichlet and inverse-Neumann responses admit a single
measurable, nonnegative, uniformly moment-bounded selector over the finite
coordinate bank. -/
theorem lem_as_coarse_shallow_grid_actual_bank_family
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (W : SubdiffusiveProcess.Lane4.SmallPerturbationInput d) (Cp : SubdiffusiveProcess.Lane4.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (HI : InfraredCharacterization M H),
        M.delta ≤ δ →
        ∃ Z : Bool × Fin d → BilateralField d → ℝ,
          ∀ b i,
            Measurable (Z (b, i)) ∧
            (∀ om, 0 ≤ Z (b, i) om) ∧
            TendstoInMeasure (chaosSampleLaw M).toMeasure
              (aux_matched_affine_finite_response M (Pi.single i 1) b) atTop
              (Z (b, i)) ∧
            AEStronglyMeasurable (Z (b, i)) (chaosSampleLaw M).toMeasure ∧
            eLpNorm (Z (b, i)) (ENNReal.ofReal (2 * q))
              (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (2 * volume.real
                (centeredCube (0 : SpatialCoordinates d) 1
                  (by norm_num) : Set (SpatialCoordinates d)) * (C + 1)) := by
  obtain ⟨δA, hδA, hactual⟩ :=
    lem_as_coarse_shallow_grid_actual_root_bank_limits d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  obtain ⟨δB, CB, hδB, hCB, hmoment⟩ :=
    lem_as_coarse_shallow_grid_bank_coordinate_moment hd Jc q hq
  let δ := min δB (min 1 δA)
  refine ⟨δ, CB, lt_min hδB (lt_min zero_lt_one hδA), hCB, ?_⟩
  intro M Rm Sreg It H HI hM
  have hMB : M.delta ≤ δB := le_trans hM (min_le_left _ _)
  have hMA : M.delta ≤ min 1 δA := le_trans hM (min_le_right _ _)
  let W : Fin d → (BilateralField d → ℝ) × (BilateralField d → ℝ) :=
    fun i =>
      let hsource := hactual M Rm Sreg It H HI hMA (Pi.single i 1)
      (Classical.choose hsource, Classical.choose (Classical.choose_spec hsource))
  have hW : ∀ i,
      (Measurable (W i).1 ∧ (∀ om, 0 ≤ (W i).1 om) ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (aux_matched_affine_finite_response M (Pi.single i 1) false) atTop (W i).1) ∧
      (Measurable (W i).2 ∧ (∀ om, 0 ≤ (W i).2 om) ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (aux_matched_affine_finite_response M (Pi.single i 1) true) atTop (W i).2) := by
    intro i
    let hsource := hactual M Rm Sreg It H HI hMA (Pi.single i 1)
    rcases Classical.choose_spec (Classical.choose_spec hsource) with
      ⟨hDmeas, hDnonneg, hDconv, hNmeas, hNnonneg, hNconv⟩
    change (Measurable (Classical.choose hsource) ∧
        (∀ om, 0 ≤ Classical.choose hsource om) ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (aux_matched_affine_finite_response M (Pi.single i 1) false) atTop
          (Classical.choose hsource)) ∧
      (Measurable (Classical.choose (Classical.choose_spec hsource)) ∧
        (∀ om, 0 ≤ Classical.choose (Classical.choose_spec hsource) om) ∧
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (aux_matched_affine_finite_response M (Pi.single i 1) true) atTop
          (Classical.choose (Classical.choose_spec hsource)) )
    exact ⟨⟨hDmeas, hDnonneg, hDconv⟩, ⟨hNmeas, hNnonneg, hNconv⟩⟩
  let Z : Bool × Fin d → BilateralField d → ℝ :=
    fun p => if p.1 then (W p.2).2 else (W p.2).1
  refine ⟨Z, ?_⟩
  intro b i
  have hWi := hW i
  have hlim : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (aux_matched_affine_finite_response M (Pi.single i 1) b) atTop (Z (b, i)) := by
    cases b with
    | false =>
        simpa [Z] using hWi.1.2.2
    | true =>
        simpa [Z] using hWi.2.2.2
  have hmeas : Measurable (Z (b, i)) := by
    cases b with
    | false => simpa [Z] using hWi.1.1
    | true => simpa [Z] using hWi.2.1
  have hnonneg : ∀ om, 0 ≤ Z (b, i) om := by
    cases b with
    | false => simpa [Z] using hWi.1.2.1
    | true => simpa [Z] using hWi.2.2.1
  have hmom := hmoment M hMB b i (Z (b, i)) hlim
  exact ⟨hmeas, hnonneg, hlim, hmom.1.1, hmom.1.2⟩

end Paper


