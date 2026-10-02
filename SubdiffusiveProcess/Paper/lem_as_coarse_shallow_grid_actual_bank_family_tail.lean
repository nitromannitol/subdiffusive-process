import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_bank_family
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_bank_limit_tail

open MeasureTheory Filter SubdiffusiveProcess Homogenization Homogenization.Book.Ch02
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The family selector has the tail proved for any other limit of the same responses. -/
theorem lem_as_coarse_shallow_grid_actual_bank_family_tail
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
          (∀ b i, Measurable (Z (b, i)) ∧ (∀ om, 0 ≤ Z (b, i) om) ∧
            TendstoInMeasure (chaosSampleLaw M).toMeasure
              (aux_matched_affine_finite_response M (Pi.single i 1) b) atTop
              (Z (b, i)) ∧
            AEStronglyMeasurable (Z (b, i)) (chaosSampleLaw M).toMeasure ∧
            eLpNorm (Z (b, i)) (ENNReal.ofReal (2 * q))
              (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (2 * volume.real
                (centeredCube (0 : SpatialCoordinates d) 1
                  (by norm_num) : Set (SpatialCoordinates d)) * (C + 1))) ∧
          ∀ b : Bool, ∃ Cgeom : ℝ, 0 < Cgeom ∧
            ∀ i : Fin d, ∀ eps : ℝ, 0 < eps →
              ∃ Ce ce : ℝ, ∃ Ne : ℕ, 0 < Ce ∧ 0 < ce ∧
                ∀ N : ℕ, Ne ≤ N →
                  (chaosSampleLaw M).toMeasure
                    {om | Cgeom * eps * Z (b, i) om +
                      Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                      |aux_matched_affine_finite_response M (Pi.single i 1) b N om -
                        Z (b, i) om|} ≤
                    ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
  obtain ⟨δF, C, hδF, hC, hF⟩ :=
    lem_as_coarse_shallow_grid_actual_bank_family d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp q hq
  obtain ⟨δD, CGD, hδD, hCGD, hD⟩ :=
    lem_as_coarse_shallow_grid_actual_bank_limit_tail d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp false
  obtain ⟨δN, CGN, hδN, hCGN, hN⟩ :=
    lem_as_coarse_shallow_grid_actual_bank_limit_tail d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp true
  refine ⟨min δF (min 1 (min δD δN)), C,
    lt_min hδF (lt_min zero_lt_one (lt_min hδD hδN)), hC, ?_⟩
  intro M Rm Sreg It H HI hM
  obtain ⟨Z, hZ⟩ := hF M Rm Sreg It H HI (hM.trans (min_le_left _ _))
  refine ⟨Z, hZ, ?_⟩
  intro b
  cases b with
  | false =>
      refine ⟨CGD, hCGD, ?_⟩
      intro i eps heps
      obtain ⟨W, hWmeas, hWpos, hWlim, hWt⟩ :=
        hD M Rm Sreg It H HI (hM.trans (le_trans (min_le_right _ _)
          (min_le_min_left 1 (min_le_left δD δN)))) i
      obtain ⟨Ce, ce, Ne, hCe, hce, ht⟩ := hWt eps heps
      refine ⟨Ce, ce, Ne, hCe, hce, ?_⟩
      have heq : W =ᵐ[(chaosSampleLaw M).toMeasure] Z (false, i) :=
        tendstoInMeasure_ae_unique hWlim (hZ false i).2.2.1
      intro k hk
      have hsets :
          (chaosSampleLaw M).toMeasure
            {om | CGD * eps * Z (false, i) om + Ce * (3 : ℝ) ^ (-(ce * (k : ℝ))) <
              |aux_matched_affine_finite_response M (Pi.single i 1) false k om -
                Z (false, i) om|} =
          (chaosSampleLaw M).toMeasure
            {om | CGD * eps * W om + Ce * (3 : ℝ) ^ (-(ce * (k : ℝ))) <
              |aux_matched_affine_finite_response M (Pi.single i 1) false k om - W om|} := by
        apply measure_congr
        filter_upwards [heq] with om hom
        change (CGD * eps * Z (false, i) om + Ce * (3 : ℝ) ^ (-(ce * (k : ℝ))) <
          |aux_matched_affine_finite_response M (Pi.single i 1) false k om -
            Z (false, i) om|) =
          (CGD * eps * W om + Ce * (3 : ℝ) ^ (-(ce * (k : ℝ))) <
          |aux_matched_affine_finite_response M (Pi.single i 1) false k om - W om|)
        rw [hom]
      rw [hsets]
      exact ht k hk
  | true =>
      refine ⟨CGN, hCGN, ?_⟩
      intro i eps heps
      obtain ⟨W, hWmeas, hWpos, hWlim, hWt⟩ :=
        hN M Rm Sreg It H HI (hM.trans (le_trans (min_le_right _ _)
          (min_le_min_left 1 (min_le_right δD δN)))) i
      obtain ⟨Ce, ce, Ne, hCe, hce, ht⟩ := hWt eps heps
      refine ⟨Ce, ce, Ne, hCe, hce, ?_⟩
      have heq : W =ᵐ[(chaosSampleLaw M).toMeasure] Z (true, i) :=
        tendstoInMeasure_ae_unique hWlim (hZ true i).2.2.1
      intro k hk
      have hsets :
          (chaosSampleLaw M).toMeasure
            {om | CGN * eps * Z (true, i) om + Ce * (3 : ℝ) ^ (-(ce * (k : ℝ))) <
              |aux_matched_affine_finite_response M (Pi.single i 1) true k om -
                Z (true, i) om|} =
          (chaosSampleLaw M).toMeasure
            {om | CGN * eps * W om + Ce * (3 : ℝ) ^ (-(ce * (k : ℝ))) <
              |aux_matched_affine_finite_response M (Pi.single i 1) true k om - W om|} := by
        apply measure_congr
        filter_upwards [heq] with om hom
        change (CGN * eps * Z (true, i) om + Ce * (3 : ℝ) ^ (-(ce * (k : ℝ))) <
          |aux_matched_affine_finite_response M (Pi.single i 1) true k om -
            Z (true, i) om|) =
          (CGN * eps * W om + Ce * (3 : ℝ) ^ (-(ce * (k : ℝ))) <
          |aux_matched_affine_finite_response M (Pi.single i 1) true k om - W om|)
        rw [hom]
      rw [hsets]
      exact ht k hk

end Paper


