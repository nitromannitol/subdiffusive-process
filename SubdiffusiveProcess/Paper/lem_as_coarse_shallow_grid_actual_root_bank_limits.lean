module

public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.prop_as_response_bank_limit_completion
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_affine_inverse_neumann_measurable

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The bank Cauchy supplier specialized to its actual zero-infrared,
root-cube affine inverse-Neumann coordinate. -/
theorem aux_actual_root_inverse_neumann_cauchy
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
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        ∀ (e : Homogenization.Vec d) (a b : ℝ), 0 < a → 0 < b →
          ∃ J : ℕ, ∀ N N' : ℕ, J ≤ N → J ≤ N' →
            (chaosSampleLaw M).toMeasure
              {om | a < |aux_matched_affine_finite_response M e true N om -
                aux_matched_affine_finite_response M e true N' om|} ≤
              ENNReal.ofReal b := by
  obtain ⟨delta0, Cgeom, hdelta0, hCgeom, hc⟩ :=
    prop_as_response_bank_cauchy d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H HI hdelta e a b ha hb
  let Q := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  have hcb := hc M Rm Sreg It H HI hdelta
    (0 : SpatialCoordinates d) 1 (by norm_num)
    ⟨0, by norm_num⟩
    (fun _ => (0 : ℝ)) (by fun_prop)
    (0 : weakSobolevGraph Q) (by
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))]
        with x hx
      simpa only [ZeroMemClass.coe_zero, Prod.fst_zero, Pi.zero_apply] using hx)
    (0 : DomainL2 Q) (0 : DomainL2 Q) 0 0
    (by norm_num) (by norm_num)
    (by
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))]
        with x hx
      rw [hx]
      norm_num)
    (by
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))]
        with x hx
      rw [hx]
      norm_num)
    (by
      have hz := Lp.coeFn_zero ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))
      calc
        (∫ x in (Q : Set (SpatialCoordinates d)), ((0 : DomainL2 Q) : SpatialCoordinates d → ℝ) x) =
            ∫ x in (Q : Set (SpatialCoordinates d)), (0 : ℝ) := integral_congr_ae hz
        _ = 0 := by simp) e
  have hraw := hcb.2.2 false ⟨3, by omega⟩ a b ha hb
  simpa [aux_matched_affine_finite_response] using! hraw

/-- The measurable completion of the actual root inverse-Neumann bank coordinate. -/
theorem aux_actual_root_inverse_neumann_limit
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
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        ∀ (e : Homogenization.Vec d),
          ∃ Z : BilateralField d → ℝ,
            Measurable Z ∧ (∀ om, 0 ≤ Z om) ∧
            TendstoInMeasure (chaosSampleLaw M).toMeasure
              (aux_matched_affine_finite_response M e true) atTop Z := by
  obtain ⟨delta0, hdelta0, hc⟩ :=
    aux_actual_root_inverse_neumann_cauchy d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H HI hdelta e
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let F : Unit → ℕ → BilateralField d → ℝ :=
    fun _ N => aux_matched_affine_finite_response M e true N
  have hmeas : ∀ i N, Measurable (F i N) := by
    intro i N
    exact lem_as_coarse_shallow_grid_affine_inverse_neumann_measurable M N e
  have hnonneg : ∀ i N om, 0 ≤ F i N om := by
    intro i N om
    change 0 ≤ affineInverseNeumannResponse (aux_matched_root_poincare (d := d)).2
      (cutoffPositiveCoefficient M (fun _ => 0) om N
        (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)) e
    exact inverseResponse_nonneg
      (meanZeroResponseSpace (aux_matched_root_poincare (d := d)).2)
      (cutoffPositiveCoefficient M (fun _ => 0) om N
        (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1))
      ((affineNeumannLoad e).comp
        (subspaceGradient (meanZeroSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)))))
  have hC : ∀ i : Unit, ∀ a b : ℝ, 0 < a → 0 < b →
      ∃ J : ℕ, ∀ N N' : ℕ, J ≤ N → J ≤ N' →
        P {om | a < |F i N om - F i N' om|} ≤ ENNReal.ofReal b := by
    intro i a b ha hb
    exact hc M Rm Sreg It H HI hdelta e a b ha hb
  obtain ⟨L, hLmeas, hLnonneg, hLconv⟩ :=
    prop_as_response_bank_limit_completion P F hmeas hnonneg hC
  exact ⟨L (), hLmeas (), hLnonneg (), hLconv ()⟩

/-- The actual root affine Dirichlet response is the first bank coordinate. -/
theorem aux_actual_root_dirichlet_cauchy
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
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        ∀ (e : Homogenization.Vec d) (a b : ℝ), 0 < a → 0 < b →
          ∃ J : ℕ, ∀ N N' : ℕ, J ≤ N → J ≤ N' →
            (chaosSampleLaw M).toMeasure
              {om | a < |aux_matched_affine_finite_response M e false N om -
                aux_matched_affine_finite_response M e false N' om|} ≤
              ENNReal.ofReal b := by
  obtain ⟨delta0, Cgeom, hdelta0, hCgeom, hc⟩ :=
    prop_as_response_bank_cauchy d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H HI hdelta e a b ha hb
  let Q := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let hQ := centeredCube_isBounded (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)
  let bd : weakSobolevGraph Q := affineSobolev hQ e 0
  have htrace : ((bd : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Q : Set (SpatialCoordinates d))] affineSlope e := by
    simpa [bd, affineSobolev, affineSobolevData] using
      (affineL2_coeFn hQ e 0)
  have hcb := hc M Rm Sreg It H HI hdelta
    (0 : SpatialCoordinates d) 1 (by norm_num)
    ⟨0, by norm_num⟩
    (affineSlope e) (ContinuousLinearMap.contDiff _)
    bd htrace
    (0 : DomainL2 Q) (0 : DomainL2 Q) 0 0
    (by norm_num) (by norm_num)
    (by
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))]
        with x hx
      rw [hx]
      norm_num)
    (by
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))]
        with x hx
      rw [hx]
      norm_num)
    (by
      have hz := Lp.coeFn_zero ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))
      calc
        (∫ x in (Q : Set (SpatialCoordinates d)), ((0 : DomainL2 Q) : SpatialCoordinates d → ℝ) x) =
            ∫ x in (Q : Set (SpatialCoordinates d)), (0 : ℝ) := integral_congr_ae hz
        _ = 0 := by simp) e
  have hraw := hcb.2.2 false ⟨0, by omega⟩ a b ha hb
  simpa [aux_matched_affine_finite_response, bd] using! hraw

/-- Measurable completion of the actual root affine Dirichlet coordinate. -/
theorem aux_actual_root_dirichlet_limit
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
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        ∀ (e : Homogenization.Vec d),
          ∃ Z : BilateralField d → ℝ,
            Measurable Z ∧ (∀ om, 0 ≤ Z om) ∧
            TendstoInMeasure (chaosSampleLaw M).toMeasure
              (aux_matched_affine_finite_response M e false) atTop Z := by
  obtain ⟨delta0, hdelta0, hc⟩ :=
    aux_actual_root_dirichlet_cauchy d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H HI hdelta e
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let F : Unit → ℕ → BilateralField d → ℝ :=
    fun _ N => aux_matched_affine_finite_response M e false N
  have hmeas : ∀ i N, Measurable (F i N) := by
    intro i N
    simpa [F, aux_matched_affine_finite_response] using!
      (lem_as_coarse_shallow_grid_affine_dirichlet_measurable M N e)
  have hnonneg : ∀ i N om, 0 ≤ F i N om := by
    intro i N om
    change 0 ≤ affineDirichletResponse
      (centeredCube_isBounded (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1))
      (aux_matched_root_poincare (d := d)).1
      (cutoffPositiveCoefficient M (fun _ => 0) om N
        (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)) e
    exact dirichletResponse_nonneg
      (killedResponseSpace (aux_matched_root_poincare (d := d)).1)
      (cutoffPositiveCoefficient M (fun _ => 0) om N
        (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1))
      (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d)
        (by norm_num : (0 : ℝ) < 1)) e 0)
  have hC : ∀ i : Unit, ∀ a b : ℝ, 0 < a → 0 < b →
      ∃ J : ℕ, ∀ N N' : ℕ, J ≤ N → J ≤ N' →
        P {om | a < |F i N om - F i N' om|} ≤ ENNReal.ofReal b := by
    intro i a b ha hb
    exact hc M Rm Sreg It H HI hdelta e a b ha hb
  obtain ⟨L, hLmeas, hLnonneg, hLconv⟩ :=
    prop_as_response_bank_limit_completion P F hmeas hnonneg hC
  exact ⟨L (), hLmeas (), hLnonneg (), hLconv ()⟩

/-- Both actual zero-infrared affine root responses have measurable nonnegative
limits in measure under the response-bank supplier's disorder threshold. -/
theorem lem_as_coarse_shallow_grid_actual_root_bank_limits
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
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        ∀ (e : Homogenization.Vec d),
          ∃ ZD ZN : BilateralField d → ℝ,
            Measurable ZD ∧ (∀ om, 0 ≤ ZD om) ∧
            TendstoInMeasure (chaosSampleLaw M).toMeasure
              (aux_matched_affine_finite_response M e false) atTop ZD ∧
            Measurable ZN ∧ (∀ om, 0 ≤ ZN om) ∧
            TendstoInMeasure (chaosSampleLaw M).toMeasure
              (aux_matched_affine_finite_response M e true) atTop ZN := by
  obtain ⟨δD, hδD, hD⟩ :=
    aux_actual_root_dirichlet_limit d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  obtain ⟨δN, hδN, hN⟩ :=
    aux_actual_root_inverse_neumann_limit d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  refine ⟨min δD δN, lt_min hδD hδN, ?_⟩
  intro M Rm Sreg It H HI hdelta e
  have hMD : M.delta ≤ min 1 δD :=
    hdelta.trans (min_le_min_left 1 (min_le_left δD δN))
  have hMN : M.delta ≤ min 1 δN :=
    hdelta.trans (min_le_min_left 1 (min_le_right δD δN))
  obtain ⟨ZD, hZD, hZDpos, hZDconv⟩ := hD M Rm Sreg It H HI hMD e
  obtain ⟨ZN, hZN, hZNpos, hZNconv⟩ := hN M Rm Sreg It H HI hMN e
  exact ⟨ZD, ZN, hZD, hZDpos, hZDconv, hZN, hZNpos, hZNconv⟩

end SubdiffusiveProcess.Paper
