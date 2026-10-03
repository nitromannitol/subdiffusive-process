module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_root_bank_limits
public import SubdiffusiveProcess.Paper.prop_as_response_bank_limit_tail

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The paper's quantitative two-cutoff comparison, specialized to the
actual zero-infrared root inverse-Neumann affine response. -/
theorem aux_actual_root_inverse_neumann_pair_tail
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
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 Cgeom : ℝ, 0 < delta0 ∧ 0 < Cgeom ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        ∀ (e : Homogenization.Vec d) (eps : ℝ), 0 < eps →
          ∃ Ce ce : ℝ, ∃ Ne : ℕ, 0 < Ce ∧ 0 < ce ∧
            ∀ N : ℕ, Ne ≤ N →
              ∃ M0 : ℕ, N ≤ M0 ∧ ∀ N' : ℕ, M0 ≤ N' →
                (chaosSampleLaw M).toMeasure
                  {om | Cgeom * eps * aux_matched_affine_finite_response M e true N om +
                    Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                    |aux_matched_affine_finite_response M e true N om -
                     aux_matched_affine_finite_response M e true N' om|} ≤
                  ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
  obtain ⟨delta0, Cgeom, hdelta0, hCgeom, hc⟩ :=
    prop_as_response_bank_cauchy d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  refine ⟨delta0, Cgeom, hdelta0, hCgeom, ?_⟩
  intro M Rm Sreg It H HI hdelta e eps heps
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
  obtain ⟨Ce, ce, Ne, hCe, hce, hNe⟩ := hcb.2.1 eps heps
  refine ⟨Ce, ce, Ne, hCe, hce, ?_⟩
  intro N hN
  obtain ⟨M0, hNM0, hM0⟩ := hNe N hN
  refine ⟨M0, hNM0, ?_⟩
  intro N' hN'
  exact hM0 N' hN' false ⟨3, by omega⟩

/-- The paper's quantitative two-cutoff comparison, specialized to the
actual zero-infrared root Dirichlet affine response. -/
theorem aux_actual_root_dirichlet_pair_tail
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
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 Cgeom : ℝ, 0 < delta0 ∧ 0 < Cgeom ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        ∀ (e : Homogenization.Vec d) (eps : ℝ), 0 < eps →
          ∃ Ce ce : ℝ, ∃ Ne : ℕ, 0 < Ce ∧ 0 < ce ∧
            ∀ N : ℕ, Ne ≤ N →
              ∃ M0 : ℕ, N ≤ M0 ∧ ∀ N' : ℕ, M0 ≤ N' →
                (chaosSampleLaw M).toMeasure
                  {om | Cgeom * eps * aux_matched_affine_finite_response M e false N om +
                    Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                    |aux_matched_affine_finite_response M e false N om -
                     aux_matched_affine_finite_response M e false N' om|} ≤
                  ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
  obtain ⟨delta0, Cgeom, hdelta0, hCgeom, hc⟩ :=
    prop_as_response_bank_cauchy d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  refine ⟨delta0, Cgeom, hdelta0, hCgeom, ?_⟩
  intro M Rm Sreg It H HI hdelta e eps heps
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
  obtain ⟨Ce, ce, Ne, hCe, hce, hNe⟩ := hcb.2.1 eps heps
  refine ⟨Ce, ce, Ne, hCe, hce, ?_⟩
  intro N hN
  obtain ⟨M0, hNM0, hM0⟩ := hNe N hN
  refine ⟨M0, hNM0, ?_⟩
  intro N' hN'
  exact hM0 N' hN' false ⟨0, by omega⟩

/-- Transfer a concrete two-cutoff affine comparison to its already
constructed measurable response-bank limit. -/
theorem aux_actual_root_affine_tail_transfer {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (e : Homogenization.Vec d)
    (inverse : Bool) (Z : BilateralField d → ℝ)
    (hZ : Measurable Z) (hZpos : ∀ om, 0 ≤ Z om)
    (hconv : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (aux_matched_affine_finite_response M e inverse) atTop Z)
    (Cgeom : ℝ) (hCgeom : 0 < Cgeom)
    (hpair : ∀ eps : ℝ, 0 < eps →
      ∃ Ce ce : ℝ, ∃ Ne : ℕ, 0 < Ce ∧ 0 < ce ∧
        ∀ N : ℕ, Ne ≤ N →
          ∃ M0 : ℕ, N ≤ M0 ∧ ∀ N' : ℕ, M0 ≤ N' →
            (chaosSampleLaw M).toMeasure
              {om | Cgeom * eps * aux_matched_affine_finite_response M e inverse N om +
                Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                |aux_matched_affine_finite_response M e inverse N om -
                 aux_matched_affine_finite_response M e inverse N' om|} ≤
              ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))))) :
    ∀ eps : ℝ, 0 < eps →
      ∃ Ce ce : ℝ, ∃ Ne : ℕ, 0 < Ce ∧ 0 < ce ∧
        ∀ N : ℕ, Ne ≤ N →
          (chaosSampleLaw M).toMeasure
            {om | Cgeom * eps * Z om + Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
              |aux_matched_affine_finite_response M e inverse N om - Z om|} ≤
            ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
  let F : Unit → ℕ → BilateralField d → ℝ :=
    fun _ N => aux_matched_affine_finite_response M e inverse N
  let L : Unit → BilateralField d → ℝ := fun _ => Z
  have hfinite : ∀ i N, Measurable (F i N) := by
    intro i N
    cases inverse with
    | false =>
        exact lem_as_coarse_shallow_grid_affine_dirichlet_measurable M N e
    | true =>
        exact lem_as_coarse_shallow_grid_affine_inverse_neumann_measurable M N e
  have hnonneg : ∀ i N om, 0 ≤ F i N om := by
    intro i N om
    cases inverse with
    | false =>
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
    | true =>
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
  have ht := prop_as_response_bank_limit_tail
    (chaosSampleLaw M).toMeasure F L hfinite
    (fun _ => hZ) hnonneg (fun _ => hZpos)
    Cgeom hCgeom (fun _ => hpair) (fun _ => hconv)
  exact ht ()

/-- Quantitative limit tails for both actual zero-infrared root affine bank
coordinates. The slope is the coordinate vector used by the response bank. -/
theorem lem_as_coarse_shallow_grid_actual_bank_limit_tail
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
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∀ inverse : Bool, ∃ delta0 Cgeom : ℝ, 0 < delta0 ∧ 0 < Cgeom ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (HI : InfraredCharacterization M H),
        M.delta ≤ min 1 delta0 →
        ∀ i : Fin d, ∃ Z : BilateralField d → ℝ,
          Measurable Z ∧ (∀ om, 0 ≤ Z om) ∧
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (aux_matched_affine_finite_response M (Pi.single i 1) inverse) atTop Z ∧
          ∀ eps : ℝ, 0 < eps →
            ∃ Ce ce : ℝ, ∃ Ne : ℕ, 0 < Ce ∧ 0 < ce ∧
              ∀ N : ℕ, Ne ≤ N →
                (chaosSampleLaw M).toMeasure
                  {om | Cgeom * eps * Z om +
                    Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                    |aux_matched_affine_finite_response M (Pi.single i 1) inverse N om - Z om|} ≤
                  ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
  intro inverse
  obtain ⟨δL, hδL, hL⟩ :=
    lem_as_coarse_shallow_grid_actual_root_bank_limits d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  cases inverse with
  | false =>
      obtain ⟨δP, Cg, hδP, hCg, hP⟩ :=
        aux_actual_root_dirichlet_pair_tail d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
      refine ⟨min δL δP, Cg, lt_min hδL hδP, hCg, ?_⟩
      intro M Rm Sreg It H HI hdelta i
      have hML : M.delta ≤ min 1 δL :=
        hdelta.trans (min_le_min_left 1 (min_le_left δL δP))
      have hMP : M.delta ≤ min 1 δP :=
        hdelta.trans (min_le_min_left 1 (min_le_right δL δP))
      obtain ⟨ZD, ZN, hZD, hZDpos, hZDconv, hZN, hZNpos, hZNconv⟩ :=
        hL M Rm Sreg It H HI hML (Pi.single i 1)
      refine ⟨ZD, hZD, hZDpos, hZDconv, ?_⟩
      apply aux_actual_root_affine_tail_transfer M (Pi.single i 1) false ZD
        hZD hZDpos hZDconv Cg hCg
      exact hP M Rm Sreg It H HI hMP (Pi.single i 1)
  | true =>
      obtain ⟨δP, Cg, hδP, hCg, hP⟩ :=
        aux_actual_root_inverse_neumann_pair_tail d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
      refine ⟨min δL δP, Cg, lt_min hδL hδP, hCg, ?_⟩
      intro M Rm Sreg It H HI hdelta i
      have hML : M.delta ≤ min 1 δL :=
        hdelta.trans (min_le_min_left 1 (min_le_left δL δP))
      have hMP : M.delta ≤ min 1 δP :=
        hdelta.trans (min_le_min_left 1 (min_le_right δL δP))
      obtain ⟨ZD, ZN, hZD, hZDpos, hZDconv, hZN, hZNpos, hZNconv⟩ :=
        hL M Rm Sreg It H HI hML (Pi.single i 1)
      refine ⟨ZN, hZN, hZNpos, hZNconv, ?_⟩
      apply aux_actual_root_affine_tail_transfer M (Pi.single i 1) true ZN
        hZN hZNpos hZNconv Cg hCg
      exact hP M Rm Sreg It H HI hMP (Pi.single i 1)

end Paper





