import SubdiffusiveProcess.Paper.lem_as_regularity_defect_carrier

/-! The unit maximal-defect comparison transfers to every physical atom
with the same constants, using its remaining cutoff and the common scale
law. This module does not yet take a union over retained cells.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace Paper

/-- The quantitative two-cutoff comparison is uniform over physical primitive atoms. -/
theorem lem_as_regularity_atom_pair_tail
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
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ eps : ℝ, 0 < eps → ∃ C c : ℝ, ∃ N0 : ℕ, 0 < C ∧ 0 < c ∧
        ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (l : ℤ) (y : SpatialCoordinates d) (N : ℕ),
          0 ≤ l + (N : ℤ) → N0 ≤ (l + (N : ℤ)).toNat →
          ∃ M0 : ℕ, N ≤ M0 ∧ ∀ N' : ℕ, M0 ≤ N' →
            (chaosSampleLaw M).toMeasure {omega |
              eps * (1 + aux_prefix_rraw_atom M eta N l y omega) <
                |aux_prefix_rraw_atom M eta N l y omega -
                  aux_prefix_rraw_atom M eta N' l y omega|} ≤
              ENNReal.ofReal (C * (3 : ℝ) ^ (-c * ((l + (N : ℤ)).toNat : ℝ))) := by
  obtain ⟨delta0, hdelta0, hroot⟩ := lem_as_regularity_defect_pair_tail
    d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hH hdelta eps heps
  obtain ⟨C, c, N0, hC, hc, htail⟩ := hroot M Rm Sreg It H hH hdelta eps heps
  refine ⟨C, c, N0, hC, hc, ?_⟩
  intro eta hEta l y N hN hN0
  obtain ⟨Mroot, hNMroot, hMroot⟩ := htail (l + (N : ℤ)).toNat hN0
  refine ⟨N + Mroot, Nat.le_add_right N Mroot, ?_⟩
  intro N' hN'
  have hN'0 : 0 ≤ l + (N' : ℤ) := by omega
  have hfuture : Mroot ≤ (l + (N' : ℤ)).toNat := by omega
  let bad : Set (BilateralField d) := {omega |
    eps * (1 + aux_lem_as_regularity_defect_pair_tail_value M (l + (N : ℤ)).toNat omega) <
      |aux_lem_as_regularity_defect_pair_tail_value M (l + (N : ℤ)).toNat omega -
        aux_lem_as_regularity_defect_pair_tail_value M (l + (N' : ℤ)).toNat omega|}
  have hmeas : MeasurableSet bad := measurableSet_lt
    (measurable_const.mul (measurable_const.add
      (aux_lem_as_regularity_defect_carrier_measurable M _)))
    (((aux_lem_as_regularity_defect_carrier_measurable M _).sub
      (aux_lem_as_regularity_defect_carrier_measurable M _)).abs)
  have hid : {omega |
      eps * (1 + aux_prefix_rraw_atom M eta N l y omega) <
        |aux_prefix_rraw_atom M eta N l y omega - aux_prefix_rraw_atom M eta N' l y omega|}
      =ᵐ[(chaosSampleLaw M).toMeasure]
        aux_lem_prefix_limit_atom_extraction_shift l y ⁻¹' bad := by
    filter_upwards [lem_as_regularity_defect_carrier M eta hEta l y] with omega homega
    change (eps * (1 + aux_prefix_rraw_atom M eta N l y omega) <
      |aux_prefix_rraw_atom M eta N l y omega - aux_prefix_rraw_atom M eta N' l y omega|) =
      (eps * (1 + aux_lem_as_regularity_defect_pair_tail_value M (l + (N : ℤ)).toNat
          (aux_lem_prefix_limit_atom_extraction_shift l y omega)) <
        |aux_lem_as_regularity_defect_pair_tail_value M (l + (N : ℤ)).toNat
            (aux_lem_prefix_limit_atom_extraction_shift l y omega) -
          aux_lem_as_regularity_defect_pair_tail_value M (l + (N' : ℤ)).toNat
            (aux_lem_prefix_limit_atom_extraction_shift l y omega)|)
    rw [homega N hN, homega N' hN'0]
  rw [measure_congr hid,
    (aux_lem_prefix_limit_atom_extraction_shift_mp M l y).measure_preimage hmeas.nullMeasurableSet]
  exact hMroot _ hfuture

end Paper
