module

public import SubdiffusiveProcess.Paper.lem_as_regularity_defect_pair_tail
public import SubdiffusiveProcess.Paper.lem_prefix_limit_atom_extraction

@[expose] public section

/-! The maximal affine response defect is the primitive stationary atom.
The identity uses the existing normalized coefficient and physical chart
identities. It supplies no new convergence or mesh estimate.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace Paper

/-- The maximal affine response defect is the existing unit response evaluation minus one. -/
theorem aux_lem_as_regularity_defect_carrier_value {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (omega : BilateralField d) :
    aux_lem_as_regularity_defect_pair_tail_value M N omega =
      aux_lem_prefix_limit_atom_extraction_Rf M N omega - 1 := by
  let g := aux_lem_prefix_limit_atom_extraction_pot M N omega
  let Sphere := {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1}
  let f : Sphere → ℝ := fun e =>
    aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) e
  have hresponse (e : SpatialCoordinates d) :
      (aux_matched_affine_finite_response M e false N omega +
        aux_matched_affine_finite_response M e true N omega) /
        (2 * volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d))) =
        aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) e := by
    rw [show g = aux_lem_prefix_limit_atom_extraction_pot M N omega from rfl,
      aux_lem_prefix_limit_atom_extraction_coef_eq]
    rfl
  have hset : {v : ℝ | ∃ e : SpatialCoordinates d, (∑ i : Fin d, (e i) ^ 2) = 1 ∧
      v = (aux_matched_affine_finite_response M e false N omega +
        aux_matched_affine_finite_response M e true N omega) /
        (2 * volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d))) - 1} = Set.range (fun e => f e - 1) := by
    ext v
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, by rw [hresponse]⟩
    · rintro ⟨e, rfl⟩
      exact ⟨e, e.2, by rw [hresponse]⟩
  have hbdd : BddAbove (Set.range (fun e => f e - 1)) := by
    obtain ⟨B, hB⟩ := aux_lem_prefix_limit_atom_extraction_bdd g
    refine ⟨B - 1, ?_⟩
    rintro _ ⟨e, rfl⟩
    exact sub_le_sub_right (hB ⟨e, rfl⟩) 1
  change sSup _ = aux_lem_prefix_limit_atom_extraction_eval g - 1
  rw [hset]
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨e, rfl⟩
    exact sub_le_sub_right (aux_lem_prefix_limit_atom_extraction_W_le_eval g e) 1
  · apply sub_le_iff_le_add.mpr
    apply ciSup_le
    intro e
    have he := le_csSup hbdd (Set.mem_range_self e)
    change f e ≤ _
    linarith only [he]

/-- The maximal unit response defect is measurable at every cutoff. -/
theorem aux_lem_as_regularity_defect_carrier_measurable {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Measurable (aux_lem_as_regularity_defect_pair_tail_value M N) := by
  have hid : aux_lem_as_regularity_defect_pair_tail_value M N =
      fun omega => aux_lem_prefix_limit_atom_extraction_Rf M N omega - 1 :=
    funext (aux_lem_as_regularity_defect_carrier_value M N)
  rw [hid]
  exact (aux_lem_prefix_limit_atom_extraction_Rf_measurable M N).sub_const 1

/-- Primal-dual response positivity makes the maximal unit defect nonnegative. -/
theorem aux_lem_as_regularity_defect_carrier_nonneg {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (omega : BilateralField d) :
    0 ≤ aux_lem_as_regularity_defect_pair_tail_value M N omega := by
  let g := aux_lem_prefix_limit_atom_extraction_pot M N omega
  obtain ⟨e⟩ := (inferInstance : Nonempty {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1})
  have hpos := affineDiagonalDefect_nonneg
    (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
    (centeredCube_volume_pos (0 : SpatialCoordinates d) one_pos)
    aux_lem_prefix_limit_atom_extraction_poincare.1
    aux_lem_prefix_limit_atom_extraction_poincare.2
    (expPotentialCoefficient g) e.val
  unfold affineDiagonalDefect at hpos
  rw [e.property] at hpos
  have hupper := aux_lem_prefix_limit_atom_extraction_W_le_eval g e
  rw [aux_lem_as_regularity_defect_carrier_value]
  change 0 ≤ aux_lem_prefix_limit_atom_extraction_eval g - 1
  change 0 ≤ aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) e.val - 1
    at hpos
  linarith only [hpos, hupper]

/-- A physical primitive atom is the maximal unit defect in its shifted field. -/
theorem lem_as_regularity_defect_carrier {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (l : ℤ) (y : SpatialCoordinates d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, 0 ≤ l + (N : ℤ) →
      aux_prefix_rraw_atom M eta N l y omega =
        aux_lem_as_regularity_defect_pair_tail_value M (l + (N : ℤ)).toNat
          (aux_lem_prefix_limit_atom_extraction_shift l y omega) := by
  filter_upwards [aux_lem_prefix_limit_atom_extraction_carrier M eta hEta l y] with omega h
  intro N hN
  rw [aux_lem_as_regularity_defect_carrier_value]
  exact h N hN

end Paper
