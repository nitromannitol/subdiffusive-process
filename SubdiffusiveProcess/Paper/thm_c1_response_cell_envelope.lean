module

public import SubdiffusiveProcess.Paper.lem_extension_cell_moment_uniform

@[expose] public section

/-! Uniform first moments on every cell of one fixed mesh, including cutoffs
below the mesh depth. No inverse-response moment is asserted here. -/

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper
noncomputable section

/-- The positive ellipticity envelope attached to a cell in the unit root. -/
def aux_thm_c1_response_cell_envelope_field {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (w : SpatialCoordinates d) (k N : ℕ) (om : BilateralField d) : ℝ :=
  E.Lam 0 1 one_pos (cutoffPositiveCoefficient M H om N 0 one_pos)
      w ((3 : ℝ) ^ (-(k : ℤ))) (1 / 16) 2 +
    (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H om N 0 one_pos)
      w ((3 : ℝ) ^ (-(k : ℤ))) (1 / 16) 2)⁻¹

/-- The cell envelope is pointwise nonnegative. -/
theorem aux_thm_c1_response_cell_envelope_nonneg {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (w : SpatialCoordinates d) (k N : ℕ) (om : BilateralField d) :
    0 ≤ aux_thm_c1_response_cell_envelope_field E M H w k N om :=
  add_nonneg (E.Lam_pos _ _ _ _ _ _ _ _).le
    (inv_nonneg.mpr (E.lam_pos _ _ _ _ _ _ _ _).le)

/-- The upper ellipticity on a cutoff cell is independent of the enclosing root. -/
theorem aux_thm_c1_response_cell_envelope_Lam_eq {d : ℕ} [NeZero d] (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d)
    (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hsub : centeredCube w r hr ≤ centeredCube (0 : SpatialCoordinates d) 1 one_pos) :
    E.Lam w r hr (cutoffPositiveCoefficient M H om N w hr) w r (1 / 16) 2 =
      E.Lam 0 1 one_pos (cutoffPositiveCoefficient M H om N 0 one_pos) w r (1 / 16) 2 := by
  have hs : (1 / 16 : ℝ) ∈ Ioc (0 : ℝ) 1 := by constructor <;> norm_num
  rw [aux_lem_extension_cell_moment_Lam_eq_tsum E w r hr _ w r hr le_rfl _ hs,
    aux_lem_extension_cell_moment_Lam_eq_tsum E 0 1 one_pos _ w r hr hsub _ hs]
  apply tsum_congr
  intro n
  rw [aux_lem_extension_cell_moment_maxB_chart_eq E M H om N w r hr w r hr le_rfl n,
    aux_lem_extension_cell_moment_maxB_chart_eq E M H om N 0 1 one_pos w r hr hsub n]

/-- A fixed mesh has a model-uniform first-moment envelope at every cutoff. -/
theorem thm_c1_response_cell_envelope {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (k : ℕ) :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta →
      ∀ w : SpatialCoordinates d,
      centeredCube w ((3 : ℝ) ^ (-(k : ℤ))) (zpow_pos zero_lt_three _) ≤
        centeredCube (0 : SpatialCoordinates d) 1 one_pos →
      ∀ N : ℕ,
        MemLp (aux_thm_c1_response_cell_envelope_field E M H w k N) 1
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_thm_c1_response_cell_envelope_field E M H w k N) 1
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
  obtain ⟨delta, Cd, hdelt, hCd, Cq, hCq, hmono, h⟩ :=
    aux_lem_extension_cell_moment_uniform_all_cutoffs hd E (3 / 4) 1
      (by constructor <;> norm_num) le_rfl
  let C := Cq delta * Real.exp (Cd * (1 + (1 : ℝ) ^ 2) * delta ^ 2 * k)
  refine ⟨delta, C, hdelt, mul_pos (hCq delta) (Real.exp_pos _), ?_⟩
  intro M H hH hdelta w hcell N
  obtain ⟨hmeas, hnorm⟩ := h M H hH hdelta w N k hcell
  norm_num only [show ((3 / 4 : ℝ) - 1 / 2) / 4 = 1 / 16 by norm_num,
    ENNReal.ofReal_one] at hmeas hnorm
  have hbound : eLpNorm (aux_thm_c1_response_cell_envelope_field E M H w k N) 1
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
    refine hnorm.trans (ENNReal.ofReal_le_ofReal ?_)
    dsimp only [C]
    apply mul_le_mul (hmono M.delta delta M.shellPrefix.delta_pos.le hdelta)
      (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (hCq delta).le
    gcongr
    · norm_num
    · exact M.shellPrefix.delta_pos.le
  exact ⟨hbound.trans_lt ENNReal.ofReal_lt_top, hbound⟩

end
end Paper
