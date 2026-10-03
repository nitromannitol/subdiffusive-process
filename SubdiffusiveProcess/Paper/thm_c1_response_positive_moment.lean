module

public import SubdiffusiveProcess.Paper.lane4_lambda_inv_moments_uniform
public import SubdiffusiveProcess.Paper.rem_bank_response_moments

@[expose] public section

/-! The first moment of a killed inverse response on the unit cube is bounded
uniformly over cutoffs and small-disorder models. No reciprocal bound is asserted. -/

open MeasureTheory TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper
noncomputable section

/-- The coarse inverse-response bound is invariant under the proof fields of a killed space. -/
theorem aux_thm_c1_response_positive_moment_pointwise {d : ℕ} (hd : 2 ≤ d)
    (E : in_J d) (P : in_poincare d hd E)
    (S : ResponseSpace (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hS : S.space = killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (f : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) :
    inverseResponse S a ((sobolevVolumeLoad f).comp S.space.subtypeL) ≤
      (‖f‖ * P.C) ^ 2 * (E.lam 0 1 one_pos a 0 1 (1 / 8) 1)⁻¹ := by
  rcases S with ⟨V, hV, hclosed, hP⟩
  change V = killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos) at hS
  subst V
  have h := aux_rem_bank_response_moments_inverse_le hd E P 0 1 one_pos hP a f
  simp only [mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (aux_rem_bank_response_moments_lam_inv_mono E 0 1 one_pos a (1 / 8) (by norm_num))
    (sq_nonneg _))

/-- The positive response moment has one bound chosen before the model and cutoff. -/
theorem thm_c1_response_positive_moment {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (f : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta →
      ∀ (S : ResponseSpace (centeredCube (0 : SpatialCoordinates d) 1 one_pos)),
      S.space = killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos) →
      ∀ N : ℕ,
        MemLp (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N 0 one_pos)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)) 1 (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N 0 one_pos)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)) 1 (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal C := by
  obtain ⟨delta, hdelta, K, hK, h⟩ := aux_lane4_lambda_inv_moments_uniform_unconditional
    d hd E (1 / 8) (by constructor <;> norm_num) 0 1 one_pos le_rfl 1 le_rfl
  let A := (‖f‖ * P.C) ^ 2
  refine ⟨delta, max 1 (A * K), hdelta, lt_max_of_lt_left one_pos, ?_⟩
  intro M H hH hMd S hS N
  obtain ⟨hmem, hnorm⟩ := h M H hH hMd N
  rw [ENNReal.ofReal_one] at hmem hnorm
  have hout := aux_rem_bank_response_moments_memLp_of_envelope (chaosSampleLaw M).toMeasure
    (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N 0 one_pos)
      ((sobolevVolumeLoad f).comp S.space.subtypeL))
    (fun om => (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H om N 0 one_pos)
      0 1 (1 / 8) 1)⁻¹) A K (sq_nonneg _) 1
    (aux_rem_bank_response_moments_measurable_inverseResponse M H hH.1 N 0 one_pos S _).aestronglyMeasurable
    hmem hnorm (Filter.Eventually.of_forall fun om => ?_)
  · exact ⟨hout.1, hout.2.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩
  · refine ⟨inverseResponse_nonneg _ _ _, inv_nonneg.mpr (E.lam_pos _ _ _ _ _ _ _ _).le, ?_⟩
    rw [mul_comm]
    exact aux_thm_c1_response_positive_moment_pointwise hd E P S hS _ f

end
end Paper
