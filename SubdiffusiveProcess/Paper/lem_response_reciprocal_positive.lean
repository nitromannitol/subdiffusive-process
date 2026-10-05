module

public import SubdiffusiveProcess.Paper.lane4_lambda_inv_moments_uniform
public import SubdiffusiveProcess.Paper.rem_bank_response_moments

@[expose] public section

/-! The positive moments of the quadratic form `⟨f, G_N^Q f⟩` of a cube `Q` of side at most one:
the killed Poincaré inequality bounds the form by the inverse of the lower ellipticity, whose
moments are uniform in the cutoff and in the small-disorder model. -/

open MeasureTheory TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- The inverse response of a source on a killed cube is bounded by the inverse lower ellipticity. -/
theorem aux_lem_response_reciprocal_positive_pointwise {d : ℕ} (hd : 2 ≤ d)
    (E : in_J d) (P : in_poincare d hd E) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : PositiveCoefficient (centeredCube z r hr))
    (f : DomainL2 (centeredCube z r hr)) :
    inverseResponse S a ((sobolevVolumeLoad f).comp S.space.subtypeL) ≤
      (‖f‖ * (P.C * r)) ^ 2 * (E.lam z r hr a z r (1 / 8) 1)⁻¹ := by
  rcases S with ⟨V, hV, hclosed, hP⟩
  change V = killedSobolevGraph (centeredCube z r hr) at hS
  subst V
  have h := aux_rem_bank_response_moments_inverse_le hd E P z r hr hP a f
  exact h.trans (mul_le_mul_of_nonneg_left
    (aux_rem_bank_response_moments_lam_inv_mono E z r hr a (1 / 8) (by norm_num))
    (sq_nonneg _))

/-- The positive `L^p` moment of the quadratic form of a source on a cube of side at most one has
one bound chosen before the model and the cutoff. -/
theorem lem_response_reciprocal_positive {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : DomainL2 (centeredCube z r hr)) (p : ℝ) (hp : 1 ≤ p) :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta →
      ∀ (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ N : ℕ,
        MemLp (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N z hr)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N z hr)
          ((sobolevVolumeLoad f).comp S.space.subtypeL)) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
  obtain ⟨delta, hdelta, K, hK, h⟩ := aux_lane4_lambda_inv_moments_uniform_unconditional
    d hd E (1 / 8) (by constructor <;> norm_num) z r hr hr1 p hp
  let A := (‖f‖ * (P.C * r)) ^ 2
  refine ⟨delta, max 1 (A * K), hdelta, lt_max_of_lt_left one_pos, ?_⟩
  intro M H hH hMd S hS N
  obtain ⟨hmem, hnorm⟩ := h M H hH hMd N
  have hout := aux_rem_bank_response_moments_memLp_of_envelope (chaosSampleLaw M).toMeasure
    (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N z hr)
      ((sobolevVolumeLoad f).comp S.space.subtypeL))
    (fun om => (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8) 1)⁻¹)
    A K (sq_nonneg _) (ENNReal.ofReal p)
    (aux_rem_bank_response_moments_measurable_inverseResponse M H hH.1 N z hr S _).aestronglyMeasurable
    hmem hnorm (Filter.Eventually.of_forall fun om => ?_)
  · exact ⟨hout.1, hout.2.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩
  · refine ⟨inverseResponse_nonneg _ _ _, inv_nonneg.mpr (E.lam_pos _ _ _ _ _ _ _ _).le, ?_⟩
    rw [mul_comm]
    exact aux_lem_response_reciprocal_positive_pointwise hd E P z r hr S hS _ f

end
end SubdiffusiveProcess.Paper
