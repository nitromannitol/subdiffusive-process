import SubdiffusiveProcess.Paper.lem_band
import SubdiffusiveProcess.Probability.FirstMomentTail

/-! Uniform first-moment tails for the discarded response score and the
initial-layer term. The response moment order and disorder threshold are
chosen before the model. Growing-catalogue summability is handled separately.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- The initial-layer term has the explicit first-moment bound inherited from its second moment. -/
theorem aux_lem_as_regularity_residual_tails_initial {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s : ℝ)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N k : ℕ) (w : SpatialCoordinates d) :
    eLpNorm (fun omega =>
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w (eta N omega)).toReal)
      1 (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * (aux_psf_sigma M *
        (2 * (2 + ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3)))) := by
  have hm := (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt234_aestronglyMeasurable
    M s eta hEta N k w).2.1
  have hbank := aux_lem_prefix_limit_actual_coordinate_cauchy_eta_bank_eLpNorm_linear
    M eta hEta (aux_lem_prefix_limit_actual_coordinate_cauchy_eta_bank_even_moment_log
      M eta hEta)
  have hb := aux_lem_prefix_limit_actual_coordinate_cauchy_t3_eLpNorm_le M s eta hEta
    hbank N k w 1 le_rfl
  have he := eLpNorm_le_eLpNorm_of_exponent_le (f := fun omega =>
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w (eta N omega)).toReal)
    (show (1 : ℝ≥0∞) ≤ ((2 * 1 : ℕ) : ℝ≥0∞) by norm_num) hm
  simpa only [Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num] using he.trans hb

/-- Two explicit residual-event tails hold uniformly over cutoffs, radii, centres, and retained depths. -/
theorem lem_as_regularity_residual_tails (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (s q : ℝ) (hq : 1 ≤ q) (hsq : 8 * (d : ℝ) < s * q) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ eta : ℕ → BilateralField d → PotentialSample d,
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
            omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (N k : ℕ) (w : SpatialCoordinates d) (H : ℕ) (tol : ℝ), 0 < tol →
          ((chaosSampleLaw M).toMeasure {omega | tol <
            (aux_prefix_rraw_tail M s (eta N omega) k w H).toReal} ≤
            ENNReal.ofReal (B * aux_prefix_rraw_rho d s q ^ (H + 1) / tol)) ∧
          ((chaosSampleLaw M).toMeasure {omega | tol <
            (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w (eta N omega)).toReal} ≤
            ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ)) * (aux_psf_sigma M *
              (2 * (2 + ((d * (k + 1) + 1 : ℕ) : ℝ) * Real.log 3))) / tol)) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  obtain ⟨hdelta0, hmoment⟩ := aux_lem_band_tailq_delta0_spec d q hq
  refine ⟨aux_lem_band_tailq_delta0 d q hq, hdelta0, ?_⟩
  intro M hM
  let b : ℝ := aux_prefix_rraw_C d * q * Real.log (2 + q) * M.delta ^ 2
  have hb : 0 ≤ b := by
    apply mul_nonneg _ (sq_nonneg _)
    exact mul_nonneg (mul_nonneg (aux_prefix_rraw_C_spec d).1.le hq0.le)
      (Real.log_nonneg (by linarith only [hq]))
  have hK := aux_prefix_rraw_K_nonneg d s q hq0 hsq
  refine ⟨aux_prefix_rraw_K d s q * b, mul_nonneg hK hb, ?_⟩
  intro eta hEta N k w H tol htol
  have hRm : AEStronglyMeasurable (fun omega =>
      (aux_prefix_rraw_tail M s (eta N omega) k w H).toReal)
      (chaosSampleLaw M).toMeasure :=
    ((ENNReal.measurable_toReal.comp (aux_prefix_rraw_tail_measurable M s k w H)).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable
  have hRbound := (aux_prefix_rraw_tail_eLpNorm_le M s eta hEta q b hq
    (hmoment M M.shellPrefix.delta_pos hM) N k w H).trans
      (aux_prefix_rraw_tail_numeric d s q hq0 hsq b hb H k)
  have hRone := (eLpNorm_le_eLpNorm_of_exponent_le
    (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal q by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq) hRm).trans hRbound
  have hBR : 0 ≤ aux_prefix_rraw_K d s q * aux_prefix_rraw_rho d s q ^ (H + 1) * b :=
    mul_nonneg (mul_nonneg hK (pow_nonneg (aux_prefix_rraw_rho_pos d s q).le _)) hb
  constructor
  · have ht := measure_gt_le_of_first_moment (chaosSampleLaw M).toMeasure _ hRm
      tol _ htol hBR hRone
    convert ht using 1 <;> congr 1 <;> ring
  · have hTm := (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt234_aestronglyMeasurable
      M s eta hEta N k w).2.1
    apply measure_gt_le_of_first_moment (chaosSampleLaw M).toMeasure _ hTm tol _ htol
    · have hl : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have hsig := (aux_psf_sigma_pos M).le
      positivity
    · exact aux_lem_as_regularity_residual_tails_initial M s eta hEta N k w

end Paper
