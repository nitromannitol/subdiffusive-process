module

public import SubdiffusiveProcess.Paper.calibResp_integrable
public import SubdiffusiveProcess.Paper.conv_represented_tight_of_bounded

@[expose] public section

/-! Uniform `L¹` bound and tightness of the infrared-free calibration responses on the cubes `Q_{3^k}`,
`k ≥ K0`, uniformly in the cutoff `N` (from the calibration `cor_37`, whose statement only bounds the integral;
the integrability is `calibResp_integrable`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal
noncomputable section
namespace Paper

/-- **Uniform `L¹` bank.**  Below a disorder threshold, from a fixed `K0` on, the normalized responses are within
`1` of `1` in `L¹`, uniformly in the cutoff. -/
theorem aux_calib_response_tight_L1_bank (d : ℕ) (hd : 2 ≤ d) (hJ : in_J d) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ δ0 →
        ∃ K0 : ℕ, ∀ k : ℕ, K0 ≤ k → ∀ N : ℕ,
          ∫ β, |calibResp d hd M k N β /
              (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
                (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal - 1|
            ∂(chaosSampleLaw M).toMeasure ≤ 1 := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨δ0, hδ0, hcor⟩ := cor_37 d hd hJ
  refine ⟨δ0, hδ0, ?_⟩
  intro _ _ M hM
  obtain ⟨K0, hK0⟩ := hcor M hM
    (fun k => centeredCube_killedPoincare (0 : SpatialCoordinates d)
      (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)) (aux_thm_c1_envcal_e0 d (by omega)) 1 one_pos
  refine ⟨K0, fun k hk N => ?_⟩
  have h := hK0 k hk N
  have hsq : ∑ i : Fin d, aux_thm_c1_envcal_e0 d (by omega) i ^ 2 = 1 := by
    have := aux_thm_c1_envcal_e0_sq d (by omega : 0 < d)
    rw [one_pow] at this
    exact this.symm
  simp only [hsq] at h
  exact h

/-- **Tightness of the calibration coordinates.** -/
theorem calib_response_tight (d : ℕ) (hd : 2 ≤ d) (hJ : in_J d) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ δ0 →
        ∃ K0 : ℕ, ∀ k : ℕ, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ N : ℕ,
          (chaosSampleLaw M).toMeasure {β | Mb < |calibResp d hd M (K0 + k) N β|} ≤
            ENNReal.ofReal rho := by
  obtain ⟨δ0, hδ0, hbank⟩ := aux_calib_response_tight_L1_bank d hd hJ
  refine ⟨δ0, hδ0, ?_⟩
  intro _ _ M hM
  obtain ⟨K0, hK0⟩ := hbank M hM
  refine ⟨K0, fun k rho hrho => ?_⟩
  set v : ℝ := (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ (K0 + k))
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) (K0 + k)) : Set (SpatialCoordinates d))).toReal with hv
  have hvpos : 0 < v := aux_thm_c1_envcal_vol_pos _ _ _
  have hint : ∀ N, Integrable (calibResp d hd M (K0 + k) N) (chaosSampleLaw M).toMeasure :=
    fun N => calibResp_integrable d hd M (K0 + k) N
  have hbound : ∀ N, ∫⁻ β, ‖calibResp d hd M (K0 + k) N β‖ₑ ∂(chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * v) := by
    intro N
    have hnn : ∀ β, 0 ≤ calibResp d hd M (K0 + k) N β := aux_calibResp_integrable_nonneg d hd M (K0 + k) N
    have hL1 := hK0 (K0 + k) (Nat.le_add_right _ _) N
    have hint2 : Integrable (fun β => calibResp d hd M (K0 + k) N β / v - 1)
        (chaosSampleLaw M).toMeasure :=
      ((hint N).div_const v).sub (integrable_const 1)
    have hpt : ∀ β, calibResp d hd M (K0 + k) N β ≤
        v * (|calibResp d hd M (K0 + k) N β / v - 1| + 1) := by
      intro β
      have h1 : calibResp d hd M (K0 + k) N β / v ≤
          |calibResp d hd M (K0 + k) N β / v - 1| + 1 := by
        have := le_abs_self (calibResp d hd M (K0 + k) N β / v - 1)
        linarith
      calc calibResp d hd M (K0 + k) N β = v * (calibResp d hd M (K0 + k) N β / v) := by
            field_simp
        _ ≤ v * (|calibResp d hd M (K0 + k) N β / v - 1| + 1) :=
            mul_le_mul_of_nonneg_left h1 hvpos.le
    have hI : ∫ β, calibResp d hd M (K0 + k) N β ∂(chaosSampleLaw M).toMeasure ≤ 2 * v := by
      calc ∫ β, calibResp d hd M (K0 + k) N β ∂(chaosSampleLaw M).toMeasure
          ≤ ∫ β, v * (|calibResp d hd M (K0 + k) N β / v - 1| + 1)
              ∂(chaosSampleLaw M).toMeasure :=
            integral_mono (hint N) ((hint2.abs.add (integrable_const 1)).const_mul v) hpt
        _ = v * (∫ β, |calibResp d hd M (K0 + k) N β / v - 1| ∂(chaosSampleLaw M).toMeasure + 1) := by
            rw [integral_const_mul, integral_add hint2.abs (integrable_const 1)]
            simp
        _ ≤ v * (1 + 1) := mul_le_mul_of_nonneg_left (by linarith) hvpos.le
        _ = 2 * v := by ring
    have hlint : ∫⁻ β, ‖calibResp d hd M (K0 + k) N β‖ₑ ∂(chaosSampleLaw M).toMeasure =
        ENNReal.ofReal (∫ β, calibResp d hd M (K0 + k) N β ∂(chaosSampleLaw M).toMeasure) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hint N) (Eventually.of_forall hnn)]
      refine lintegral_congr fun β => ?_
      rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hnn β)]
    rw [hlint]
    exact ENNReal.ofReal_le_ofReal hI
  obtain ⟨Mb, hMb⟩ := aux_conv_represented_tight_of_bounded_L1_bounded
    (chaosSampleLaw M).toMeasure (fun N => calibResp d hd M (K0 + k) N)
    (fun N => aux_calibResp_integrable_measurable d hd M (K0 + k) N) (2 * v) (by positivity) hbound rho hrho
  exact ⟨Mb, hMb⟩

end Paper
