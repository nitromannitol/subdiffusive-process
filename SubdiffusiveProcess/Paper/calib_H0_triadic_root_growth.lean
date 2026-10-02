import Mathlib
import SubdiffusiveProcess.Paper.calib3_HT
import SubdiffusiveProcess.Paper.calib3_shift
import SubdiffusiveProcess.Paper.calib3_unit_growth
import SubdiffusiveProcess.Paper.prop_growth_large_root
import SubdiffusiveProcess.Paper.in_responses

/-! **Stage 3 of the calibration: `prop_growth` for the infrared-free coefficient on cubes of side `3^j`.**

For `H ≡ 0` (the coefficient `A^0_N` without its infrared factor) and every cube `Q(z, 3^j)`, `j ≥ 1`, the conclusion of
`prop_growth` (energy growth `rad^t` for radii `≤ 1`, and the `C^α` Hölder norm bound, with one random constant of all
prescribed moments) holds.  Proof (paper rescaling of `mfd:prop-growth`, lines 598-617): the scale shift `S_j` maps
`A^0_N(3^j y)` to `c · A^{HT_j}_{N+j}(S_jω)(y)` (`calib3_shift`), the unit-cube growth for the top-block-removed model
`HT_j = -∑_{i<j} ω(-i)` is `calib3_unit_growth`, and the deterministic transfer of `prop_growth_large_root` carries it back. -/

open MeasureTheory Set TopologicalSpace Metric SubdiffusiveProcess SubdiffusiveProcess.Lane4 Filter
open scoped ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

variable {d : ℕ}

/-- The coefficient pullback for `H = 0`: on the dilated unit cube, `A^0_N(r x) = c · A^{HT_j}_{N+j}(S_jω)(s x)`, `r = 3^j s`. -/
theorem aux_calib_H0_triadic_root_growth_pullback [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M) (om : BilateralField d) (j N : ℕ) (hj : 0 < j)
    (z : SpatialCoordinates d) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r = (3 : ℝ) ^ j * s) :
    ∀ᵐ x ∂volume.restrict (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N z hr).val
          (cubeDilation z (r⁻¹ • z) r x) =
        aux_calib3_shift_const M j N *
          (cutoffPositiveCoefficient M (calib3_HT d j) (aux_prop_growth_large_root_scaleShift j om) (N + j)
            (((3 : ℝ) ^ j)⁻¹ • z) hs).val (cubeDilation (((3 : ℝ) ^ j)⁻¹ • z) (r⁻¹ • z) s x) := by
  have hq := Paper.lane4_dilation_quasi_measure_preserving d z (r⁻¹ • z) r hr one_pos
  have hq' := Paper.lane4_dilation_quasi_measure_preserving d (((3 : ℝ) ^ j)⁻¹ • z)
    (r⁻¹ • z) s hs one_pos
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hT' : ∀ x : SpatialCoordinates d,
      cubeDilation (((3 : ℝ) ^ j)⁻¹ • z) (r⁻¹ • z) s x = s • x := by
    intro x
    funext i
    rw [cubeDilation_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hrs]
    field_simp
    ring
  filter_upwards [hq.ae (aux_prop_growth_large_root_cutoffPositiveCoefficient_val_ae M
      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N z hr),
    hq'.ae (aux_prop_growth_large_root_cutoffPositiveCoefficient_val_ae M (calib3_HT d j)
      (aux_prop_growth_large_root_scaleShift j om) (N + j) (((3 : ℝ) ^ j)⁻¹ • z) hs)] with x hx hx'
  rw [hx, hx', aux_prop_growth_large_root_cubeDilation_origin z hr x, hT' x]
  have hrx : r • x = ((3 : ℝ) ^ j) • (s • x) := by rw [smul_smul, hrs]
  rw [hrx]
  exact (calib3_shift M Rm j N hj om (s • x)).1

/-- The deterministic shift constant is dominated by the random envelope `shiftEnv` of `prop_growth_large_root`. -/
theorem aux_calib_H0_triadic_root_growth_env_le [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℕ) (om : BilateralField d) :
    Real.exp ((j : ℝ) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) ≤ aux_prop_growth_large_root_shiftEnv M j om := by
  unfold aux_prop_growth_large_root_shiftEnv
  exact Real.exp_le_exp.2 (by linarith [abs_nonneg (aux_prop_growth_large_root_irAnchor j om)])

/-- **`prop_growth` for the infrared-free coefficient on the cubes `Q(z, 3^j)`, `j ≥ 1`** (Stage 3 of the calibration). -/
theorem calib_H0_triadic_root_growth (d : ℕ) (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : Paper.in_J d) (Pc : Paper.in_poincare d hd Jc) (Xc : Paper.in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd) :
    ∀ (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
      (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : Paper.in_responses d M), M.delta ≤ delta0 →
        ∀ (j : ℕ), 0 < j → ∀ (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ j),
        ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
          aux_prop_growth_large_root_GrowthBody M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) z ((3 : ℝ) ^ j) hr
            t alpha k ps K Cbound := by
  intro t alpha k ps h1 h2 h3 h4 h5
  obtain ⟨δ0, hδ0, hU⟩ := calib3_unit_growth d hd Jc Pc Xc W Cp Sf t alpha k (fun i => 2 * ps i) h1 h2 h3 h4
    (fun i => by linarith [h5 i])
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm hδ j hj z hr
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hS := aux_prop_growth_large_root_measurePreserving_scaleShift M j
  obtain ⟨K', Cb', hmem', hbd', hK1', hG'⟩ := hU M Rm hδ j hj (((3 : ℝ) ^ j)⁻¹ • z)
  have hR2 : 1 ≤ 1 + (3 : ℝ) ^ j + ((3 : ℝ) ^ j) ^ 2 := by
    linarith [pow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) j, sq_nonneg ((3 : ℝ) ^ j)]
  have hR2sq : 1 ≤ (1 + (3 : ℝ) ^ j + ((3 : ℝ) ^ j) ^ 2) ^ 2 := one_le_pow₀ hR2
  refine ⟨fun N om => (1 + (3 : ℝ) ^ j + ((3 : ℝ) ^ j) ^ 2) ^ 2 * aux_prop_growth_large_root_shiftEnv M j om *
      K' N (aux_prop_growth_large_root_scaleShift j om),
    fun i => (1 + (3 : ℝ) ^ j + ((3 : ℝ) ^ j) ^ 2) ^ 2 *
      (eLpNorm (aux_prop_growth_large_root_shiftEnv M j) (ENNReal.ofReal (2 * ps i))
        (chaosSampleLaw M).toMeasure).toReal * Cb' i, ?_, ?_, ?_, ?_⟩
  · intro i N
    exact (aux_prop_growth_large_root_moment_step M j _ (by positivity) (ps i) (h5 i) (K' N) (Cb' i)
      (hmem' i N) (hbd' i N)).1
  · intro i N
    exact (aux_prop_growth_large_root_moment_step M j _ (by positivity) (ps i) (h5 i) (K' N) (Cb' i)
      (hmem' i N) (hbd' i N)).2
  · filter_upwards [hS.quasiMeasurePreserving.ae hK1'] with om hom N
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hR2sq (aux_prop_growth_large_root_one_le_shiftEnv M j om)) (hom N)
  · filter_upwards [hS.quasiMeasurePreserving.ae hG', hS.quasiMeasurePreserving.ae hK1'] with om hg hk1
    have hl1 : (1 : ℝ) ≤ (3 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    exact aux_prop_growth_large_root_growthAt_transfer_gen (z0 := ((3 : ℝ) ^ j)⁻¹ • z) hr one_pos hl1
      (mul_one _).symm (by linarith) h3.le
      (fun N => cutoffPositiveCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N z hr)
      (fun N => cutoffPositiveCoefficient M (calib3_HT d j) (aux_prop_growth_large_root_scaleShift j om) (N + j)
        (((3 : ℝ) ^ j)⁻¹ • z) one_pos)
      (fun N => aux_calib3_shift_const M j N) (aux_prop_growth_large_root_shiftEnv M j om)
      (fun N => aux_calib3_shift_const_pos M Rm j N)
      (fun N => (aux_calib3_shift_const_le M Rm j N hj).trans
        (aux_calib_H0_triadic_root_growth_env_le M j om))
      (fun N => (aux_calib3_shift_const_inv_le M Rm j N hj).trans
        (aux_calib_H0_triadic_root_growth_env_le M j om))
      (aux_prop_growth_large_root_one_le_shiftEnv M j om)
      (fun N => by
        have := aux_calib_H0_triadic_root_growth_pullback M Rm om j N hj z hr (s := 1) one_pos
          ((mul_one _).symm)
        simpa using this)
      (fun N => K' N (aux_prop_growth_large_root_scaleShift j om)) (fun N => hk1 N) hg

end Paper
