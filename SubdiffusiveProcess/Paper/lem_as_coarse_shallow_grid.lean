module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.prop_as_response_bank_cauchy
public import SubdiffusiveProcess.Paper.prop_as_response_bank_limit_completion
public import SubdiffusiveProcess.Paper.prop_as_response_bank_limit_tail
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.lem_as_coarse_deep_grid
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_numeric_tail
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_theta_split
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_parent_local_fraction
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_translated_zero_ir_bank_product
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_translated_two_branch_envelope
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_translated_cell_bridge
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_bank_family_tail
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_factor_product
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_matrix_bank
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_envelope
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_shifted_bank
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_envelope_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_point_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_envelope_exponential
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_inverse_point_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_cell_moment
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_envelope
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_ahom_ratio
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_cell_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_disorder_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_factor_moment_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_center_carrier
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_centered_point_moments
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_centered_oscillation_moments
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_centered_cell_moment
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_centered_factor_moment_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_factor_moment_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_factor_aestronglyMeasurable
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_factor_bank_product
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_factor_moment_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_factor_measurable
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_factor_bank_product
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_charted_cellMap_ae
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_charted_shifted_factor_ae
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_charted_origin_scalar_bounds
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_uniform_factor_envelope
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_affine_coeff_comparison
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_osc_sup_pair_bound
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_osc_coefficient_comparison
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_cell_coefficient_comparison
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_cellMap_mem_osc_ball
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_matched_affine_moment
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_affine_dirichlet_measurable
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_affine_inverse_neumann_measurable
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_root_inverse_neumann_coordinate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_tau_absorption
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_limit_bank_norm
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_matched_limit_affine_moment
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_root_dirichlet_coordinate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_shifted_dirichlet_coordinate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_uniform_ratio_pointwise
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_ahom_exp_pair
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_responseJ_bridge
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_exponent_choice
public import SubdiffusiveProcess.Paper.lane4_reference_point_moments
public import SubdiffusiveProcess.Paper.lane4_reference_oscillation_moments
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.Inputs
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set Filter Topology SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- A uniform moment bound for cutoff response-bank coordinates passes to
their limit in measure. This is the finite-bank moment step used after the
response Cauchy construction; no moment of the limit is assumed. -/
theorem aux_lem_as_coarse_shallow_grid_limit_bank_norm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p C : ℝ≥0∞) (hC : C < ∞)
    (R : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hRmeas : ∀ N, AEStronglyMeasurable (R N) P)
    (hRbound : ∀ N, eLpNorm (R N) p P ≤ C)
    (hconv : TendstoInMeasure P R atTop Z) :
    MemLp Z p P ∧ eLpNorm Z p P ≤ C := by
  have hZbound : eLpNorm Z p P ≤ C :=
    eLpNorm_le_of_tendstoInMeasure (Filter.Eventually.of_forall hRbound) hconv hRmeas
  have hZmeas : AEStronglyMeasurable Z P :=
    hconv.aestronglyMeasurable hRmeas
  exact ⟨lt_of_le_of_lt hZbound hC, hZbound⟩

/-- The $L^p$ moment-to-tail step for one retained cell. -/
theorem aux_lem_as_coarse_shallow_grid_probability_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (p B T : ℝ)
    (hp : 0 < p) (hT : 0 < T)
    (hX : AEStronglyMeasurable X P)
    (hLp : eLpNorm X (ENNReal.ofReal p) P ≤ ENNReal.ofReal B) :
    P {ω | T ≤ |X ω|} ≤ ENNReal.ofReal (B / T) ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hT0 : ENNReal.ofReal T ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hT
  have hpReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hLp' : eLpNorm X (ENNReal.ofReal p) P ^ p ≤ ENNReal.ofReal B ^ p := by
    gcongr
  have hmarkov :=
    meas_ge_le_mul_pow_eLpNorm_enorm P (f := X) hp0 hptop hT0 (by simp)
  have hbound :
      P {ω | ENNReal.ofReal T ≤ ‖X ω‖ₑ} ≤
        (ENNReal.ofReal T)⁻¹ ^ p * ENNReal.ofReal B ^ p := by
    calc
      P {ω | ENNReal.ofReal T ≤ ‖X ω‖ₑ} ≤
          (ENNReal.ofReal T)⁻¹ ^ p * eLpNorm X (ENNReal.ofReal p) P ^ p := by
            simpa [hpReal] using hmarkov
      _ ≤ (ENNReal.ofReal T)⁻¹ ^ p * ENNReal.ofReal B ^ p := by
            exact mul_le_mul_of_nonneg_left hLp' bot_le
  have hrhs :
      (ENNReal.ofReal T)⁻¹ ^ p * ENNReal.ofReal B ^ p = ENNReal.ofReal (B / T) ^ p := by
    rw [ENNReal.ofReal_div_of_pos hT]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hp)]
    congr 1
    rw [div_eq_mul_inv]
    simp [mul_comm]
  have hevent :
      {ω | T ≤ |X ω|} = {ω | ENNReal.ofReal T ≤ ‖X ω‖ₑ} := by
    ext ω
    change (T ≤ |X ω|) ↔ ENNReal.ofReal T ≤ ‖X ω‖ₑ
    rw [Real.enorm_eq_ofReal_abs]
    exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg (X ω))).symm
  rw [hevent]
  exact hbound.trans_eq hrhs

/-- A response-comparison rate admits a strictly smaller retained-grid fraction. -/
theorem aux_lem_as_coarse_shallow_grid_theta
    (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
      (d : ℝ) * theta < c * (1 - theta) / 2 := by
  let D : ℝ := 2 * ((d : ℝ) + c + 1)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨c / D, div_pos hc hD, ?_, ?_⟩
  · apply (div_lt_iff₀ hD).2
    dsimp [D]
    linarith
  · have hthetaD : (c / D) * D = c := div_mul_cancel₀ c (ne_of_gt hD)
    dsimp [D] at hthetaD ⊢
    nlinarith [mul_pos hc hc]

section FiniteMaxima
open Homogenization Homogenization.Book.Ch02
/-- A uniform bound on the two matrix norms in every descendant bounds
the sum of the two separate finite descendant maxima. -/
theorem aux_lem_as_coarse_shallow_grid_maxima_of_cells {d : ℕ}
    (Q : TriadicCube d) (s : ℤ) (A : TriadicCoeffFamily d)
    (C : ℝ) (hC : 0 ≤ C)
    (hcell : ∀ R ∈ descendantsAtScale Q s,
      coarseBMatrixNorm R A + coarseSigmaStarInvMatrixNorm R A ≤ C) :
    maxDescendantBMatrixNormAtScale Q s A +
      maxDescendantSigmaStarInvMatrixNormAtScale Q s A ≤ 2 * C := by
  have hB_nonneg : ∀ R, 0 ≤ coarseBMatrixNorm R A := by
    intro R; exact matrixNorm_nonneg _
  have hS_nonneg : ∀ R, 0 ≤ coarseSigmaStarInvMatrixNorm R A := by
    intro R; exact matrixNorm_nonneg _
  have hB_le_C : ∀ R ∈ descendantsAtScale Q s, coarseBMatrixNorm R A ≤ C := by
    intro R hR
    have hsum := hcell R hR
    have hS := hS_nonneg R
    linarith
  have hS_le_C : ∀ R ∈ descendantsAtScale Q s, coarseSigmaStarInvMatrixNorm R A ≤ C := by
    intro R hR
    have hsum := hcell R hR
    have hB := hB_nonneg R
    linarith
  by_cases hne : (descendantsAtScale Q s).Nonempty
  · have hmaxB : maxDescendantBMatrixNormAtScale Q s A ≤ C := by
      unfold maxDescendantBMatrixNormAtScale
      exact finsetSupReal_le (descendantsAtScale Q s) hne hB_le_C
    have hmaxS : maxDescendantSigmaStarInvMatrixNormAtScale Q s A ≤ C := by
      unfold maxDescendantSigmaStarInvMatrixNormAtScale
      exact finsetSupReal_le (descendantsAtScale Q s) hne hS_le_C
    linarith
  · have hempty : descendantsAtScale Q s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    unfold maxDescendantBMatrixNormAtScale maxDescendantSigmaStarInvMatrixNormAtScale
    unfold finsetSupReal
    simp [hempty, Real.sSup_empty]
    nlinarith
end FiniteMaxima

open Homogenization Homogenization.Book.Ch02

/-- Coordinate response bounds on every retained cell give the exact pair of
descendant maxima used by the shallow-grid conclusion. -/
theorem aux_shallow_coordinate_bounds_to_maxima {d : ℕ} [NeZero d]
    (Jc : in_J d) (Q : TriadicCube d) (s : ℤ) (A : TriadicCoeffFamily d)
    (Kb Ks : ℝ) (hK : 0 ≤ Kb + Ks)
    (hs : ∀ R ∈ descendantsAtScale Q s, CoeffOn.IsSymmetric (A.coeffOn R))
    (hb : ∀ R ∈ descendantsAtScale Q s, ∀ i : Fin d,
      responseJ (cubeDomain R) (A.coeffOn R) (Pi.single i 1) 0 ≤ Kb)
    (hstar : ∀ R ∈ descendantsAtScale Q s, ∀ i : Fin d,
      responseJ (cubeDomain R) (A.coeffOn R) 0 (Pi.single i 1) ≤ Ks) :
    maxDescendantBMatrixNormAtScale Q s A +
      maxDescendantSigmaStarInvMatrixNormAtScale Q s A ≤
        4 * (d : ℝ) * (Kb + Ks) := by
  have hC : 0 ≤ 2 * (d : ℝ) * (Kb + Ks) := by positivity
  have hcell : ∀ R ∈ descendantsAtScale Q s,
      coarseBMatrixNorm R A + coarseSigmaStarInvMatrixNorm R A ≤
        2 * (d : ℝ) * (Kb + Ks) := by
    intro R hR
    exact lem_as_coarse_shallow_grid_matrix_bank Jc R A
      (hs R hR) Kb Ks (hb R hR) (hstar R hR)
  have h := aux_lem_as_coarse_shallow_grid_maxima_of_cells Q s A
    (2 * (d : ℝ) * (Kb + Ks)) hC hcell
  convert h using 1 <;> ring

/-- The retained-grid estimate in the proof of the pathwise coarse bounds.
The common grid fraction is chosen before reducing the disorder. The two
matrix norms are those appearing in the root chart's multiscale sums. -/
theorem lem_as_coarse_shallow_grid
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d)
    (Pc : in_poincare d hd Jc)
    (Xc : in_extension d hd Jc)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (s rho : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hrho : 0 < rho) (hrhos : rho < s / 4) :
    ∃ theta delta0 : ℝ, 0 < theta ∧ theta < 1 ∧ 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg),
        ∀ (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M Hir →
        M.delta ≤ min 1 delta0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
          ∀ withIR : Bool,
            let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
              if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
            ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
              ∀ k : ℕ, (k : ℝ) ≤ theta * (N : ℝ) →
                Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
                  Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
                  K * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  exact lem_as_coarse_shallow_grid_theta_split d hd Jc Xc Sf rho hrho
    (lem_as_coarse_shallow_grid_parent_local_fraction d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp rho hrho)

end Paper

