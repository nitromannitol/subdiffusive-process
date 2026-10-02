import SubdiffusiveProcess.Paper.lane4_reference_oscillation_moments

open MeasureTheory Set Filter Metric ProbabilityTheory TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem lem_as_coarse_shallow_grid_zero_ir_compact_exp_lp
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ BH : ℝ, 0 < BH ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ 1 →
        let P := (chaosSampleLaw M).toMeasure
        let K3 : Compacts (SpatialCoordinates d) :=
          ⟨Metric.closedBall 0 3, ProperSpace.isCompact_closedBall 0 3⟩
        let Y : BilateralField d → ℝ := fun omega =>
          ‖(H omega).restrict (K3 : Set (SpatialCoordinates d))‖
        MemLp (fun omega => Real.exp (3 * Y omega))
          (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (3 * Y omega))
          (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal BH := by
  classical
  obtain ⟨CH, hCH, hHmom⟩ :=
    exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  let K3 : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall 0 3, ProperSpace.isCompact_closedBall 0 3⟩
  let BH : ℝ := (2 * Real.exp (CH K3 * (6 * q)^2)) ^ (1 / (2 * q))
  refine ⟨BH, by dsimp [BH]; positivity, ?_⟩
  intro M H hH hM
  dsimp only
  let P := (chaosSampleLaw M).toMeasure
  let Y : BilateralField d → ℝ := fun omega =>
    ‖(H omega).restrict (K3 : Set (SpatialCoordinates d))‖
  have hYmeas : Measurable Y := by
    have hcont : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ‖f.restrict (K3 : Set (SpatialCoordinates d))‖) :=
      continuous_norm.comp (ContinuousMap.continuous_restrict _)
    simpa [Y, Function.comp_apply] using hcont.measurable.comp hH.1
  have hp : 0 < 2 * q := by linarith
  have hp0 : ENNReal.ofReal (2 * q) ≠ 0 :=
    (ENNReal.ofReal_eq_zero.not).2 (not_le.mpr hp)
  have hptop : ENNReal.ofReal (2 * q) ≠ ∞ := ENNReal.ofReal_ne_top
  have hraw := hHmom M H hH K3 (6 * q) (by positivity)
  have hδsq : M.delta ^ 2 ≤ 1 := by
    have hδ0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
    have hh := mul_self_le_mul_self hδ0 hM
    simpa [pow_two] using hh
  have hE0 : 0 ≤ CH K3 * (6 * q)^2 :=
    mul_nonneg (hCH K3) (sq_nonneg _)
  have hInt : Integrable (fun omega => Real.exp ((2 * q) * (3 * Y omega))) P := by
    convert hraw.1 using 1
    funext omega
    dsimp [Y]
    congr 1
    ring
  have hBound :
      (∫ omega, Real.exp ((2 * q) * (3 * Y omega)) ∂P) ≤
        2 * Real.exp (CH K3 * (6 * q)^2) := by
    calc
      (∫ omega, Real.exp ((2 * q) * (3 * Y omega)) ∂P) =
          (∫ omega, Real.exp ((6 * q) * Y omega) ∂P) := by congr 1; funext omega; congr 1; ring
      _ ≤ 2 * Real.exp (CH K3 * (6 * q)^2 * M.delta^2) := by
        simpa [P, Y] using hraw.2
      _ ≤ 2 * Real.exp (CH K3 * (6 * q)^2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        calc
          CH K3 * (6 * q)^2 * M.delta^2 ≤ CH K3 * (6 * q)^2 * 1 :=
            mul_le_mul_of_nonneg_left hδsq hE0
          _ = CH K3 * (6 * q)^2 := by ring
  have heq : ∀ omega, ‖Real.exp (3 * Y omega)‖ ^
      (ENNReal.ofReal (2 * q)).toReal =
        Real.exp ((2 * q) * (3 * Y omega)) := by
    intro omega
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ENNReal.toReal_ofReal hp.le]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have hpow : Integrable (fun omega =>
      ‖Real.exp (3 * Y omega)‖ ^ (ENNReal.ofReal (2 * q)).toReal) P := by
    simpa only [heq] using hInt
  have hexpm : Measurable (fun omega => Real.exp (3 * Y omega)) :=
    (measurable_const.mul hYmeas).exp
  have hmem :=
    (integrable_norm_rpow_iff hexpm.aestronglyMeasurable hp0 hptop).mp hpow
  refine ⟨hmem, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hptop]
  have hlin :
      ∫⁻ omega, ‖Real.exp (3 * Y omega)‖ₑ ^
          (ENNReal.ofReal (2 * q)).toReal ∂P =
        ENNReal.ofReal (∫ omega, Real.exp ((2 * q) * (3 * Y omega)) ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun omega => (Real.exp_pos _).le)]
    apply lintegral_congr_ae
    filter_upwards [] with omega
    rw [← ofReal_norm_eq_enorm]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (norm_nonneg (Real.exp (3 * Y omega))) ENNReal.toReal_nonneg]
    rw [heq]
  rw [hlin]
  change (ENNReal.ofReal
      (∫ omega, Real.exp ((2 * q) * (3 * Y omega)) ∂P)) ^
      (1 / (ENNReal.ofReal (2 * q)).toReal) ≤ ENNReal.ofReal BH
  dsimp [BH]
  rw [ENNReal.toReal_ofReal hp.le]
  calc
    (ENNReal.ofReal
        (∫ omega, Real.exp ((2 * q) * (3 * Y omega)) ∂P)) ^ (1 / (2 * q)) ≤
        (ENNReal.ofReal (2 * Real.exp (CH K3 * (6 * q)^2))) ^ (1 / (2 * q)) := by
          exact ENNReal.rpow_le_rpow
            ((ENNReal.ofReal_le_ofReal_iff (by positivity)).2 hBound)
            (by positivity)
    _ = ENNReal.ofReal
        ((2 * Real.exp (CH K3 * (6 * q)^2)) ^ (1 / (2 * q))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]

end Paper

