import SubdiffusiveProcess.Section10.DensityHalfMomentRoot
import Mathlib.Probability.Independence.Integration

/-! Exact square-root moments for the actual finite fine densities. -/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess
open scoped BigOperators ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem fine_half_factor_identDistrib (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n : ℕ) (x : SpatialCoordinates d) :
    IdentDistrib
      (fun w : BilateralField d =>
        Real.exp ((w (-(n : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) / 2))
      (rootHalfFactor M) (chaosSampleLaw M).toMeasure
        (chaosRootFieldLaw M).toMeasure :=
  (Paper.aux_lim_measure_fine_eval_identDistrib M n x).comp
    (((measurable_id.sub measurable_const).div_const 2).exp :
      Measurable (fun t : ℝ => Real.exp ((t - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) / 2)))

theorem integrable_fine_half_factor (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n : ℕ) (x : SpatialCoordinates d) :
    Integrable (fun w : BilateralField d =>
      Real.exp ((w (-(n : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) / 2))
        (chaosSampleLaw M).toMeasure :=
  (fine_half_factor_identDistrib M n x).integrable_iff.mpr (integrable_rootHalfFactor M)

theorem integral_fine_half_factor (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n : ℕ) (x : SpatialCoordinates d) :
    (∫ w : BilateralField d,
      Real.exp ((w (-(n : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) / 2)
        ∂(chaosSampleLaw M).toMeasure) = densityHalfMomentRatio M :=
  (fine_half_factor_identDistrib M n x).integral_eq

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem sqrt_fineDensity_eq_prod (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (w : BilateralField d) (x : SpatialCoordinates d) :
    Real.sqrt (fineDensity M N w x) =
      ∏ i : (Finset.range (N + 1)),
        Real.exp ((w (-((i : ℕ) : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) / 2) := by
  rw [fineDensity, ← Real.exp_half]
  unfold finePotential
  calc
    _ = Real.exp (∑ j ∈ Finset.range (N + 1),
        (w (-(j : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) / 2) := by
      congr 1
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Int.ofNat_eq_natCast]
    _ = ∏ j ∈ Finset.range (N + 1),
        Real.exp ((w (-(j : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) / 2) :=
      Real.exp_sum _ _
    _ = _ := (Finset.prod_coe_sort (Finset.range (N + 1)) _).symm

theorem measurable_sqrt_fineDensity (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (x : SpatialCoordinates d) :
    Measurable (fun w => Real.sqrt (fineDensity M N w x)) := by
  apply Real.continuous_sqrt.measurable.comp
  exact (stronglyMeasurable_fineDensity_uncurry M N).measurable.comp
    (measurable_id.prodMk measurable_const)

theorem integrable_sqrt_fineDensity (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (x : SpatialCoordinates d) :
    Integrable (fun w => Real.sqrt (fineDensity M N w x))
      (chaosSampleLaw M).toMeasure := by
  have hi := integrable_of_integral_eq_one (integral_fineDensity_chaosSampleLaw M N x)
  apply ((integrable_const (1 : ℝ)).add hi).mono'
    (measurable_sqrt_fineDensity M N x).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun w => by
    change ‖Real.sqrt (fineDensity M N w x)‖ ≤ 1 + fineDensity M N w x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs := Real.sq_sqrt (le_of_lt (fineDensity_pos M N w x))
    nlinarith [sq_nonneg (Real.sqrt (fineDensity M N w x) - 1)]

theorem integral_sqrt_fineDensity (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (x : SpatialCoordinates d) :
    (∫ w, Real.sqrt (fineDensity M N w x) ∂(chaosSampleLaw M).toMeasure) =
      densityHalfMomentRatio M ^ (N + 1) := by
  let S := Finset.range (N + 1)
  have hcoord : iIndepFun
      (fun i : S => fun w : BilateralField d => w (-((i : ℕ) : ℤ)) x)
        (chaosSampleLaw M).toMeasure :=
    (Paper.aux_lim_measure_fine_eval_independent M x).precomp Subtype.val_injective
  have hindep : iIndepFun
      (fun i : S => fun w : BilateralField d =>
        Real.exp ((w (-((i : ℕ) : ℤ)) x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) / 2))
        (chaosSampleLaw M).toMeasure :=
    hcoord.comp (fun _ => fun t : ℝ => Real.exp ((t - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) / 2))
      (fun _ => ((measurable_id.sub measurable_const).div_const 2).exp)
  have hfactor := hindep.integral_fun_prod_comp
    (fun i => (integrable_fine_half_factor M i x).aemeasurable)
    (fun _ => aestronglyMeasurable_id)
  simp only [id_eq] at hfactor
  simp_rw [sqrt_fineDensity_eq_prod]
  rw [hfactor]
  simp only [integral_fine_half_factor, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe, S, Finset.card_range]

theorem lintegral_sqrt_fineDensity (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (x : SpatialCoordinates d) :
    (∫⁻ w, ENNReal.ofReal (Real.sqrt (fineDensity M N w x))
      ∂(chaosSampleLaw M).toMeasure) = ENNReal.ofReal (densityHalfMomentRatio M ^ (N + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sqrt_fineDensity M N x)
    (Filter.Eventually.of_forall fun w => Real.sqrt_nonneg _), integral_sqrt_fineDensity]

end SubdiffusiveProcess.Section10
