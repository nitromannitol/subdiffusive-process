import SubdiffusiveProcess.Section10.ChaosStrongLaw
import SubdiffusiveProcess.Probability.FineDensityMean

/-! The strict half moment on the model's continuous root-field law. -/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.Section10

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The one-shell half-density factor at the root point. -/
def rootHalfFactor (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (f : C(SpatialCoordinates d, ℝ)) : ℝ :=
  Real.exp ((f 0 - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) / 2)

/-- The same root expectation used for every finite-density half moment. -/
def densityHalfMomentRatio (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) : ℝ :=
  ∫ f, rootHalfFactor M f ∂(chaosRootFieldLaw M).toMeasure

theorem measurable_rootHalfFactor (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    Measurable (rootHalfFactor M) :=
  (((continuous_eval_const (0 : SpatialCoordinates d)).measurable.sub
    measurable_const).div_const 2).exp

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem rootHalfFactor_sq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (f : C(SpatialCoordinates d, ℝ)) :
    rootHalfFactor M f ^ 2 = Real.exp (f 0 - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
  rw [rootHalfFactor, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem integral_root_normalized_exp (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    (∫ f : C(SpatialCoordinates d, ℝ),
      Real.exp (f 0 - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
        ∂(chaosRootFieldLaw M).toMeasure) = 1 := by
  have hid := (Paper.aux_lim_measure_fine_eval_identDistrib M 0 0).comp
    ((measurable_id.sub measurable_const).exp :
      Measurable (fun t : ℝ => Real.exp (t - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)))
  have hmean := integral_fineDensity_chaosSampleLaw M 0 0
  have hs : (∫ w : BilateralField d,
      Real.exp (w 0 0 - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
        ∂(chaosSampleLaw M).toMeasure) = 1 := by
    simpa only [fineDensity, finePotential, zero_add, Finset.range_one,
      Finset.sum_singleton, Int.ofNat_zero, neg_zero, Nat.cast_zero, one_mul] using hmean
  exact hid.integral_eq.symm.trans hs

theorem integrable_rootHalfFactor_sq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    Integrable (fun f => rootHalfFactor M f ^ 2) (chaosRootFieldLaw M).toMeasure := by
  simp_rw [rootHalfFactor_sq]
  exact integrable_of_integral_eq_one (integral_root_normalized_exp M)

theorem integral_rootHalfFactor_sq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    (∫ f, rootHalfFactor M f ^ 2 ∂(chaosRootFieldLaw M).toMeasure) = 1 := by
  simp_rw [rootHalfFactor_sq]
  exact integral_root_normalized_exp M

theorem integrable_rootHalfFactor (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    Integrable (rootHalfFactor M) (chaosRootFieldLaw M).toMeasure := by
  apply ((integrable_const (1 : ℝ)).add (integrable_rootHalfFactor_sq M)).mono'
    (measurable_rootHalfFactor M).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun f => by
    change ‖rootHalfFactor M f‖ ≤ 1 + rootHalfFactor M f ^ 2
    rw [Real.norm_eq_abs, abs_of_pos (show 0 < rootHalfFactor M f from Real.exp_pos _)]
    nlinarith [sq_nonneg (rootHalfFactor M f - 1)]

theorem densityHalfMomentRatio_pos (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    0 < densityHalfMomentRatio M := by
  exact integral_exp_pos (integrable_rootHalfFactor M)

theorem integrable_rootHalfFactor_sub_one_sq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    Integrable (fun f => (rootHalfFactor M f - 1) ^ 2)
      (chaosRootFieldLaw M).toMeasure := by
  have hi := ((integrable_rootHalfFactor_sq M).sub
    ((integrable_rootHalfFactor M).const_mul 2)).add (integrable_const (1 : ℝ))
  exact hi.congr (Filter.Eventually.of_forall fun f => by
    change rootHalfFactor M f ^ 2 - 2 * rootHalfFactor M f + 1 = _
    ring)

theorem integral_rootHalfFactor_sub_one_sq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    (∫ f, (rootHalfFactor M f - 1) ^ 2 ∂(chaosRootFieldLaw M).toMeasure) =
      2 - 2 * densityHalfMomentRatio M := by
  calc
    _ = ∫ f, (rootHalfFactor M f ^ 2 - 2 * rootHalfFactor M f + 1)
        ∂(chaosRootFieldLaw M).toMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall fun f => by ring)
    _ = 2 - 2 * densityHalfMomentRatio M := by
      rw [integral_add (f := fun f => rootHalfFactor M f ^ 2 - 2 * rootHalfFactor M f)
        (g := fun _ => (1 : ℝ)) ((integrable_rootHalfFactor_sq M).sub
        ((integrable_rootHalfFactor M).const_mul 2)) (integrable_const (1 : ℝ)),
        integral_sub (f := fun f => rootHalfFactor M f ^ 2)
          (g := fun f => 2 * rootHalfFactor M f) (integrable_rootHalfFactor_sq M)
          ((integrable_rootHalfFactor M).const_mul 2),
        integral_const_mul, integral_rootHalfFactor_sq, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul, densityHalfMomentRatio]
      ring

theorem densityHalfMomentRatio_lt_one (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    densityHalfMomentRatio M < 1 := by
  have hn : 0 ≤ 2 - 2 * densityHalfMomentRatio M := by
    rw [← integral_rootHalfFactor_sub_one_sq]
    exact integral_nonneg fun f => sq_nonneg _
  have hle : densityHalfMomentRatio M ≤ 1 := by linarith
  apply lt_of_le_of_ne hle
  intro heq
  have hz : (∫ f, (rootHalfFactor M f - 1) ^ 2
      ∂(chaosRootFieldLaw M).toMeasure) = 0 := by
    rw [integral_rootHalfFactor_sub_one_sq, heq]
    norm_num
  have hae := (integral_eq_zero_iff_of_nonneg (fun f => sq_nonneg _)
    (integrable_rootHalfFactor_sub_one_sq M)).mp hz
  have hg : (fun f : C(SpatialCoordinates d, ℝ) => f 0) =ᵐ[
      (chaosRootFieldLaw M).toMeasure] fun _ => SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
    filter_upwards [hae] with f hf
    change (rootHalfFactor M f - 1) ^ 2 = 0 at hf
    have hZ : rootHalfFactor M f = 1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hf)
    have hexp : (f 0 - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) / 2 = 0 :=
      Real.exp_injective (hZ.trans Real.exp_zero.symm)
    linarith
  have hmean := (Paper.aux_lim_measure_root_eval_moments M 0).2
  have hconst := integral_congr_ae hg
  rw [hmean, integral_const] at hconst
  simp only [probReal_univ, smul_eq_mul, one_mul] at hconst
  exact (ne_of_gt M.G4.tauSq_pos) hconst.symm

theorem densityHalfMomentRatio_mem_Ioo (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    densityHalfMomentRatio M ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨densityHalfMomentRatio_pos M, densityHalfMomentRatio_lt_one M⟩

end SubdiffusiveProcess.Section10
