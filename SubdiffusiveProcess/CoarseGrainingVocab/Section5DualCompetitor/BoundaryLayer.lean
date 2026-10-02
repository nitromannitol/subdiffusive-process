import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.CoveredCompetitor




open MeasureTheory Homogenization Homogenization.Book Filter
open scoped BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-! ## The finite Cauchy--Schwarz step -/

/-- **Fraction versus second moment.**  A normalized partial sum of
nonnegative cell observables is at most the square root of the index fraction
times the square root of the normalized second moment. -/
theorem normalized_partial_sum_le_sqrt_fraction_mul_sqrt
    {ι : Type*} [DecidableEq ι] (D T : Finset ι) (hT : T ⊆ D)
    (Y : ι → ℝ) (hY0 : ∀ i ∈ D, 0 ≤ Y i) :
    ((D.card : ℝ)⁻¹) * ∑ i ∈ T, Y i ≤
      Real.sqrt ((T.card : ℝ) / (D.card : ℝ)) *
        Real.sqrt (((D.card : ℝ)⁻¹) * ∑ i ∈ D, Y i ^ 2) := by
  classical
  rcases Finset.eq_empty_or_nonempty D with hDempty | hDne
  · subst hDempty
    have hTempty : T = ∅ := Finset.subset_empty.mp hT
    subst hTempty
    simp
  have hDcard : 0 < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hDne
  have hsumT0 : 0 ≤ ∑ i ∈ T, Y i :=
    Finset.sum_nonneg fun i hi ↦ hY0 i (hT hi)
  have hsqSub : ∑ i ∈ T, Y i ^ 2 ≤ ∑ i ∈ D, Y i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hT fun i _ _ ↦ sq_nonneg _
  have hcs : (∑ i ∈ T, Y i) ^ 2 ≤ (T.card : ℝ) * ∑ i ∈ D, Y i ^ 2 := by
    refine sq_sum_le_card_mul_sum_sq.trans ?_
    exact mul_le_mul_of_nonneg_left hsqSub (Nat.cast_nonneg _)
  have hprod0 : 0 ≤ (T.card : ℝ) * ∑ i ∈ D, Y i ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  have hroot : ∑ i ∈ T, Y i ≤
      Real.sqrt ((T.card : ℝ) * ∑ i ∈ D, Y i ^ 2) := by
    have := Real.sqrt_le_sqrt hcs
    rwa [Real.sqrt_sq hsumT0] at this
  have hinv0 : (0 : ℝ) ≤ ((D.card : ℝ))⁻¹ := by positivity
  have hrhs : Real.sqrt ((T.card : ℝ) / (D.card : ℝ)) *
      Real.sqrt (((D.card : ℝ)⁻¹) * ∑ i ∈ D, Y i ^ 2) =
      ((D.card : ℝ))⁻¹ *
        Real.sqrt ((T.card : ℝ) * ∑ i ∈ D, Y i ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (T.card : ℝ) / (D.card : ℝ) *
        (((D.card : ℝ))⁻¹ * ∑ i ∈ D, Y i ^ 2) =
        (((D.card : ℝ))⁻¹) ^ 2 * ((T.card : ℝ) * ∑ i ∈ D, Y i ^ 2) by
      field_simp]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hinv0]
  rw [hrhs]
  exact mul_le_mul_of_nonneg_left hroot hinv0

/-! ## The expectation step -/

/-- On a probability space, `∫ √Z ≤ √(∫ Z)` for a nonnegative integrable
`Z`. -/
theorem integral_sqrt_le_sqrt_integral
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] (Z : Omega → ℝ)
    (hZ0 : ∀ omega, 0 ≤ Z omega) (hZ : Integrable Z mu) :
    ∫ omega, Real.sqrt (Z omega) ∂mu ≤
      Real.sqrt (∫ omega, Z omega ∂mu) := by
  have hsq : Integrable (fun omega ↦ Real.sqrt (Z omega) ^ 2) mu := by
    refine hZ.congr ?_
    filter_upwards with omega
    rw [Real.sq_sqrt (hZ0 omega)]
  have hone : Integrable (fun _ : Omega ↦ (1 : ℝ) ^ 2) mu := by
    simp only [one_pow]
    exact integrable_const 1
  have hcs :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq_of_ae_nonneg
      hsq hone
      (Filter.Eventually.of_forall fun omega ↦ Real.sqrt_nonneg (Z omega))
      (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
  have hsqeq : ∫ omega, Real.sqrt (Z omega) ^ 2 ∂mu =
      ∫ omega, Z omega ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards with omega
    rw [Real.sq_sqrt (hZ0 omega)]
  have hmu : ∫ _omega : Omega, (1 : ℝ) ^ 2 ∂mu = 1 := by simp
  calc
    ∫ omega, Real.sqrt (Z omega) ∂mu
        = ∫ omega, Real.sqrt (Z omega) * (1 : ℝ) ∂mu := by simp
    _ ≤ Real.sqrt (∫ omega, Real.sqrt (Z omega) ^ 2 ∂mu) *
          Real.sqrt (∫ _omega, (1 : ℝ) ^ 2 ∂mu) := hcs
    _ = Real.sqrt (∫ omega, Z omega ∂mu) := by
        rw [hsqeq, hmu, Real.sqrt_one, mul_one]

/-- **The reduction.**  The expectation of a normalized partial sum of
nonnegative cell observables is bounded by the square root of the index
fraction times the square root of a normalized second moment. -/
theorem integral_normalized_partial_sum_le_sqrt_fraction_mul_sqrt
    {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (D T : Finset ι) (hT : T ⊆ D) (Y : ι → Omega → ℝ)
    (hY0 : ∀ i ∈ D, ∀ omega, 0 ≤ Y i omega)
    (hYint : ∀ i ∈ D, Integrable (Y i) mu)
    (hsqint : Integrable
      (fun omega ↦ ((D.card : ℝ)⁻¹) * ∑ i ∈ D, Y i omega ^ 2) mu)
    {C : ℝ}
    (hC : ∫ omega, ((D.card : ℝ)⁻¹) * ∑ i ∈ D, Y i omega ^ 2 ∂mu ≤ C) :
    ∫ omega, ((D.card : ℝ)⁻¹) * ∑ i ∈ T, Y i omega ∂mu ≤
      Real.sqrt ((T.card : ℝ) / (D.card : ℝ)) * Real.sqrt C := by
  classical
  set Z : Omega → ℝ := fun omega ↦
    ((D.card : ℝ)⁻¹) * ∑ i ∈ D, Y i omega ^ 2 with hZdef
  have hZ0 : ∀ omega, 0 ≤ Z omega := by
    intro omega
    refine mul_nonneg (by positivity) ?_
    exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hfrac0 : (0 : ℝ) ≤ (T.card : ℝ) / (D.card : ℝ) := by positivity
  have hleft : Integrable
      (fun omega ↦ ((D.card : ℝ)⁻¹) * ∑ i ∈ T, Y i omega) mu :=
    (MeasureTheory.integrable_finset_sum T
      (fun i hi ↦ hYint i (hT hi))).const_mul _
  have hsqrtZint : Integrable (fun omega ↦ Real.sqrt (Z omega)) mu := by
    refine Integrable.mono' (hsqint.add (integrable_const (1 : ℝ)))
      (Real.continuous_sqrt.comp_aestronglyMeasurable
        hsqint.aestronglyMeasurable) ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : Real.sqrt (Z omega) ≤ Z omega + 1 := by
      nlinarith [sq_nonneg (Real.sqrt (Z omega) - 1),
        Real.sq_sqrt (hZ0 omega), Real.sqrt_nonneg (Z omega)]
    simpa only [hZdef, Pi.add_apply] using h1
  have hpointwise : ∀ omega,
      ((D.card : ℝ)⁻¹) * ∑ i ∈ T, Y i omega ≤
        Real.sqrt ((T.card : ℝ) / (D.card : ℝ)) * Real.sqrt (Z omega) := by
    intro omega
    simpa only [hZdef] using
      normalized_partial_sum_le_sqrt_fraction_mul_sqrt D T hT
        (fun i ↦ Y i omega) (fun i hi ↦ hY0 i hi omega)
  calc
    ∫ omega, ((D.card : ℝ)⁻¹) * ∑ i ∈ T, Y i omega ∂mu ≤
        ∫ omega, Real.sqrt ((T.card : ℝ) / (D.card : ℝ)) *
          Real.sqrt (Z omega) ∂mu :=
      integral_mono hleft (hsqrtZint.const_mul _) hpointwise
    _ = Real.sqrt ((T.card : ℝ) / (D.card : ℝ)) *
          ∫ omega, Real.sqrt (Z omega) ∂mu := integral_const_mul _ _
    _ ≤ Real.sqrt ((T.card : ℝ) / (D.card : ℝ)) *
          Real.sqrt (∫ omega, Z omega ∂mu) :=
      mul_le_mul_of_nonneg_left
        (integral_sqrt_le_sqrt_integral Z hZ0 hsqint)
        (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt ((T.card : ℝ) / (D.card : ℝ)) * Real.sqrt C :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hC) (Real.sqrt_nonneg _)

/-- The resulting bound vanishes whenever the index fraction does. -/
theorem tendsto_sqrt_fraction_mul_sqrt_zero (C : ℝ) (frac : ℕ → ℝ)
    (hfrac : Tendsto frac atTop (nhds 0)) :
    Tendsto (fun K : ℕ ↦ Real.sqrt (frac K) * Real.sqrt C) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun K : ℕ ↦ Real.sqrt (frac K)) atTop (nhds 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hfrac
  simpa only [zero_mul] using hsqrt.mul_const (Real.sqrt C)

/-! ## The concrete boundary-layer statement -/

/-- **The boundary-layer expectation bound, in the shape
`CoveredCompetitor.lean` consumes**, reduced to two named inputs: a vanishing
uncovered *fraction* and a uniform normalized *second moment* of the glued
cell half-energies. -/
theorem exists_dualPaperBoundaryLayer_expectation_bound
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (hh : 0 < h)
    (K₀ : ℕ)
    (covered : ℕ → Finset (Homogenization.TriadicCube d))
    (_hcovered : ∀ K, covered K ⊆ oneStepSourceCells d K n M.delta)
    (frac : ℕ → ℝ) (hfrac0 : Tendsto frac atTop (nhds 0))
    (hfrac : ∀ K, K₀ ≤ K →
      (((oneStepSourceCells d K n M.delta) \ covered K).card : ℝ) /
        ((oneStepSourceCells d K n M.delta).card : ℝ) ≤ frac K)
    (C : ℝ)
    (hcellInt : ∀ (K : ℕ), K₀ ≤ K →
      ∀ R ∈ oneStepSourceCells d K n M.delta,
      Integrable (fun omega ↦ paperGluedCellHalfEnergy M n h q omega hh
        (dualParentEllipticityData_descendants M (n + h) omega
          (originCube d (K : ℤ))
          (K - oneStepLocalizationScale n M.delta)) R) M.P.toMeasure)
    (hsqInt : ∀ K : ℕ, K₀ ≤ K → Integrable (fun omega ↦
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            (paperGluedCellHalfEnergy M n h q omega hh
              (dualParentEllipticityData_descendants M (n + h) omega
                (originCube d (K : ℤ))
                (K - oneStepLocalizationScale n M.delta)) R) ^ 2)
      M.P.toMeasure)
    (hsq : ∀ K : ℕ, K₀ ≤ K → ∫ omega,
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            (paperGluedCellHalfEnergy M n h q omega hh
              (dualParentEllipticityData_descendants M (n + h) omega
                (originCube d (K : ℤ))
                (K - oneStepLocalizationScale n M.delta)) R) ^ 2
        ∂M.P.toMeasure ≤ C) :
    ∃ boundaryBound : ℕ → ℝ,
      Tendsto boundaryBound atTop (nhds 0) ∧
      ∀ K : ℕ, K₀ ≤ K → ∫ omega,
          (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
            ∑ R ∈ (oneStepSourceCells d K n M.delta) \ covered K,
              paperGluedCellHalfEnergy M n h q omega hh
                (dualParentEllipticityData_descendants M (n + h) omega
                  (originCube d (K : ℤ))
                  (K - oneStepLocalizationScale n M.delta)) R
          ∂M.P.toMeasure ≤ boundaryBound K := by
  classical
  haveI : IsProbabilityMeasure M.P.toMeasure := M.P.prop
  refine ⟨fun K ↦ Real.sqrt (frac K) * Real.sqrt C,
    tendsto_sqrt_fraction_mul_sqrt_zero C frac hfrac0, ?_⟩
  intro K hK
  have hsubset : (oneStepSourceCells d K n M.delta) \ covered K ⊆
      oneStepSourceCells d K n M.delta := Finset.sdiff_subset
  have hmain := integral_normalized_partial_sum_le_sqrt_fraction_mul_sqrt
    (mu := M.P.toMeasure)
    (oneStepSourceCells d K n M.delta)
    ((oneStepSourceCells d K n M.delta) \ covered K) hsubset
    (fun R omega ↦ paperGluedCellHalfEnergy M n h q omega hh
      (dualParentEllipticityData_descendants M (n + h) omega
        (originCube d (K : ℤ))
        (K - oneStepLocalizationScale n M.delta)) R)
    (fun R _hR omega ↦ paperGluedCellHalfEnergy_nonneg M n h q omega hh _ R)
    (hcellInt K hK) (hsqInt K hK) (hsq K hK)
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt (hfrac K hK)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
