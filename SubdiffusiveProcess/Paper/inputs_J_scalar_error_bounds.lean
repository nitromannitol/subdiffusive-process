module

public import SubdiffusiveProcess.Paper.inputs_J_native_lower_one
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.EllipticityErrorAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.LowerEllipticityComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.EnergyFactor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CarrierComparison

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_inputs_J_scalar_error_bounds_native_series_summable
    {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (a0 : ℝ)
    {s q : ℝ} (hs : 0 < s) (hq : q = 1 ∨ q = 2) :
    Summable (fun l : ℕ =>
      Homogenization.Book.Ch02.geometricWeight s q l *
        Real.rpow
          (Homogenization.Book.Ch02.scaleResponseAtScale Q
            (Q.scale - (l : ℤ)) .infinity F
            (Homogenization.scalarMatrix a0)) q) := by
  rcases hq with hq | hq
  · subst q
    have h := Homogenization.Book.Ch02.summable_homogenizationErrorOnCube_infinity_one_terms
      Q F (Homogenization.scalarMatrix a0) hs
    simpa [Real.rpow_one] using h
  · subst q
    have h :=
      Homogenization.Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q F (Homogenization.scalarMatrix a0) hs
    convert h using 1
    funext l
    have hk : Q.scale - (l : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le l)
    rw [Homogenization.Book.Ch02.scaleResponseAtScale_infinity_rpow_two_eq
      Q hk F (Homogenization.scalarMatrix a0)]

theorem aux_inputs_J_scalar_error_bounds_paper_le_native
    {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hSymm : ∀ R : Homogenization.TriadicCube d,
      Homogenization.Book.Ch02.CoeffOn.IsSymmetric (F.coeffOn R))
    {s q a0 : ℝ} (hs : 0 < s) (hq : q = 1 ∨ q = 2)
    (ha0 : 0 < a0) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError Q Q.scale s
      Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite q) F a0 ≤
    ENNReal.ofReal
      (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
        (.finite q) F (Homogenization.scalarMatrix a0)) := by
  apply SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.paperHomogenizationError_le_ofReal_finite
    Q le_rfl hs.le (by rcases hq with h | h <;> simp [h]) F hSymm ha0
  exact aux_inputs_J_scalar_error_bounds_native_series_summable
    Q F a0 hs hq

theorem aux_inputs_J_scalar_error_bounds_native_le_paper
    {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hSymm : ∀ R : Homogenization.TriadicCube d,
      Homogenization.Book.Ch02.CoeffOn.IsSymmetric (F.coeffOn R))
    {s a0 : ℝ} (hs : 0 < s) (ha0 : 0 < a0) :
    ∀ q : ℝ, q = 1 ∨ q = 2 →
    ENNReal.ofReal
      (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
        (.finite q) F (Homogenization.scalarMatrix a0)) ≤
    SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError Q Q.scale s
      Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite q) F a0 := by
  intro q hq
  rcases hq with hq | hq
  · subst q
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.ofReal_homogenizationErrorOnCube_le_paperHomogenizationError
      Q F hSymm hs ha0
  · subst q
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ofReal_homogenizationErrorOnCube_infinity_two_le_paper
      Q F hSymm hs ha0

theorem inputs_J_scalar_error_bounds (d : ℕ) [NeZero d] (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hSymm : ∀ R : Homogenization.TriadicCube d,
      Homogenization.Book.Ch02.CoeffOn.IsSymmetric (F.coeffOn R)) :
    (∀ (a0 : ℝ), 0 < a0 → ∀ (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ (q : ℝ), q = 1 ∨ q = 2 →
      let E : ENNReal := SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError Q Q.scale s
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite q) F a0;
      E ≠ ⊤ ∧
      (1 / 2 : ℝ) * E.toReal ^ 2 ≤
        max (a0⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite q) F)
          (a0 * (Homogenization.Book.Ch02.lambdaSq Q s (.finite q) F)⁻¹) ∧
      max (a0⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite q) F)
          (a0 * (Homogenization.Book.Ch02.lambdaSq Q s (.finite q) F)⁻¹) ≤
        (if q = 1 then (1 + Real.sqrt 2 * E.toReal) ^ 2
         else 1 + 2 * E.toReal ^ 2 + 2 * E.toReal)) := by
  intro a0 ha0 s hs q hq
  let E : ENNReal := SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationError Q Q.scale s
    Homogenization.Book.Ch02.MultiscaleExponent.infinity
    (Homogenization.Book.Ch02.MultiscaleExponent.finite q) F a0
  change E ≠ ⊤ ∧
    (1 / 2 : ℝ) * E.toReal ^ 2 ≤
      max (a0⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite q) F)
        (a0 * (Homogenization.Book.Ch02.lambdaSq Q s (.finite q) F)⁻¹) ∧
    max (a0⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite q) F)
        (a0 * (Homogenization.Book.Ch02.lambdaSq Q s (.finite q) F)⁻¹) ≤
      (if q = 1 then (1 + Real.sqrt 2 * E.toReal) ^ 2
       else 1 + 2 * E.toReal ^ 2 + 2 * E.toReal)
  rcases hq with hq | hq
  · subst q
    have hfiniteCmp := aux_inputs_J_scalar_error_bounds_paper_le_native
      Q F hSymm hs.1 (Or.inl rfl) ha0
    have hfinite : E ≠ ⊤ := by
      apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      simpa [E] using hfiniteCmp
    have hnativePaper := aux_inputs_J_scalar_error_bounds_native_le_paper
      Q F hSymm hs.1 ha0 1 (Or.inl rfl)
    have hnative :
        Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 1) F (Homogenization.scalarMatrix a0) ≤ E.toReal := by
      exact (ENNReal.ofReal_le_iff_le_toReal hfinite).mp (by simpa [E] using hnativePaper)
    have hnativeNonneg :=
      Homogenization.Book.Ch02.HomogenizationErrorOnCube_infinity_one_nonneg
        Q F (Homogenization.scalarMatrix a0) hs.1
    have hpaperLE : E ≤ ENNReal.ofReal
        (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 1) F (Homogenization.scalarMatrix a0)) := by
      simpa [E] using hfiniteCmp
    have hrealLE : E.toReal ≤
        Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 1) F (Homogenization.scalarMatrix a0) :=
      (ENNReal.le_ofReal_iff_toReal_le hfinite hnativeNonneg).mp hpaperLE
    have hrealEq : E.toReal =
        Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 1) F (Homogenization.scalarMatrix a0) := le_antisymm hrealLE hnative
    have hAgg1 :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.sqrt_inv_mul_LambdaSq_le_one_add_sqrt_two_mul_error
        Q F hs.1 ha0
    have hAgg2 :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.sqrt_mul_lambdaSq_inv_le_one_add_sqrt_two_mul_error
        Q F hs.1 ha0
    have hA0 : 0 ≤ a0⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F :=
      mul_nonneg (inv_nonneg.2 ha0.le)
        (Homogenization.Book.Ch02.LambdaSq_nonneg Q F hs.1 (by norm_num))
    have hB0 : 0 ≤ a0 * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹ :=
      mul_nonneg ha0.le
        (inv_nonneg.2 (Homogenization.Book.Ch02.lambdaSq_nonneg Q F hs.1 (by norm_num)))
    have hC : 0 ≤ Real.sqrt 2 * Homogenization.Book.Ch02.HomogenizationErrorOnCube
        Q s .infinity (.finite 1) F (Homogenization.scalarMatrix a0) :=
      mul_nonneg (Real.sqrt_nonneg _) hnativeNonneg
    have hC' : 0 ≤ Real.sqrt 2 * E.toReal :=
      mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
    have hmul : Real.sqrt 2 *
        Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 1) F (Homogenization.scalarMatrix a0) ≤ Real.sqrt 2 * E.toReal :=
      mul_le_mul_of_nonneg_left hnative (Real.sqrt_nonneg _)
    have hroot1 :
        Real.sqrt (a0⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F) ≤
          1 + Real.sqrt 2 * E.toReal := by
      nlinarith [hAgg1, hmul]
    have hroot2 :
        Real.sqrt (a0 * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) ≤
          1 + Real.sqrt 2 * E.toReal := by
      nlinarith [hAgg2, hmul]
    have hA : a0⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F ≤
        (1 + Real.sqrt 2 * E.toReal) ^ 2 := by
      nlinarith [Real.sq_sqrt hA0, Real.sqrt_nonneg (a0⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F), hC',
        sq_nonneg (Real.sqrt (a0⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F) -
          (1 + Real.sqrt 2 * E.toReal))]
    have hB : a0 * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹ ≤
        (1 + Real.sqrt 2 * E.toReal) ^ 2 := by
      nlinarith [Real.sq_sqrt hB0, Real.sqrt_nonneg (a0 * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹), hC',
        sq_nonneg (Real.sqrt (a0 * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) -
          (1 + Real.sqrt 2 * E.toReal))]
    refine ⟨hfinite, ?_, ?_⟩
    · rw [hrealEq]
      exact inputs_J_native_lower_one Q F hSymm hs.1 ha0
    · simp only [ite_true]
      exact max_le hA hB
  · subst q
    have hfiniteCmp := aux_inputs_J_scalar_error_bounds_paper_le_native
      Q F hSymm hs.1 (Or.inr rfl) ha0
    have hfinite : E ≠ ⊤ := by
      apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      simpa [E] using hfiniteCmp
    have hnativePaper := aux_inputs_J_scalar_error_bounds_native_le_paper
      Q F hSymm hs.1 ha0 2 (Or.inr rfl)
    have hnative :
        Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 2) F (Homogenization.scalarMatrix a0) ≤ E.toReal := by
      exact (ENNReal.ofReal_le_iff_le_toReal hfinite).mp (by simpa [E] using hnativePaper)
    have hnativeNonneg : 0 ≤
        Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 2) F (Homogenization.scalarMatrix a0) :=
      SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.homogenizationErrorOnCube_infinity_two_nonneg
        Q F (Homogenization.scalarMatrix a0) hs.1
    have hpaperLE : E ≤ ENNReal.ofReal
        (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 2) F (Homogenization.scalarMatrix a0)) := by
      simpa [E] using hfiniteCmp
    have hrealLE : E.toReal ≤
        Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 2) F (Homogenization.scalarMatrix a0) :=
      (ENNReal.le_ofReal_iff_toReal_le hfinite hnativeNonneg).mp hpaperLE
    have hrealEq : E.toReal =
        Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 2) F (Homogenization.scalarMatrix a0) := le_antisymm hrealLE hnative
    have hLower :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.half_homogenizationErrorOnCube_infinity_two_sq_le_max_weightedEllipticity
        Q F hs.1 ha0
    have hUpper :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ErrorComparison.max_weightedEllipticity_le_one_add_two_mul_sq_add_sqrt_two_mul
        Q F hs.1 ha0
    have hA0 : 0 ≤ a0⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 2) F :=
      mul_nonneg (inv_nonneg.2 ha0.le)
        (Homogenization.Book.Ch02.LambdaSq_nonneg Q F hs.1 (by norm_num))
    have hB0 : 0 ≤ a0 * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 2) F)⁻¹ :=
      mul_nonneg ha0.le
        (inv_nonneg.2 (Homogenization.Book.Ch02.lambdaSq_nonneg Q F hs.1 (by norm_num)))
    have hSq :
        (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 2) F (Homogenization.scalarMatrix a0)) ^ 2 ≤ E.toReal ^ 2 := by
      rw [hrealEq]
    have hsqrt2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hlin : Real.sqrt 2 *
        Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 2) F (Homogenization.scalarMatrix a0) ≤ 2 * E.toReal :=
      calc
        Real.sqrt 2 *
            Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
              (.finite 2) F (Homogenization.scalarMatrix a0) ≤
          2 * Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
              (.finite 2) F (Homogenization.scalarMatrix a0) :=
          mul_le_mul_of_nonneg_right hsqrt2 hnativeNonneg
        _ ≤ 2 * E.toReal := mul_le_mul_of_nonneg_left hnative (by norm_num)
    refine ⟨hfinite, ?_, ?_⟩
    · rw [hrealEq]
      exact hLower
    · have hmax := hUpper
      have hsq_le :
          2 * (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
            (.finite 2) F (Homogenization.scalarMatrix a0)) ^ 2 ≤ 2 * E.toReal ^ 2 :=
        mul_le_mul_of_nonneg_left hSq (by norm_num)
      rw [← hrealEq] at hmax hsq_le hlin
      simp only [ite_eq_right (by norm_num : (2 : ℝ) ≠ 1)]
      nlinarith [hmax, hsq_le, hlin]

end SubdiffusiveProcess.Paper
