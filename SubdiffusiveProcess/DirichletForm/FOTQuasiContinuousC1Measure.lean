module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyFamily

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X]

/-- Uniform setwise control of finite measures controls every bounded integral. -/
theorem bounded_integral_difference_bound (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hbound : ∀ B : Set X, MeasurableSet B → |(μ B).toReal - (ν B).toReal| ≤ C)
    {f : X → ℝ} (hf : Measurable f) (hfK : ∀ x, |f x| ≤ K) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ 2 * K * C := by
  let s : SignedMeasure X := μ.toSignedMeasure - ν.toSignedMeasure
  let J := s.toJordanDecomposition
  have hJ : μ.toSignedMeasure - ν.toSignedMeasure = J.posPart.toSignedMeasure - J.negPart.toSignedMeasure :=
    (SignedMeasure.toSignedMeasure_toJordanDecomposition s).symm
  obtain ⟨P, hP, hpP, hnPc⟩ := J.mutuallySingular
  have heval : ∀ B : Set X, MeasurableSet B →
      (μ B).toReal - (ν B).toReal = (J.posPart B).toReal - (J.negPart B).toReal := by
    intro B hB
    change μ.real B - ν.real B = J.posPart.real B - J.negPart.real B
    rw [← Measure.toSignedMeasure_sub_apply hB, hJ, Measure.toSignedMeasure_sub_apply hB]
  have hpmass : (J.posPart univ).toReal ≤ C := by
    have hsum : J.posPart univ = J.posPart P + J.posPart Pᶜ := by
      rw [← measure_union disjoint_compl_right hP.compl, union_compl_self]
    rw [hsum, hpP, zero_add]
    have hb := hbound Pᶜ hP.compl
    rw [heval Pᶜ hP.compl, hnPc, ENNReal.toReal_zero, sub_zero,
      abs_of_nonneg ENNReal.toReal_nonneg] at hb
    exact hb
  have hnmass : (J.negPart univ).toReal ≤ C := by
    have hsum : J.negPart univ = J.negPart P + J.negPart Pᶜ := by
      rw [← measure_union disjoint_compl_right hP.compl, union_compl_self]
    rw [hsum, hnPc, add_zero]
    have hb := hbound P hP
    rw [heval P hP, hpP, ENNReal.toReal_zero, zero_sub, abs_neg,
      abs_of_nonneg ENNReal.toReal_nonneg] at hb
    exact hb
  have hmeasures : μ + J.negPart = ν + J.posPart := by
    apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    exact (sub_eq_sub_iff_add_eq_add.mp hJ).trans (add_comm _ _)
  have hint : ∀ (ρ : Measure X) [IsFiniteMeasure ρ], Integrable f ρ := by
    intro ρ _
    exact (integrable_const K).mono' hf.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hfK x)
  have hid : (∫ x, f x ∂μ) - ∫ x, f x ∂ν =
      (∫ x, f x ∂J.posPart) - ∫ x, f x ∂J.negPart := by
    have hh := congrArg (fun ρ : Measure X => ∫ x, f x ∂ρ) hmeasures
    rw [integral_add_measure (hint μ) (hint J.negPart),
      integral_add_measure (hint ν) (hint J.posPart)] at hh
    linarith
  have hp : |∫ x, f x ∂J.posPart| ≤ K * (J.posPart univ).toReal := by
    simpa only [Real.norm_eq_abs, measureReal_def] using norm_integral_le_of_norm_le_const
      (μ := J.posPart) (f := f) (C := K) (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hfK x)
  have hn : |∫ x, f x ∂J.negPart| ≤ K * (J.negPart univ).toReal := by
    simpa only [Real.norm_eq_abs, measureReal_def] using norm_integral_le_of_norm_le_const
      (μ := J.negPart) (f := f) (C := K) (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hfK x)
  rw [hid]
  have hp' := mul_le_mul_of_nonneg_left hpmass hK
  have hn' := mul_le_mul_of_nonneg_left hnmass hK
  exact (abs_sub _ _).trans (by linarith)

/-- The bounded-integral estimate also holds after restriction to a measurable set. -/
theorem bounded_setIntegral_difference_bound (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hbound : ∀ A : Set X, MeasurableSet A → |(μ A).toReal - (ν A).toReal| ≤ C)
    {f : X → ℝ} (hf : Measurable f) (hfK : ∀ x, |f x| ≤ K)
    {B : Set X} (hB : MeasurableSet B) :
    |(∫ x in B, f x ∂μ) - ∫ x in B, f x ∂ν| ≤ 2 * K * C := by
  apply bounded_integral_difference_bound (μ.restrict B) (ν.restrict B) hC hK _ hf hfK
  intro A hA
  simpa only [Measure.restrict_apply hA] using hbound (A ∩ B) (hA.inter hB)

end DirichletForm.FOTConstruction
