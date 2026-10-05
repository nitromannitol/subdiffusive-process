module

public import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssemblyContinuity
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

@[expose] public section

open MeasureTheory Filter Set Topology

noncomputable section
namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X]

/-- Signed integration depends on the signed measure, independently of the
chosen difference of finite positive measures. -/
theorem assembly_signedIntegral_sub (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : SignedMeasure X) (hs : s = μ.toSignedMeasure - ν.toSignedMeasure)
    (B : Set X) (_hB : MeasurableSet B) (f : X → ℝ) (hf : Measurable f)
    (R : ℝ) (hR : ∀ x, ‖f x‖ ≤ R) :
    signedIntegralOn s B f = (∫ x in B, f x ∂μ) - ∫ x in B, f x ∂ν := by
  have hi : ∀ ρ : Measure X, IsFiniteMeasure ρ → Integrable f ρ := by
    intro ρ hρ
    let := hρ
    exact (integrable_const R).mono' hf.aestronglyMeasurable (Eventually.of_forall hR)
  let p := s.toJordanDecomposition.posPart
  let n := s.toJordanDecomposition.negPart
  have hpn : p.toSignedMeasure - n.toSignedMeasure = s :=
    s.toSignedMeasure_toJordanDecomposition
  have heq : μ + n = ν + p := by
    apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add.mp (hpn.trans hs)).symm
  have hint := congrArg (fun ρ : Measure X => ∫ x in B, f x ∂ρ) heq
  rw [Measure.restrict_add, Measure.restrict_add,
    integral_add_measure (hi μ inferInstance).integrableOn (hi n inferInstance).integrableOn,
    integral_add_measure (hi ν inferInstance).integrableOn (hi p inferInstance).integrableOn] at hint
  change (∫ x in B, f x ∂p) - (∫ x in B, f x ∂n) = _
  linarith

/-- Restricting a signed measure restricts its integral. -/
theorem assembly_signedIntegral_restrict (s : SignedMeasure X) {O B : Set X}
    (hO : MeasurableSet O) (hB : MeasurableSet B) (f : X → ℝ) (hf : Measurable f)
    (R : ℝ) (hR : ∀ x, ‖f x‖ ≤ R) :
    signedIntegralOn (s.restrict O) B f = signedIntegralOn s (B ∩ O) f := by
  have hs : s.restrict O =
      (s.toJordanDecomposition.posPart.restrict O).toSignedMeasure -
        (s.toJordanDecomposition.negPart.restrict O).toSignedMeasure := by
    rw [← Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hO,
      ← Measure.toSignedMeasure_restrict_eq_restrict_toSignedMeasure _ _ hO,
      ← VectorMeasure.restrict_sub]
    exact congrArg (fun v : SignedMeasure X => v.restrict O)
      s.toSignedMeasure_toJordanDecomposition.symm
  rw [assembly_signedIntegral_sub _ _ _ hs B hB f hf R hR]
  simp only [signedIntegralOn, Measure.restrict_restrict hB]

/-- Equality of restrictions identifies bounded weighted integrals on a subset. -/
theorem assembly_signedIntegral_eq_of_restrict {s t : SignedMeasure X} {O B : Set X}
    (hO : MeasurableSet O) (hB : MeasurableSet B) (hBO : B ⊆ O)
    (hst : s.restrict O = t.restrict O) (f : X → ℝ) (hf : Measurable f)
    (R : ℝ) (hR : ∀ x, ‖f x‖ ≤ R) :
    signedIntegralOn s B f = signedIntegralOn t B f := by
  rw [← inter_eq_left.mpr hBO,
    ← assembly_signedIntegral_restrict s hO hB f hf R hR,
    ← assembly_signedIntegral_restrict t hO hB f hf R hR, hst]

/-- A uniform setwise bound controls the integral of a bounded function. -/
theorem assembly_integral_sub_bound (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X → ℝ) (hf : Measurable f) (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ x, ‖f x‖ ≤ R)
    (C : ℝ) (hC : ∀ B, MeasurableSet B → |(μ B).toReal - (ν B).toReal| ≤ C) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ 2 * R * C := by
  let s : SignedMeasure X := μ.toSignedMeasure - ν.toSignedMeasure
  have hsc : ∀ B, MeasurableSet B → |s B| ≤ C := by
    intro B hB
    simpa only [s, sub_apply, Measure.toSignedMeasure_apply_measurable hB,
      measureReal_def] using hC B hB
  obtain ⟨i, hi, hipos, hineg, hp, hn⟩ := s.toJordanDecomposition_spec
  have hposmass : (s.toJordanDecomposition.posPart univ).toReal ≤ C := by
    change s.toJordanDecomposition.posPart.real univ ≤ C
    rw [hp, SignedMeasure.toMeasureOfZeroLE_real_apply _ _ _ MeasurableSet.univ, inter_univ]
    exact
      (le_abs_self (s i)).trans (hsc i hi)
  have hnegmass : (s.toJordanDecomposition.negPart univ).toReal ≤ C := by
    change s.toJordanDecomposition.negPart.real univ ≤ C
    rw [hn, SignedMeasure.toMeasureOfLEZero_real_apply _ _ _ MeasurableSet.univ, inter_univ]
    exact
      (neg_le_abs (s iᶜ)).trans (hsc iᶜ hi.compl)
  have hiR : ∀ ρ : Measure X, IsFiniteMeasure ρ →
      |∫ x, f x ∂ρ| ≤ R * (ρ univ).toReal := by
    intro ρ hρ
    let := hρ
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall hR)
  have hint := assembly_signedIntegral_sub μ ν s rfl univ .univ f hf R hR
  simp only [Measure.restrict_univ] at hint
  rw [← hint]
  simp only [signedIntegralOn, Measure.restrict_univ]
  calc
    _ ≤ |∫ x, f x ∂s.toJordanDecomposition.posPart| +
        |∫ x, f x ∂s.toJordanDecomposition.negPart| := abs_sub _ _
    _ ≤ R * (s.toJordanDecomposition.posPart univ).toReal +
        R * (s.toJordanDecomposition.negPart univ).toReal :=
      add_le_add (hiR _ inferInstance) (hiR _ inferInstance)
    _ ≤ R * C + R * C := add_le_add
      (mul_le_mul_of_nonneg_left hposmass hR0) (mul_le_mul_of_nonneg_left hnegmass hR0)
    _ = _ := by ring

end SubdiffusiveProcess.DirichletForm.FOTConstruction
