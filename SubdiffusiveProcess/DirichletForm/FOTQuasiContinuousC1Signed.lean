import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssemblySigned

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X]

/-- Bounded integration is additive in the signed measure. -/
theorem c1_signedIntegral_add (s t : SignedMeasure X) (B : Set X) (hB : MeasurableSet B)
    (f : X → ℝ) (hf : Measurable f) (R : ℝ) (hR : ∀ x, ‖f x‖ ≤ R) :
    signedIntegralOn (s + t) B f = signedIntegralOn s B f + signedIntegralOn t B f := by
  let p := s.toJordanDecomposition.posPart + t.toJordanDecomposition.posPart
  let n := s.toJordanDecomposition.negPart + t.toJordanDecomposition.negPart
  have hs : s + t = p.toSignedMeasure - n.toSignedMeasure := by
    dsimp only [p, n]
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    calc
      s + t = s.toJordanDecomposition.toSignedMeasure + t.toJordanDecomposition.toSignedMeasure :=
        congrArg₂ (· + ·) s.toSignedMeasure_toJordanDecomposition.symm t.toSignedMeasure_toJordanDecomposition.symm
      _ = _ := by
        change (_ - _) + (_ - _) = (_ + _) - (_ + _)
        abel
  have hi : ∀ ρ : Measure X, IsFiniteMeasure ρ → Integrable f ρ := by
    intro ρ hρ
    letI := hρ
    exact (integrable_const R).mono' hf.aestronglyMeasurable (Eventually.of_forall hR)
  rw [assembly_signedIntegral_sub p n (s + t) hs B hB f hf R hR]
  dsimp only [p, n]
  simp only [Measure.restrict_add, signedIntegralOn]
  rw [integral_add_measure (hi _ inferInstance).integrableOn (hi _ inferInstance).integrableOn,
    integral_add_measure (hi _ inferInstance).integrableOn (hi _ inferInstance).integrableOn]
  ring

/-- Bounded integration commutes with negation of the signed measure. -/
theorem c1_signedIntegral_neg (s : SignedMeasure X) (B : Set X) (f : X → ℝ) :
    signedIntegralOn (-s) B f = -signedIntegralOn s B f := by
  simp only [signedIntegralOn, SignedMeasure.toJordanDecomposition_neg,
    JordanDecomposition.neg_posPart, JordanDecomposition.neg_negPart]
  ring

/-- A setwise signed-measure bound controls bounded integration. -/
theorem c1_signedIntegral_bound (s : SignedMeasure X) (B : Set X)
    (f : X → ℝ) (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ x, ‖f x‖ ≤ R)
    (C : ℝ) (hC : ∀ A, MeasurableSet A → |s A| ≤ C) :
    |signedIntegralOn s B f| ≤ 2 * R * C := by
  obtain ⟨i, hi, hipos, hineg, hp, hn⟩ := s.toJordanDecomposition_spec
  have hposmass : (s.toJordanDecomposition.posPart univ).toReal ≤ C := by
    change s.toJordanDecomposition.posPart.real univ ≤ C
    rw [hp, SignedMeasure.toMeasureOfZeroLE_real_apply _ _ _ MeasurableSet.univ, inter_univ]
    exact (le_abs_self (s i)).trans (hC i hi)
  have hnegmass : (s.toJordanDecomposition.negPart univ).toReal ≤ C := by
    change s.toJordanDecomposition.negPart.real univ ≤ C
    rw [hn, SignedMeasure.toMeasureOfLEZero_real_apply _ _ _ MeasurableSet.univ, inter_univ]
    exact (neg_le_abs (s iᶜ)).trans (hC iᶜ hi.compl)
  have hiR : ∀ ρ : Measure X, IsFiniteMeasure ρ →
      |∫ x in B, f x ∂ρ| ≤ R * (ρ univ).toReal := by
    intro ρ hρ
    letI := hρ
    have hh : |∫ x in B, f x ∂ρ| ≤ R * (ρ.restrict B univ).toReal :=
      norm_integral_le_of_norm_le_const (ae_restrict_of_ae (Eventually.of_forall hR))
    exact hh.trans (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (_root_.MeasureTheory.measure_ne_top ρ univ)
        (by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]; exact measure_mono (subset_univ B))) hR0)
  unfold signedIntegralOn
  calc
    _ ≤ |∫ x in B, f x ∂s.toJordanDecomposition.posPart| +
        |∫ x in B, f x ∂s.toJordanDecomposition.negPart| := abs_sub _ _
    _ ≤ R * (s.toJordanDecomposition.posPart univ).toReal +
        R * (s.toJordanDecomposition.negPart univ).toReal := add_le_add (hiR _ inferInstance) (hiR _ inferInstance)
    _ ≤ R * C + R * C := add_le_add
      (mul_le_mul_of_nonneg_left hposmass hR0) (mul_le_mul_of_nonneg_left hnegmass hR0)
    _ = _ := by ring

/-- Signed integrals are continuous for uniform setwise convergence. -/
theorem c1_signedIntegral_sub_bound (s t : SignedMeasure X) (B : Set X) (hB : MeasurableSet B)
    (f : X → ℝ) (hf : Measurable f) (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ x, ‖f x‖ ≤ R)
    (C : ℝ) (hC : ∀ A, MeasurableSet A → |(s - t) A| ≤ C) :
    |signedIntegralOn s B f - signedIntegralOn t B f| ≤ 2 * R * C := by
  have hh := c1_signedIntegral_add s (-t) B hB f hf R hR
  rw [c1_signedIntegral_neg] at hh
  rw [← sub_eq_add_neg, ← sub_eq_add_neg] at hh
  rw [← hh]
  exact c1_signedIntegral_bound (s - t) B f R hR0 hR C hC

variable [TopologicalSpace X] {m : Measure X}

/-- The cross energy measure has a uniform global bound. -/
theorem EnergyFamily.cross_global_bound {F : _root_.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) {u v : Lp ℝ 2 m} (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    {B : Set X} (hB : MeasurableSet B) :
    |Γ.cross u v B| ≤ Real.sqrt (F.form u u) * Real.sqrt (F.form v v) := by
  exact (Γ.cross_le u hu v hv B hB).trans (mul_le_mul
    (Real.sqrt_le_sqrt (Γ.toReal_measure_le_form hu B))
    (Real.sqrt_le_sqrt (Γ.toReal_measure_le_form hv B)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Cross energy measures vary continuously when their arguments vary in energy. -/
theorem EnergyFamily.cross_difference_bound {F : _root_.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) {p r u : Lp ℝ 2 m} (hp : p ∈ F.domain) (hr : r ∈ F.domain)
    (hu : u ∈ F.domain) {C : ℝ} (hrC : Real.sqrt (F.form r r) ≤ C)
    (huC : Real.sqrt (F.form u u) ≤ C) {B : Set X} (hB : MeasurableSet B) :
    |(Γ.cross p r - Γ.cross u u) B| ≤ C *
      (Real.sqrt (F.form (p - u) (p - u)) + Real.sqrt (F.form (r - u) (r - u))) := by
  have hpu := F.domain.sub_mem hp hu
  have hru := F.domain.sub_mem hr hu
  have h1 := Γ.cross_add_left hu hpu hr
  have h2 := Γ.cross_add_right u hu u hu (r - u) hru
  have hpeq : u + (p - u) = p := by abel
  have hreq : u + (r - u) = r := by abel
  rw [hpeq] at h1
  rw [hreq] at h2
  have hsplit : Γ.cross p r - Γ.cross u u = Γ.cross (p - u) r + Γ.cross u (r - u) := by
    rw [h1, h2]
    abel
  rw [hsplit, VectorMeasure.add_apply]
  calc
    _ ≤ |Γ.cross (p - u) r B| + |Γ.cross u (r - u) B| := abs_add_le _ _
    _ ≤ Real.sqrt (F.form (p - u) (p - u)) * Real.sqrt (F.form r r) +
        Real.sqrt (F.form u u) * Real.sqrt (F.form (r - u) (r - u)) :=
      add_le_add (Γ.cross_global_bound hpu hr hB) (Γ.cross_global_bound hu hru hB)
    _ ≤ Real.sqrt (F.form (p - u) (p - u)) * C +
        C * Real.sqrt (F.form (r - u) (r - u)) := add_le_add
      (mul_le_mul_of_nonneg_left hrC (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_right huC (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- On the diagonal, signed and positive energy measures agree. -/
theorem EnergyFamily.cross_self_signed {F : _root_.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) {u : Lp ℝ 2 m} (hu : u ∈ F.domain)
    [IsFiniteMeasure (Γ.measure u)] : Γ.cross u u = (Γ.measure u).toSignedMeasure := by
  apply VectorMeasure.ext
  intro B hB
  rw [Γ.cross_self u hu B hB, Measure.toSignedMeasure_apply_measurable hB, measureReal_def]

/-- Diagonal signed integration reduces to positive integration. -/
theorem EnergyFamily.cross_self_integral {F : _root_.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) {u : Lp ℝ 2 m} (hu : u ∈ F.domain)
    (B : Set X) (hB : MeasurableSet B) (f : X → ℝ) (hf : Measurable f)
    (R : ℝ) (hR : ∀ x, ‖f x‖ ≤ R) :
    signedIntegralOn (Γ.cross u u) B f = ∫ x in B, f x ∂Γ.measure u := by
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu⟩
  have hs : Γ.cross u u = (Γ.measure u).toSignedMeasure - (0 : Measure X).toSignedMeasure := by
    rw [Γ.cross_self_signed hu, Measure.toSignedMeasure_zero, sub_zero]
  rw [assembly_signedIntegral_sub _ _ _ hs B hB f hf R hR, Measure.restrict_zero, integral_zero_measure, sub_zero]

end DirichletForm.FOTConstruction
