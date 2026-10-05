module

public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusSigned

@[expose] public section

open MeasureTheory Filter Set Topology

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X]

/-- Integration against a signed measure agrees with any finite-measure difference presentation. -/
theorem signedIntegralOn_of_measure_difference {ν : SignedMeasure X} {μ ρ : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (hν : ν = μ.toSignedMeasure - ρ.toSignedMeasure) {f : X → ℝ}
    (hfν : SignedIntegrable ν f) (hfμ : Integrable f μ) (hfρ : Integrable f ρ)
    (B : Set X) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B f = (∫ x in B, f x ∂μ) - ∫ x in B, f x ∂ρ := by
  have hJ := ν.toSignedMeasure_toJordanDecomposition
  change ν.toJordanDecomposition.posPart.toSignedMeasure -
    ν.toJordanDecomposition.negPart.toSignedMeasure = ν at hJ
  have heq : μ + ν.toJordanDecomposition.negPart = ρ + ν.toJordanDecomposition.posPart := by
    apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    apply sub_eq_zero.mp
    calc
      _ = (μ.toSignedMeasure - ρ.toSignedMeasure) -
          (ν.toJordanDecomposition.posPart.toSignedMeasure -
            ν.toJordanDecomposition.negPart.toSignedMeasure) := by abel
      _ = ν - ν := by rw [← hν, hJ]
      _ = 0 := sub_self _
  have hi := congrArg (fun θ : Measure X => ∫ x in B, f x ∂θ) heq
  rw [Measure.restrict_add, Measure.restrict_add,
    integral_add_measure hfμ.integrableOn hfν.2.integrableOn,
    integral_add_measure hfρ.integrableOn hfν.1.integrableOn] at hi
  unfold _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn
  linarith only [hi]

theorem signedIntegralOn_add_measure {ν ρ : SignedMeasure X} {f : X → ℝ}
    (hfν : SignedIntegrable ν f) (hfρ : SignedIntegrable ρ f)
    (hfadd : SignedIntegrable (ν + ρ) f) (B : Set X) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (ν + ρ) B f =
      _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B f + _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ρ B f := by
  have heq : ν + ρ =
      (ν.toJordanDecomposition.posPart + ρ.toJordanDecomposition.posPart).toSignedMeasure -
        (ν.toJordanDecomposition.negPart + ρ.toJordanDecomposition.negPart).toSignedMeasure := by
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition, ← ρ.toSignedMeasure_toJordanDecomposition]
    simp only [JordanDecomposition.toSignedMeasure]
    abel
  rw [signedIntegralOn_of_measure_difference heq hfadd
    (integrable_add_measure.mpr ⟨hfν.1, hfρ.1⟩) (integrable_add_measure.mpr ⟨hfν.2, hfρ.2⟩) B]
  rw [Measure.restrict_add, Measure.restrict_add,
    integral_add_measure hfν.1.integrableOn hfρ.1.integrableOn,
    integral_add_measure hfν.2.integrableOn hfρ.2.integrableOn]
  simp only [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn]
  ring

theorem signedIntegralOn_smul_measure (ν : SignedMeasure X) (c : ℝ) (hc : 0 ≤ c)
    (B : Set X) (f : X → ℝ) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (c • ν) B f =
      c * _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B f := by
  simp only [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn, SignedMeasure.toJordanDecomposition_smul_real,
    JordanDecomposition.real_smul_posPart_nonneg _ _ hc,
    JordanDecomposition.real_smul_negPart_nonneg _ _ hc, Measure.restrict_smul,
    integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hc]
  ring

section Core

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
  {m : Measure X} {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}

theorem EnergyFamily.core_integrable (h : Data F U) (Γ : EnergyFamily F U)
    {u : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u) {f : X → ℝ} (hf : Continuous f) :
    Integrable f (Γ.measure u) := by
  let : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu.1⟩
  obtain ⟨g, hg, hgc, hgU, hgae⟩ := hu.2
  have hr : (Γ.measure u).restrict (tsupport g) = Γ.measure u :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (Γ.measure_compl_tsupport h hu.1 hgae))
  have hi := hf.continuousOn.integrableOn_compact (μ := Γ.measure u) hgc
  change Integrable f ((Γ.measure u).restrict (tsupport g)) at hi
  rwa [hr] at hi

theorem EnergyFamily.core_signedIntegrable (h : Data F U) (Γ : EnergyFamily F U)
    {u v : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u) (hv : v ∈ F.domain)
    {f : X → ℝ} (hf : Continuous f) : SignedIntegrable (Γ.cross u v) f := by
  obtain ⟨g, hg, hgc, hgU, hgae⟩ := hu.2
  have hz := (Γ.cross_variation_ac_left hu.1 hv) (Γ.measure_compl_tsupport h hu.1 hgae)
  exact signedIntegrable_of_compact_carrier (Γ.cross u v) hgc hz hf

theorem EnergyFamily.signedIntegralOn_self (h : Data F U) (Γ : EnergyFamily F U)
    {u : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u) {f : X → ℝ}
    (hf : Continuous f) (B : Set X) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross u u) B f = ∫ x in B, f x ∂Γ.measure u := by
  let : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu.1⟩
  have heq : Γ.cross u u = (Γ.measure u).toSignedMeasure - (0 : Measure X).toSignedMeasure := by
    ext A hA
    rw [sub_apply, Measure.toSignedMeasure_apply_measurable hA,
      Measure.toSignedMeasure_zero, zero_apply, sub_zero, Γ.cross_self u hu.1 A hA]
    rfl
  rw [signedIntegralOn_of_measure_difference heq (Γ.core_signedIntegrable h hu hu.1 hf)
    (Γ.core_integrable h hu hf) (by simp) B]
  simp only [Measure.restrict_zero, integral_zero_measure, sub_zero]

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
theorem signedIntegralOn_neg_measure {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [_t2 : T2Space X] [_lc : LocallyCompactSpace X] [_borel : BorelSpace X]
    (ν : SignedMeasure X) (B : Set X) (f : X → ℝ) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (-ν) B f =
      -_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B f := by
  simp only [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn, SignedMeasure.toJordanDecomposition_neg,
    JordanDecomposition.neg_posPart, JordanDecomposition.neg_negPart]
  ring

theorem signedIntegralOn_smul_measure_real (ν : SignedMeasure X) (c : ℝ)
    (B : Set X) (f : X → ℝ) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (c • ν) B f =
      c * _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B f := by
  rcases le_or_gt 0 c with hc | hc
  · exact signedIntegralOn_smul_measure ν c hc B f
  · rw [show c • ν = -((-c) • ν) by module, signedIntegralOn_neg_measure,
      signedIntegralOn_smul_measure ν (-c) (by linarith) B f]
    ring

theorem EnergyFamily.signedIntegralOn_cross_add_left (h : Data F U) (Γ : EnergyFamily F U)
    {u v w : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hv : F.toClosedForm.MemCoreOn U v) (hw : w ∈ F.domain)
    {f : X → ℝ} (hf : Continuous f) (B : Set X) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross (u + v) w) B f =
      _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross u w) B f +
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross v w) B f := by
  have hs := Γ.core_signedIntegrable h (hu.add hv) hw hf
  rw [Γ.cross_add_left hu.1 hv.1 hw] at hs ⊢
  exact signedIntegralOn_add_measure (Γ.core_signedIntegrable h hu hw hf)
    (Γ.core_signedIntegrable h hv hw hf) hs B

theorem EnergyFamily.signedIntegralOn_cross_add_right (h : Data F U) (Γ : EnergyFamily F U)
    {u v w : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hv : v ∈ F.domain) (hw : w ∈ F.domain)
    {f : X → ℝ} (hf : Continuous f) (B : Set X) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross u (v + w)) B f =
      _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross u v) B f +
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross u w) B f := by
  have hs := Γ.core_signedIntegrable h hu (F.domain.add_mem hv hw) hf
  rw [Γ.cross_add_right u hu.1 v hv w hw] at hs ⊢
  exact signedIntegralOn_add_measure (Γ.core_signedIntegrable h hu hv hf)
    (Γ.core_signedIntegrable h hu hw hf) hs B

theorem EnergyFamily.integral_measure_smul (h : Data F U) (Γ : EnergyFamily F U)
    {u : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u) (c : ℝ)
    {f : X → ℝ} (hf : Continuous f) (B : Set X) :
    (∫ x in B, f x ∂Γ.measure (c • u)) = c ^ 2 * ∫ x in B, f x ∂Γ.measure u := by
  rw [← Γ.signedIntegralOn_self h (hu.smul c) hf,
    Γ.cross_smul_left c hu.1 (F.domain.smul_mem c hu.1), Γ.cross_smul_right c u hu.1 u hu.1,
    signedIntegralOn_smul_measure_real, signedIntegralOn_smul_measure_real,
    Γ.signedIntegralOn_self h hu hf]
  ring

theorem EnergyFamily.integral_measure_add (h : Data F U) (Γ : EnergyFamily F U)
    {u v : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hv : F.toClosedForm.MemCoreOn U v) {f : X → ℝ} (hf : Continuous f) (B : Set X) :
    (∫ x in B, f x ∂Γ.measure (u + v)) = (∫ x in B, f x ∂Γ.measure u) +
      2 * _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross u v) B f + ∫ x in B, f x ∂Γ.measure v := by
  rw [← Γ.signedIntegralOn_self h (hu.add hv) hf,
    Γ.signedIntegralOn_cross_add_left h hu hv (F.domain.add_mem hu.1 hv.1) hf,
    Γ.signedIntegralOn_cross_add_right h hu hu.1 hv.1 hf,
    Γ.signedIntegralOn_cross_add_right h hv hu.1 hv.1 hf,
    Γ.cross_symm v hv.1 u hu.1, Γ.signedIntegralOn_self h hu hf,
    Γ.signedIntegralOn_self h hv hf]
  ring

theorem EnergyFamily.integral_measure_sub (h : Data F U) (Γ : EnergyFamily F U)
    {u v : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hv : F.toClosedForm.MemCoreOn U v) {f : X → ℝ} (hf : Continuous f) (B : Set X) :
    (∫ x in B, f x ∂Γ.measure (u - v)) = (∫ x in B, f x ∂Γ.measure u) -
      2 * _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross u v) B f + ∫ x in B, f x ∂Γ.measure v := by
  rw [show u - v = u + (-1 : ℝ) • v by module,
    Γ.integral_measure_add h hu (hv.smul (-1)) hf,
    Γ.integral_measure_smul h hv (-1) hf, Γ.cross_smul_right (-1) u hu.1 v hv.1,
    signedIntegralOn_smul_measure_real]
  ring

theorem EnergyFamily.signedIntegralOn_sum_sub (h : Data F U) (Γ : EnergyFamily F U)
    {u v : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    (hv : F.toClosedForm.MemCoreOn U v) {f : X → ℝ} (hf : Continuous f) (B : Set X) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross (u + v) (u - v)) B f =
      (∫ x in B, f x ∂Γ.measure u) - ∫ x in B, f x ∂Γ.measure v := by
  rw [show u - v = u + (-1 : ℝ) • v by module,
    Γ.signedIntegralOn_cross_add_left h hu hv (F.domain.add_mem hu.1 (F.domain.smul_mem (-1) hv.1)) hf,
    Γ.signedIntegralOn_cross_add_right h hu hu.1 (F.domain.smul_mem (-1) hv.1) hf,
    Γ.signedIntegralOn_cross_add_right h hv hu.1 (F.domain.smul_mem (-1) hv.1) hf,
    Γ.cross_smul_right (-1) u hu.1 v hv.1, Γ.cross_smul_right (-1) v hv.1 v hv.1,
    signedIntegralOn_smul_measure_real, signedIntegralOn_smul_measure_real,
    Γ.cross_symm v hv.1 u hu.1, Γ.signedIntegralOn_self h hu hf, Γ.signedIntegralOn_self h hv hf]
  ring

end Core

end SubdiffusiveProcess.DirichletForm.FOTConstruction
