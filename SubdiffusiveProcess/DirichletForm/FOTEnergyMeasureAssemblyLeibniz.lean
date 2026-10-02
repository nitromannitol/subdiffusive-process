import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssemblyLocalCore

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] [SecondCountableTopology X] {m : Measure X}

/-- Gluing the relative-core identities across a cutoff cover proves Leibniz
for globally compact continuous representatives. -/
theorem EnergyFamily.leibniz_compact {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U)
    {u v : Lp ℝ 2 m} (hu : F.toClosedForm.MemCore u) (hv : F.toClosedForm.MemCore v)
    {uc vc : X → ℝ} (huc : Continuous uc) (hvc : Continuous vc)
    (hucc : HasCompactSupport uc) (hvcc : HasCompactSupport vc)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ) {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => vc x * Φ (uc x)) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure w B).toReal =
      (∫ x in B, vc x ^ 2 * deriv Φ (uc x) ^ 2 ∂Γ.measure u) +
        2 * signedIntegralOn (Γ.cross u v) B
          (fun x => vc x * Φ (uc x) * deriv Φ (uc x)) +
        (∫ x in B, Φ (uc x) ^ 2 ∂Γ.measure v) := by
  let f1 : X → ℝ := fun x => vc x ^ 2 * deriv Φ (uc x) ^ 2
  let f2 : X → ℝ := fun x => vc x * Φ (uc x) * deriv Φ (uc x)
  let f3 : X → ℝ := fun x => Φ (uc x) ^ 2
  have hd : Continuous (fun x => deriv Φ (uc x)) :=
    (hΦ.continuous_deriv (by norm_num)).comp huc
  have hf1 : Continuous f1 := (hvc.pow 2).mul (hd.pow 2)
  have hf2 : Continuous f2 := (hvc.mul (hΦ.continuous.comp huc)).mul hd
  have hf3 : Continuous f3 := (hΦ.continuous.comp huc).pow 2
  have hf1c : HasCompactSupport f1 := by
    have hc : HasCompactSupport
        (fun x => (vc x * vc x) * (deriv Φ (uc x) * deriv Φ (uc x))) :=
      hvcc.mul_right.mul_right
    simpa only [f1, pow_two] using hc
  have hf2c : HasCompactSupport f2 := hvcc.mul_right.mul_right
  obtain ⟨C1, hC1⟩ := hf1c.exists_bound_of_continuous hf1
  obtain ⟨C2, hC2⟩ := hf2c.exists_bound_of_continuous hf2
  have hΦsquare : Continuous (fun s : ℝ => Φ s ^ 2) := hΦ.continuous.pow 2
  obtain ⟨C3, hC3'⟩ := (hucc.isCompact_range huc).exists_bound_of_continuousOn
    (f := fun s : ℝ => Φ s ^ 2) hΦsquare.continuousOn
  have hC3 : ∀ x, ‖f3 x‖ ≤ C3 := fun x => hC3' _ (mem_range_self x)
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu.1⟩
  letI : IsFiniteMeasure (Γ.measure v) := ⟨Γ.finite v hv.1⟩
  letI : IsFiniteMeasure (Γ.measure w) := ⟨Γ.finite w hw⟩
  have hi1 : Integrable f1 (Γ.measure u) :=
    (integrable_const C1).mono' hf1.measurable.aestronglyMeasurable (Eventually.of_forall hC1)
  have hi2p : Integrable f2 (Γ.cross u v).toJordanDecomposition.posPart :=
    (integrable_const C2).mono' hf2.measurable.aestronglyMeasurable (Eventually.of_forall hC2)
  have hi2n : Integrable f2 (Γ.cross u v).toJordanDecomposition.negPart :=
    (integrable_const C2).mono' hf2.measurable.aestronglyMeasurable (Eventually.of_forall hC2)
  have hi3 : Integrable f3 (Γ.measure v) :=
    (integrable_const C3).mono' hf3.measurable.aestronglyMeasurable (Eventually.of_forall hC3)
  let A : SignedMeasure X := (Γ.measure w).toSignedMeasure
  let S : SignedMeasure X := (Γ.measure u).withDensityᵥ f1 +
    (2 : ℝ) • ((Γ.cross u v).toJordanDecomposition.posPart.withDensityᵥ f2 -
      (Γ.cross u v).toJordanDecomposition.negPart.withDensityᵥ f2) +
        (Γ.measure v).withDensityᵥ f3
  have hS : ∀ T : Set X, MeasurableSet T → S T =
      (∫ x in T, f1 x ∂Γ.measure u) + 2 * signedIntegralOn (Γ.cross u v) T f2 +
        ∫ x in T, f3 x ∂Γ.measure v := by
    intro T hT
    simp only [S, VectorMeasure.add_apply, VectorMeasure.smul_apply, VectorMeasure.sub_apply,
      smul_eq_mul, withDensityᵥ_apply hi1 hT, withDensityᵥ_apply hi2p hT,
      withDensityᵥ_apply hi2n hT, withDensityᵥ_apply hi3 hT, signedIntegralOn]
  obtain ⟨β, f, V, hβ, hf, hV, hcover⟩ := assembly_cutoff_cover h
  have hplateau : ∀ n, A.restrict (V n) = S.restrict (V n) := by
    intro n
    ext T hT
    rw [VectorMeasure.restrict_apply _ (hV n).1.measurableSet hT,
      VectorMeasure.restrict_apply _ (hV n).1.measurableSet hT,
      Measure.toSignedMeasure_apply_measurable (hT.inter (hV n).1.measurableSet),
      measureReal_def, hS _ (hT.inter (hV n).1.measurableSet)]
    exact Γ.leibniz_on_plateau h hu hv (hβ n) huc hvc (hf n).1 hvcc (hf n).2.1
      huae hvae (hf n).2.2.2 (hV n).1 (hV n).2.2 Φ hΦ hw hwae
      (hT.inter (hV n).1.measurableSet) inter_subset_right
  have hAU : A.restrict U = S.restrict U := by
    apply le_antisymm
    · have hr := VectorMeasure.restrict_le_restrict_iUnion A S
        (fun n => (hV n).1.measurableSet) (fun n => (hplateau n).le)
      rwa [hcover] at hr
    · have hr := VectorMeasure.restrict_le_restrict_iUnion S A
        (fun n => (hV n).1.measurableSet) (fun n => (hplateau n).ge)
      rwa [hcover] at hr
  have hcrosscarried := (SignedMeasure.totalVariation_absolutelyContinuous_iff _ _).mp
    (Γ.cross_absolutelyContinuous_left hu.1 hv.1)
  have hzeroA : A.restrict Uᶜ = 0 := by
    ext T hT
    rw [VectorMeasure.restrict_apply _ h.isOpen.measurableSet.compl hT,
      Measure.toSignedMeasure_apply_measurable (hT.inter h.isOpen.measurableSet.compl),
      measureReal_def, measure_mono_null inter_subset_right (Γ.carried w hw),
      ENNReal.toReal_zero, VectorMeasure.zero_apply]
  have hzeroS : S.restrict Uᶜ = 0 := by
    ext T hT
    rw [VectorMeasure.restrict_apply _ h.isOpen.measurableSet.compl hT,
      hS _ (hT.inter h.isOpen.measurableSet.compl)]
    have hu0 := measure_mono_null (inter_subset_right (s := T)) (Γ.carried u hu.1)
    have hv0 := measure_mono_null (inter_subset_right (s := T)) (Γ.carried v hv.1)
    have hp0 := measure_mono_null (inter_subset_right (s := T))
      (hcrosscarried.1 (Γ.carried u hu.1))
    have hn0 := measure_mono_null (inter_subset_right (s := T))
      (hcrosscarried.2 (Γ.carried u hu.1))
    simp only [signedIntegralOn, Measure.restrict_zero_set hu0, Measure.restrict_zero_set hv0,
      Measure.restrict_zero_set hp0, Measure.restrict_zero_set hn0, integral_zero_measure,
      sub_self, mul_zero, add_zero, VectorMeasure.zero_apply]
  have hAS : A = S := by
    calc
      A = A.restrict U + A.restrict Uᶜ :=
        (VectorMeasure.restrict_add_restrict_compl A h.isOpen.measurableSet).symm
      _ = S.restrict U + S.restrict Uᶜ := by rw [hAU, hzeroA, hzeroS]
      _ = S := VectorMeasure.restrict_add_restrict_compl S h.isOpen.measurableSet
  have heq := congrArg (fun s : SignedMeasure X => s B) hAS
  simpa only [A, Measure.toSignedMeasure_apply_measurable hB, measureReal_def, hS B hB] using heq

end DirichletForm.FOTConstruction
