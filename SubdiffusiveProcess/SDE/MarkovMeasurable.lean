module

public import SubdiffusiveProcess.SDE.Markov
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumSmoothRange
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The Markov identity for bounded measurable functions

The Markov identity `setIntegral_comp_add_eq_setIntegral_kernel` for smooth compactly supported
`h` extends to continuous compactly supported `h` by uniform approximation
(`exists_contDiff_compactSupport_norm_sub_lt`), hence identifies the finite measures
`B ↦ P(A ∩ {X_{s+q} ∈ B})` and `B ↦ ∫_A Q_q(X_s, B) dP` (Riesz–Markov–Kakutani uniqueness), and so
holds for every bounded measurable `h`.
-/

@[expose] public section

noncomputable section

namespace SubdiffusiveProcess.SDE

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped NNReal ENNReal Topology ContDiff CompactlySupported ZeroAtInfty

variable {d : ℕ}

universe u

/-- **The Markov identity for bounded measurable functions.** -/
theorem setIntegral_comp_add_eq_setIntegral_kernel_of_measurable (hIto : ItoFormulaStopped.{u} d)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P ℱ] {σ : ℝ} {b : Vec d → Vec d}
    (hb : Continuous b) {W X : ℝ≥0 → Ω → Vec d} (hW : IsBrownianMotion W ℱ P)
    (hX : IsStrongSolution σ b W X ℱ) {Q : MarkovProcess.SubMarkovKernelSemigroup (Vec d)}
    (hQ : HasClassicalResolvent Q σ b)
    (hQc : ∀ h : Vec d → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ y,
      Continuous fun t : ℝ≥0 => ∫ z, h z ∂(Q t y))
    (s q : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    (P.restrict A).map (X (s + q)) = Q q ∘ₘ ((P.restrict A).map (X s)) := by
  have hXm : ∀ t, Measurable (X t) := fun t => (hX.adapted t).mono (ℱ.le t) le_rfl
  have : ∀ t, IsFiniteKernel (Q t) := fun t =>
    ⟨⟨1, ENNReal.one_lt_top, fun y => Q.measure_univ_le_one t y⟩⟩
  set ν : Measure (Vec d) := (P.restrict A).map (X s) with hν
  have hν_fin : IsFiniteMeasure ν := by rw [hν]; infer_instance
  -- Integrals against the two measures.
  have hint1 : ∀ f : Vec d → ℝ, Continuous f → (∃ C, ∀ z, |f z| ≤ C) →
      ∫ z, f z ∂((P.restrict A).map (X (s + q))) = ∫ w in A, f (X (s + q) w) ∂P :=
    fun f hf _ => integral_map (hXm _).aemeasurable hf.aestronglyMeasurable
  have hint2 : ∀ f : Vec d → ℝ, Continuous f → (∃ C, ∀ z, |f z| ≤ C) →
      ∫ z, f z ∂(Q q ∘ₘ ν) = ∫ w in A, (∫ z, f z ∂(Q q (X s w))) ∂P := by
    intro f hf ⟨C, hC⟩
    have hfi : Integrable (fun p : Vec d × Vec d => f p.2) (ν ⊗ₘ Q q) :=
      Integrable.of_bound (hf.comp continuous_snd).aestronglyMeasurable C
        (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC _)
    rw [← Measure.snd_compProd, Measure.snd, integral_map measurable_snd.aemeasurable
      hf.aestronglyMeasurable, Measure.integral_compProd hfi, hν,
      integral_map (hXm s).aemeasurable]
    exact (StronglyMeasurable.integral_kernel (κ := Q q)
      hf.stronglyMeasurable).aestronglyMeasurable
  -- Agreement on smooth compactly supported functions.
  have hsmooth : ∀ g : Vec d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ w in A, g (X (s + q) w) ∂P = ∫ w in A, (∫ z, g z ∂(Q q (X s w))) ∂P :=
    fun g hg hgc => setIntegral_comp_add_eq_setIntegral_kernel hIto hb hW hX hQ hQc hg hgc s q hA
  -- The bound on the difference of two integrals against `P.restrict A`.
  have hAle : (P.restrict A).real univ ≤ 1 := by
    rw [Measure.real, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have hQle : ∀ y, (Q q y).real univ ≤ 1 := fun y =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact Q.measure_univ_le_one q y)
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  have hfc : Continuous f := f.continuous
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hfb : ∃ C, ∀ z, |f z| ≤ C := ⟨C, fun z => by rw [← Real.norm_eq_abs]; exact hC z⟩
  rw [hint1 f hfc hfb, hint2 f hfc hfb]
  -- Approximate `f` uniformly by smooth compactly supported functions.
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨g, hgs, hg⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.exists_contDiff_compactSupport_norm_sub_lt
      (SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.compactSupportToC0 f)
      (eps := ε / 2) (by positivity)
  have hfg : ∀ z, |g z - f z| ≤ ε / 2 := by
    intro z
    set F := SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.compactSupportToC0 g -
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.compactSupportToC0 f with hF
    have h1 := BoundedContinuousFunction.norm_coe_le_norm F.toBCF z
    rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] at h1
    have h2 : F.toBCF z = g z - f z := rfl
    rw [h2, Real.norm_eq_abs] at h1
    linarith
  have hgc : Continuous g := g.continuous
  obtain ⟨Cg, hCg⟩ := g.continuous.bounded_above_of_compact_support g.hasCompactSupport
  have e := hsmooth g hgs g.hasCompactSupport
  obtain ⟨Cf, hCf⟩ := hfb
  have hCg' : ∀ z, |g z| ≤ Cg := fun z => by rw [← Real.norm_eq_abs]; exact hCg z
  have hint_path : ∀ φ : Vec d → ℝ, Continuous φ → ∀ C, (∀ z, |φ z| ≤ C) →
      Integrable (fun w => φ (X (s + q) w)) (P.restrict A) := fun φ hφ C hφC =>
    Integrable.of_bound (hφ.measurable.comp (hXm _)).aestronglyMeasurable C
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hφC _)
  have hker_bound : ∀ φ : Vec d → ℝ, ∀ C, 0 ≤ C → (∀ z, |φ z| ≤ C) → ∀ y,
      |∫ z, φ z ∂(Q q y)| ≤ C := by
    intro φ C hC0 hφC y
    have h1 := norm_integral_le_of_norm_le_const (μ := Q q y) (f := φ) (C := C)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hφC z)
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (mul_le_of_le_one_right hC0 (hQle y))
  have hint_ker : ∀ φ : Vec d → ℝ, Continuous φ → ∀ C, 0 ≤ C → (∀ z, |φ z| ≤ C) →
      Integrable (fun w => ∫ z, φ z ∂(Q q (X s w))) (P.restrict A) := fun φ hφ C hC0 hφC =>
    Integrable.of_bound (((StronglyMeasurable.integral_kernel (κ := Q q)
      hφ.stronglyMeasurable).measurable.comp (hXm s)).aestronglyMeasurable) C
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hker_bound φ C hC0 hφC _)
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf 0)
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0)
  have hε2 : (0 : ℝ) ≤ ε / 2 := by positivity
  have d1 : |∫ w in A, f (X (s + q) w) ∂P - ∫ w in A, g (X (s + q) w) ∂P| ≤ ε / 2 := by
    rw [← integral_sub (hint_path f hfc Cf hCf) (hint_path g hgc Cg hCg')]
    have h1 := norm_integral_le_of_norm_le_const (μ := P.restrict A) (C := ε / 2)
      (f := fun w => f (X (s + q) w) - g (X (s + q) w))
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_sub_comm]; exact hfg _)
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (mul_le_of_le_one_right hε2 hAle)
  have d2 : |∫ w in A, (∫ z, g z ∂(Q q (X s w))) ∂P -
      ∫ w in A, (∫ z, f z ∂(Q q (X s w))) ∂P| ≤ ε / 2 := by
    rw [← integral_sub (hint_ker g hgc Cg hCg0 hCg') (hint_ker f hfc Cf hCf0 hCf)]
    have hpt : ∀ y, |∫ z, g z ∂(Q q y) - ∫ z, f z ∂(Q q y)| ≤ ε / 2 := by
      intro y
      have hgi : Integrable (fun z => g z) (Q q y) := Integrable.of_bound
        hgc.aestronglyMeasurable Cg (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact hCg' z)
      have hfi : Integrable (fun z => f z) (Q q y) := Integrable.of_bound
        hfc.aestronglyMeasurable Cf (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact hCf z)
      rw [← integral_sub hgi hfi]
      exact hker_bound (fun z => g z - f z) (ε / 2) hε2 hfg y
    have h1 := norm_integral_le_of_norm_le_const (μ := P.restrict A) (C := ε / 2)
      (f := fun w => ∫ z, g z ∂(Q q (X s w)) - ∫ z, f z ∂(Q q (X s w)))
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hpt _)
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (mul_le_of_le_one_right hε2 hAle)
  rw [Real.dist_eq]
  calc |∫ w in A, f (X (s + q) w) ∂P - ∫ w in A, (∫ z, f z ∂(Q q (X s w))) ∂P|
      = |(∫ w in A, f (X (s + q) w) ∂P - ∫ w in A, g (X (s + q) w) ∂P) +
          (∫ w in A, (∫ z, g z ∂(Q q (X s w))) ∂P -
            ∫ w in A, (∫ z, f z ∂(Q q (X s w))) ∂P)| := by rw [e]; congr 1; ring
    _ ≤ ε / 2 + ε / 2 := (abs_add_le _ _).trans (add_le_add d1 d2)
    _ = ε := by ring

end SubdiffusiveProcess.SDE
