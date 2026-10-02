import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Descent of a whole monotone certificate from a coupling to its actual marginal.
The standard Borel coupling carrier is disintegrated. No regularity or
countable test assumption on the certificate is needed. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- A measurable constant on the target marginal, obtained from the conditional
law of the coupling constant. The extra one handles null exceptional fibers. -/
def physicalBankDescentConstant {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace X] [MeasurableEq X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → X) (K : Ω → ℝ) (Q : ℝ)
    (x : X) : ℝ :=
  (1 + 2 * (∫⁻ ω, ENNReal.ofReal (K ω ^ Q) ∂condDistrib id f μ x).toReal) ^ Q⁻¹

/-- Descend an entire upward closed certificate, rather than separate events for
uncountably many tests. The moment cost is `1+2*C`, on the literal target law. -/
theorem physicalBank_measurable_descent {Ω X : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace X] [MeasurableEq X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X)
    {f : Ω → X} (hf : MeasurePreserving f μ ν)
    {K : Ω → ℝ} (hK : Measurable K) (hKone : ∀ ω, 1 ≤ K ω)
    {Q C : ℝ} (hQ : 0 < Q) (hC : 0 ≤ C)
    (hmoment : (∫⁻ ω, ENNReal.ofReal (K ω ^ Q) ∂μ) ≤ ENNReal.ofReal C)
    (P : X → ℝ → Prop) (hmono : ∀ x k k', k ≤ k' → P x k → P x k')
    (hP : ∀ᵐ ω ∂μ, P (f ω) (K ω)) :
    ∃ Ktarget : X → ℝ, Measurable Ktarget ∧ (∀ x, 1 ≤ Ktarget x) ∧
      (∫⁻ x, ENNReal.ofReal (Ktarget x ^ Q) ∂ν) ≤ ENNReal.ofReal (1 + 2 * C) ∧
      ∀ᵐ x ∂ν, P x (Ktarget x) := by
  haveI : IsProbabilityMeasure ν := by
    rw [← hf.map_eq]
    exact Measure.isProbabilityMeasure_map hf.measurable.aemeasurable
  let κ := condDistrib id f μ
  let A : X → ℝ≥0∞ := fun x => ∫⁻ ω, ENNReal.ofReal (K ω ^ Q) ∂κ x
  have hg : Measurable (fun ω : Ω => ENNReal.ofReal (K ω ^ Q)) :=
    ENNReal.measurable_ofReal.comp (hK.pow measurable_const)
  have hA : Measurable A := hg.lintegral_kernel
  have hprod : ν ⊗ₘ κ = μ.map (fun ω => (f ω, ω)) := by
    rw [← hf.map_eq]
    exact compProd_map_condDistrib measurable_id.aemeasurable
  have hAmoment : (∫⁻ x, A x ∂ν) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ p : X × Ω, ENNReal.ofReal (K p.2 ^ Q) ∂(ν ⊗ₘ κ) :=
        (Measure.lintegral_compProd (μ := ν) (κ := κ) (hg.comp measurable_snd)).symm
      _ = ∫⁻ ω, ENNReal.ofReal (K ω ^ Q) ∂μ := by
        rw [hprod]
        exact lintegral_map (hg.comp measurable_snd) (hf.measurable.prodMk measurable_id)
      _ ≤ ENNReal.ofReal C := hmoment
  have hfinite : ∀ᵐ x ∂ν, A x < ∞ :=
    ae_lt_top hA (ne_of_lt (lt_of_le_of_lt hAmoment ENNReal.ofReal_lt_top))
  let Ktarget : X → ℝ := fun x => (1 + 2 * (A x).toReal) ^ Q⁻¹
  have hm : Measurable Ktarget :=
    (measurable_const.add (measurable_const.mul hA.ennreal_toReal)).pow measurable_const
  have hone : ∀ x, 1 ≤ Ktarget x := by
    intro x
    exact Real.one_le_rpow (le_add_of_nonneg_right (by positivity)) (inv_nonneg.mpr hQ.le)
  have hpower (x : X) : Ktarget x ^ Q = 1 + 2 * (A x).toReal :=
    Real.rpow_inv_rpow (by positivity) hQ.ne'
  have htargetmoment : (∫⁻ x, ENNReal.ofReal (Ktarget x ^ Q) ∂ν) ≤
      ENNReal.ofReal (1 + 2 * C) := by
    calc
      _ ≤ ∫⁻ x, 1 + 2 * A x ∂ν := by
        apply lintegral_mono
        intro x
        change ENNReal.ofReal (Ktarget x ^ Q) ≤ 1 + 2 * A x
        rw [hpower, ENNReal.ofReal_add zero_le_one (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_one,
          show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
        gcongr
        exact ENNReal.ofReal_toReal_le
      _ = 1 + 2 * ∫⁻ x, A x ∂ν := by
        rw [lintegral_add_left measurable_const, lintegral_const_mul _ hA]
        simp
      _ ≤ 1 + 2 * ENNReal.ofReal C := by gcongr
      _ = ENNReal.ofReal (1 + 2 * C) := by
        rw [ENNReal.ofReal_add zero_le_one (by positivity),
          ENNReal.ofReal_mul (by norm_num)]
        norm_num
  have hcomp : κ ∘ₘ ν = μ := by
    rw [← hf.map_eq]
    simpa only [Measure.map_id] using
      (condDistrib_comp_map hf.measurable.aemeasurable measurable_id.aemeasurable)
  have hsource : ∀ᵐ x ∂ν, ∀ᵐ ω ∂κ x, 1 ≤ K ω ∧ P (f ω) (K ω) := by
    apply Measure.ae_ae_of_ae_comp
    rw [hcomp]
    filter_upwards [hP] with ω hω using ⟨hKone ω, hω⟩
  have hgraph : ∀ᵐ x ∂ν, ∀ᵐ ω ∂κ x, f ω = x := by
    apply Measure.ae_ae_of_ae_compProd (p := fun p : X × Ω => f p.2 = p.1)
    rw [hprod]
    apply (ae_map_iff (hf.measurable.prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun (hf.measurable.comp measurable_snd) measurable_fst)).2
    filter_upwards with ω using rfl
  have hgood : ∀ᵐ x ∂ν, ∀ᵐ ω ∂κ x, 1 ≤ K ω ∧ P x (K ω) := by
    filter_upwards [hsource, hgraph] with x hs hgx
    filter_upwards [hs, hgx] with ω hω heq
    simpa only [heq] using hω
  refine ⟨Ktarget, hm, hone, htargetmoment, ?_⟩
  filter_upwards [hfinite, hgood] with x hx hgoodx
  have hex : ∃ ω : Ω, (1 ≤ K ω ∧ P x (K ω)) ∧ K ω ^ Q ≤ 1 + 2 * (A x).toReal := by
    by_contra h
    have hlarge : ∀ᵐ ω ∂κ x, ENNReal.ofReal (1 + 2 * (A x).toReal) ≤
        ENNReal.ofReal (K ω ^ Q) := by
      filter_upwards [hgoodx] with ω hk
      exact ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge (fun hle => h ⟨ω, hk, hle⟩)))
    have hi := lintegral_mono_ae hlarge
    haveI : IsProbabilityMeasure (κ x) := inferInstance
    simp only [lintegral_const, measure_univ, mul_one] at hi
    have hr := (ENNReal.ofReal_le_iff_le_toReal hx.ne).mp hi
    have hn := ENNReal.toReal_nonneg (a := A x)
    linarith
  obtain ⟨ω, hk, hkp⟩ := hex
  apply hmono x (K ω) (Ktarget x) _ hk.2
  apply (Real.le_rpow_inv_iff_of_pos (zero_le_one.trans hk.1) (by positivity) hQ).2
  exact hkp

end SubdiffusiveProcess.Section10
