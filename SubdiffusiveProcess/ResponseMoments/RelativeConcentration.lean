module

public import SubdiffusiveProcess.ResponseMoments.HyperoctahedralMean
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Relative concentration: the mean-zero clause

Proposition `mfd:prop-conc`.

`eLpNorm_eq_zero_of_le_disorder_mul` is the collapse lemma: a bound
`‖f‖_p ≤ C · disorder · gap` that holds for **every** `disorder ∈ (0,1]`,
with `C` and `f` fixed independently of `disorder`, forces `‖f‖_p = 0`.
In the statement of `relative_concentration`
the admissibility hypotheses on `A_E`, `A_F` never mention `disorder`, so the
statement collapses to `B_k = 0`, i.e. to `A_F = c_k A_E`.

The remaining results here are the two clauses of `mfd:prop-conc` that are
genuinely available from disorder-free hypotheses: `c_k ∈ [m, M]` and the
vanishing of the trace of `B_k` in mean.
-/

open MeasureTheory Filter Matrix Topology
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess
namespace ResponseMoments

/-- A bound proportional to a disorder parameter that ranges over all of
`(0, 1]`, with everything else fixed, forces the quantity to vanish. -/
theorem eLpNorm_eq_zero_of_le_disorder_mul {Om : Type} [MeasurableSpace Om]
    (P : Measure Om) (f : Om → ℝ) (p : ℝ≥0∞) (Cp gap : ℝ)
    (h : ∀ disorder : ℝ, 0 < disorder → disorder ≤ 1 →
      eLpNorm f p P ≤ ENNReal.ofReal (Cp * disorder * gap)) :
    eLpNorm f p P = 0 := by
  have hkey : ∀ n : ℕ, eLpNorm f p P ≤
      ENNReal.ofReal (Cp * (1 / ((n : ℝ) + 1)) * gap) := by
    intro n
    refine h _ (by positivity) ?_
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hreal : Tendsto (fun n : ℕ => Cp * (1 / ((n : ℝ) + 1)) * gap) atTop (𝓝 0) := by
    have := (hone.const_mul Cp).mul_const gap
    simpa using this
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Cp * (1 / ((n : ℝ) + 1)) * gap))
      atTop (𝓝 0) := by
    have hc := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using hc
  exact le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hkey)) bot_le

variable {Om : Type} [MeasurableSpace Om]

/-- `c_k ∈ [m, M]` and the trace of `B_k` has mean zero.  These are the two clauses of `mfd:prop-conc` that follow from
hypotheses not involving the disorder. -/
theorem relative_concentration_mean_zero (d : ℕ) (_hd : 1 ≤ d)
    (P : Measure Om) [IsProbabilityMeasure P]
    (AE AF : Om → Matrix (Fin d) (Fin d) ℝ) (m M : ℝ)
    (htr : ∀ ω, 0 < Matrix.trace (AE ω))
    (hord : ∀ (ω : Om) (x : Fin d → ℝ),
      m * (x ⬝ᵥ (AE ω).mulVec x) ≤ x ⬝ᵥ (AF ω).mulVec x ∧
        x ⬝ᵥ (AF ω).mulVec x ≤ M * (x ⬝ᵥ (AE ω).mulVec x))
    (hint : Integrable (fun ω => Matrix.trace (AF ω) / Matrix.trace (AE ω)) P) :
    m ≤ ∫ ω, Matrix.trace (AF ω) / Matrix.trace (AE ω) ∂P ∧
      (∫ ω, Matrix.trace (AF ω) / Matrix.trace (AE ω) ∂P) ≤ M ∧
      (∀ ω, Matrix.trace ((Matrix.trace (AE ω))⁻¹ •
          (AF ω - (∫ ω', Matrix.trace (AF ω') / Matrix.trace (AE ω') ∂P) • AE ω)) =
        Matrix.trace (AF ω) / Matrix.trace (AE ω) -
          ∫ ω', Matrix.trace (AF ω') / Matrix.trace (AE ω') ∂P) ∧
      (∫ ω, Matrix.trace ((Matrix.trace (AE ω))⁻¹ •
          (AF ω - (∫ ω', Matrix.trace (AF ω') / Matrix.trace (AE ω') ∂P) • AE ω)) ∂P = 0) := by
  set ck : ℝ := ∫ ω, Matrix.trace (AF ω) / Matrix.trace (AE ω) ∂P with hck
  have hptwise : ∀ ω, m ≤ Matrix.trace (AF ω) / Matrix.trace (AE ω) ∧
      Matrix.trace (AF ω) / Matrix.trace (AE ω) ≤ M := by
    intro ω
    exact trace_ratio_mem_Icc_of_form_order (AE ω) (AF ω) m M (htr ω) (hord ω)
  have hlow : m ≤ ck := by
    have h := integral_mono (integrable_const m) hint (fun ω => (hptwise ω).1)
    simpa using h
  have hup : ck ≤ M := by
    have h := integral_mono hint (integrable_const M) (fun ω => (hptwise ω).2)
    simpa using h
  have htrace : ∀ ω, Matrix.trace ((Matrix.trace (AE ω))⁻¹ • (AF ω - ck • AE ω)) =
      Matrix.trace (AF ω) / Matrix.trace (AE ω) - ck := by
    intro ω
    rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul]
    have hne : Matrix.trace (AE ω) ≠ 0 := ne_of_gt (htr ω)
    simp only [smul_eq_mul]
    field_simp
  have hzero : (∫ ω, Matrix.trace ((Matrix.trace (AE ω))⁻¹ • (AF ω - ck • AE ω)) ∂P) = 0 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall htrace)]
    rw [integral_sub hint (integrable_const ck)]
    simp [← hck]
  exact ⟨hlow, hup, htrace, hzero⟩

/-- The mean matrix vanishes, : hyperoctahedral
invariance makes it scalar and its trace is zero. -/
theorem relative_concentration_mean_matrix_eq_zero (d : ℕ) (hd : 0 < d)
    (EB : Matrix (Fin d) (Fin d) ℝ)
    (hrefl : ∀ (i j k : Fin d),
      EB j k = (if j = i then -(1 : ℝ) else 1) * (if k = i then -(1 : ℝ) else 1) * EB j k)
    (hperm : ∀ (σ : Equiv.Perm (Fin d)) (j k : Fin d), EB (σ j) (σ k) = EB j k)
    (htr : Matrix.trace EB = 0) : EB = 0 := by
  obtain ⟨c, hc⟩ := eq_smul_one_of_hyperoctahedral_invariant d hd EB hrefl hperm
  exact eq_zero_of_smul_one_of_trace_eq_zero d hd EB c hc htr

end ResponseMoments
end SubdiffusiveProcess
