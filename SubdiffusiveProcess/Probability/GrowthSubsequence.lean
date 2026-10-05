module

public import SubdiffusiveProcess.Probability.LiminfGrowth
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

/-! Bounded pathwise extraction of cutoff growth constants. A bound on their
moments does not bound their supremum along the original sequence. -/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess

/-- Uniform moments give a measurable bound for a samplewise subsequence.
The bound loses only the prescribed positive epsilon. No measurability of the
subsequence is asserted or used. -/
theorem exists_bounded_subsequence_of_eLpNorm_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (p C eps : ℝ≥0) (hp : 1 ≤ p) (heps : 0 < eps)
    (hf : ∀ n, Measurable (f n)) (hb : ∀ n, eLpNorm (f n) p P ≤ C) :
    ∃ K : Ω → ℝ, Measurable K ∧ (∀ om, 0 < K om) ∧
      eLpNorm K p P ≤ (C + eps : ℝ≥0) ∧
      ∀ᵐ om ∂P, ∃ seq : ℕ → ℕ, StrictMono seq ∧ ∀ n, ‖f (seq n) om‖ < K om := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hepsR : 0 < (eps : ℝ) := by exact_mod_cast heps
  let k : Ω → ℝ≥0∞ := fun om => liminf (fun n => ‖f n om‖ₑ) atTop
  obtain ⟨hk, hnorm, hfin⟩ := eLpNorm_liminf_enorm_toReal_le P f p C hp0 hf hb
  let K : Ω → ℝ := fun om => (k om).toReal + eps
  have hK : Measurable K := hk.add_const _
  have hKpos : ∀ om, 0 < K om := fun om =>
    add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hepsR
  refine ⟨K, hK, hKpos, ?_, ?_⟩
  · have hepsnorm : eLpNorm (fun _ : Ω => (eps : ℝ)) p P = eps := by
      rw [eLpNorm_const' (eps : ℝ) (by exact_mod_cast hp0) ENNReal.coe_ne_top,
        measure_univ, ENNReal.one_rpow, mul_one]
      change (↑‖(eps : ℝ)‖₊ : ℝ≥0∞) = (eps : ℝ≥0∞)
      exact congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞)) (Real.nnnorm_of_nonneg eps.property)
    have htri := eLpNorm_add_le (μ := P) (p := (p : ℝ≥0∞))
      (f := fun om => (k om).toReal) (g := fun _ : Ω => (eps : ℝ)) (by exact_mod_cast hp)
    change eLpNorm ((fun om => (k om).toReal) + fun _ : Ω => (eps : ℝ)) p P ≤ _
    refine htri.trans ?_
    rw [hepsnorm, ENNReal.coe_add]
    exact add_le_add hnorm le_rfl
  · filter_upwards [hfin] with om hom
    have hlt : k om < ENNReal.ofReal (K om) := by
      have hom' : k om ≠ ⊤ := hom.ne
      rw [← ENNReal.ofReal_toReal hom']
      apply (ENNReal.ofReal_lt_ofReal_iff (hKpos om)).mpr
      exact lt_add_of_pos_right _ hepsR
    have hfreq : ∃ᶠ n in atTop, ‖f n om‖ₑ < ENNReal.ofReal (K om) :=
      frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
    obtain ⟨seq, hseq, hbound⟩ := extraction_of_frequently_atTop hfreq
    refine ⟨seq, hseq, fun n => ?_⟩
    have hn := hbound n
    rw [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff (hKpos om)] at hn
    exact hn

end SubdiffusiveProcess

