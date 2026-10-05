module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.InteriorWeakLogEnergy
public import Homogenization.Sobolev.MatchedPair.ScaledPoincare

@[expose] public section

/-!
# Controlling a mean from a set of positive relative measure

If a function is bounded on at least half the domain, its centered square
integral controls the full square integral. This is the anchoring step in
the logarithmic oscillation argument.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A bound on half the measure anchors the otherwise undetermined mean. -/
theorem harmonic_integral_sq_le_centered_of_half_measure
    {X : Type*} [MeasurableSpace X] {mu : Measure X} [IsFiniteMeasure mu]
    {E : Set X} {f : X → ℝ} (hf : MemLp f 2 mu)
    {m B : ℝ} (hhalf : (mu Set.univ).toReal / 2 ≤ (mu E).toReal)
    (hgood : ∀ᵐ x ∂mu.restrict E, |f x| ≤ B) :
    (∫ x, f x ^ 2 ∂mu) ≤
      10 * (∫ x, (f x - m) ^ 2 ∂mu) + 8 * B ^ 2 * (mu Set.univ).toReal := by
  have hcenter : MemLp (fun x => f x - m) 2 mu := hf.sub (memLp_const m)
  have hcenterE : IntegrableOn (fun x => (f x - m) ^ 2) E mu := hcenter.integrable_sq.restrict
  have hEint : (mu E).toReal * m ^ 2 ≤
      2 * (∫ x in E, (f x - m) ^ 2 ∂mu) + 2 * B ^ 2 * (mu E).toReal := by
    have hpoint : ∀ᵐ x ∂mu.restrict E, m ^ 2 ≤ 2 * (f x - m) ^ 2 + 2 * B ^ 2 := by
      filter_upwards [hgood] with x hx
      have hfsq : f x ^ 2 ≤ B ^ 2 := by
        nlinarith [sq_nonneg (B - |f x|), sq_abs (f x), abs_nonneg (f x)]
      nlinarith [sq_nonneg (2 * f x - m)]
    have hi := integral_mono_ae (integrable_const (m ^ 2))
      ((hcenterE.const_mul 2).add (integrable_const (2 * B ^ 2))) hpoint
    simp only [Pi.add_apply] at hi
    rw [integral_add (hcenterE.const_mul 2) (integrable_const (2 * B ^ 2)),
      integral_const_mul] at hi
    simp only [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul] at hi
    convert hi using 1
    ring
  have hEfull : (∫ x in E, (f x - m) ^ 2 ∂mu) ≤ ∫ x, (f x - m) ^ 2 ∂mu :=
    setIntegral_le_integral hcenter.integrable_sq (Eventually.of_forall fun x => sq_nonneg _)
  have hmass : (mu E).toReal ≤ (mu Set.univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top mu Set.univ) (measure_mono (subset_univ E))
  have hmean : (mu Set.univ).toReal * m ^ 2 ≤
      4 * (∫ x, (f x - m) ^ 2 ∂mu) + 4 * B ^ 2 * (mu Set.univ).toReal := by
    have hlow := mul_le_mul_of_nonneg_right hhalf (sq_nonneg m)
    have hB := mul_le_mul_of_nonneg_left hmass (sq_nonneg B)
    linarith
  have hi := integral_mono_ae hf.integrable_sq
    ((hcenter.integrable_sq.const_mul 2).add (integrable_const (2 * m ^ 2)))
    (Eventually.of_forall fun x => show f x ^ 2 ≤ 2 * (f x - m) ^ 2 + 2 * m ^ 2 by
      nlinarith [sq_nonneg (f x - 2 * m)])
  simp only [Pi.add_apply] at hi
  rw [integral_add (hcenter.integrable_sq.const_mul 2) (integrable_const (2 * m ^ 2)),
    integral_const_mul, integral_const, smul_eq_mul] at hi
  simp only [Measure.real] at hi
  nlinarith only [hi, hmean]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
