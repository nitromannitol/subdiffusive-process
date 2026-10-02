import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.Conservativity
import MarkovProcess.Semigroup.Generator
import MarkovProcess.Semigroup.Resolvent
import MarkovProcess.Feller.Semigroup

/-!
# Conservativity from approximations to the constant function

A criterion on generator-domain functions that does not assume a path law.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Filter MeasureTheory MarkovProcess MarkovProcess.Semigroup
open scoped Topology ZeroAtInfty

theorem norm_semigroup_sub_le_generator {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (f : S.generatorDomain) (t : NNReal) :
    ‖S t f - f‖ ≤ (t : ℝ) * ‖S.generator f‖ := by
  rw [S.operator_sub_eq_integral f t]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => S (Real.toNNReal s) (S.generator f)) (C := ‖S.generator f‖)
    (a := (0:ℝ)) (b := (t:ℝ))
    (fun s _ => S.norm_apply_le (Real.toNNReal s) (S.generator f))
  simpa only [sub_zero, abs_of_nonneg t.coe_nonneg, mul_comm] using h


/-- A sequence approaching one with generators tending uniformly to zero
forces every transition measure to have total mass one. -/
theorem isConservative_of_generator_approximation
    {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
    {P : SubMarkovKernelSemigroup alpha} (hF : P.IsFellerKernelSemigroup)
    (f : ℕ → hF.c0Semigroup.generatorDomain)
    (hbound : ∀ n x, (f n : C₀(alpha, ℝ)) x ≤ 1)
    (hpoint : ∀ x, Tendsto (fun n ↦ (f n : C₀(alpha, ℝ)) x) atTop (nhds 1))
    (hgen : Tendsto (fun n ↦ ‖hF.c0Semigroup.generator (f n)‖) atTop (nhds 0)) :
    P.IsConservative := by
  apply Section7Process.isConservative_of_tendsto_integral_c0
    (fun n ↦ (f n : C₀(alpha, ℝ))) hbound
  intro t x
  have herr : Tendsto
      (fun n ↦ hF.c0Semigroup t (f n) x - (f n : C₀(alpha, ℝ)) x)
      atTop (nhds 0) := by
    refine squeeze_zero_norm (a := fun n ↦ (t : ℝ) * ‖hF.c0Semigroup.generator (f n)‖)
      (fun n ↦ ?_) ?_
    · exact ((hF.c0Semigroup t (f n) - (f n : C₀(alpha, ℝ))).toBCF.norm_coe_le_norm x).trans
        (norm_semigroup_sub_le_generator hF.c0Semigroup (f n) t)
    · simpa using hgen.const_mul (t : ℝ)
  have hsum := herr.add (hpoint x)
  simpa only [sub_add_cancel, zero_add] using hsum

theorem generator_eq_of_resolvent_witness {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (mu : MarkovProcess.Semigroup.PositiveShift) (w f : E)
    (hres : S.resolvent mu f = w) :
    ∃ hw : w ∈ S.generatorDomain, S.generator ⟨w, hw⟩ = (mu : ℝ) • w - f := by
  subst hres
  exact ⟨S.resolvent_mem_generatorDomain mu f,
    S.generator_eq_of_resolvent_eq mu (S.resolvent_mem_generatorDomain mu f) rfl⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
