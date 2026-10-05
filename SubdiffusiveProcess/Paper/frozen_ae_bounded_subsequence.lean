module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section




open Filter MeasureTheory
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A sequence with uniformly bounded first moments has an almost everywhere
subsequence bounded by a finite sample-dependent constant. -/
theorem frozen_ae_bounded_subsequence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ≥0∞)
    (hX : ∀ n, AEMeasurable (X n) μ)
    (hbound : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, ∫⁻ ω, X n ω ∂μ ≤ C) :
    ∀ᵐ ω ∂μ, ∃ B : ℝ≥0∞, B < ⊤ ∧ ∃ ns : ℕ → ℕ,
      StrictMono ns ∧ ∀ n, X (ns n) ω ≤ B := by
  obtain ⟨C, hC, hXC⟩ := hbound
  have hfatou : ∫⁻ ω, liminf (fun n => X n ω) atTop ∂μ ≤ C :=
    (lintegral_liminf_le' hX).trans
      ((liminf_le_of_frequently_le' (Frequently.of_forall hXC)))
  have hlt : ∀ᵐ ω ∂μ, liminf (fun n => X n ω) atTop < ⊤ := by
    have hmeas : AEMeasurable (fun ω => liminf (fun n => X n ω) atTop) μ := by
      simp only [liminf_eq_iSup_iInf_of_nat]
      exact AEMeasurable.iSup fun n => AEMeasurable.biInf _ (Set.to_countable _) fun i _ => hX i
    exact ae_lt_top' hmeas (lt_of_le_of_lt hfatou hC).ne
  filter_upwards [hlt] with ω hω
  have hB : liminf (fun n => X n ω) atTop + 1 < ⊤ := by
    exact ENNReal.add_lt_top.mpr ⟨hω, ENNReal.one_lt_top⟩
  have hfreq : ∃ᶠ n in atTop, X n ω < liminf (fun n => X n ω) atTop + 1 :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) (ENNReal.lt_add_right hω.ne one_ne_zero)
  obtain ⟨ns, hns, hns'⟩ := extraction_of_frequently_atTop hfreq
  exact ⟨_, hB, ns, hns, fun n => (hns' n).le⟩

end SubdiffusiveProcess.Paper
end
