module

public import SubdiffusiveProcess.Analysis.RawLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Order.Group.Lattice

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Cutoffs

/-- Combine a pathwise envelope with a nonnegative moment envelope. -/
def minimumEnvelope (a b : ℝ) : ℝ := min (max a 0) b

theorem minimumEnvelope_nonneg (a b : ℝ) (hb : 0 ≤ b) :
    0 ≤ minimumEnvelope a b := le_min (le_max_right _ _) hb

theorem minimumEnvelope_le_left (a b : ℝ) :
    minimumEnvelope a b ≤ max a 0 := min_le_left _ _

theorem minimumEnvelope_le_right (a b : ℝ) :
    minimumEnvelope a b ≤ b := min_le_right _ _

theorem le_minimumEnvelope {a b c : ℝ} (ha : c ≤ a) (hb : c ≤ b) :
    c ≤ minimumEnvelope a b := le_min (ha.trans (le_max_left _ _)) hb

theorem measurable_minimumEnvelope {Ω : Type*} [MeasurableSpace Ω]
    {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => minimumEnvelope (a ω) (b ω)) :=
  (ha.max measurable_const).min hb

theorem norm_minimumEnvelope_le (a b : ℝ) (hb : 0 ≤ b) :
    ‖minimumEnvelope a b‖ ≤ ‖b‖ := by
  rw [Real.norm_of_nonneg (minimumEnvelope_nonneg a b hb), Real.norm_of_nonneg hb]
  exact minimumEnvelope_le_right a b

theorem memLp_minimumEnvelope {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : ℝ≥0∞} {a b : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hb0 : ∀ ω, 0 ≤ b ω)
    (hmb : MemLp b p μ) :
    MemLp (fun ω => minimumEnvelope (a ω) (b ω)) p μ :=
  hmb.of_le (measurable_minimumEnvelope ha hb).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => norm_minimumEnvelope_le _ _ (hb0 ω))

theorem eLpNorm_minimumEnvelope_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : ℝ≥0∞} {a b : Ω → ℝ} (hb0 : ∀ ω, 0 ≤ b ω) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun ω => minimumEnvelope (a ω) (b ω)) p μ ≤ SubdiffusiveProcess.RawLp.eLpNorm b p μ :=
  SubdiffusiveProcess.RawLp.eLpNorm_mono_ae
    (Filter.Eventually.of_forall fun ω => norm_minimumEnvelope_le _ _ (hb0 ω))

theorem bddAbove_range_minimumEnvelope (a b : ℕ → ℝ)
    (ha : BddAbove (range a)) :
    BddAbove (range (fun n => minimumEnvelope (a n) (b n))) := by
  obtain ⟨B, hB⟩ := ha
  refine ⟨max B 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (minimumEnvelope_le_left _ _).trans (max_le_max (hB ⟨n, rfl⟩) le_rfl)

end SubdiffusiveProcess.Cutoffs
