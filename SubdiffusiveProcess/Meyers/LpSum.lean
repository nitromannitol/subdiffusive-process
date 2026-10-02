import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Subadditivity of the `L^p` norm in the measure, and for a finite cover. -/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Meyers

theorem eLpNorm_add_measure_le' {α : Type*} [MeasurableSpace α] (f : α → ℝ) {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (μ ν : Measure α) :
    eLpNorm f p (μ + ν) ≤ eLpNorm f p μ + eLpNorm f p ν := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp1).ne'
  have hpr : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp1
    simpa using this
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpt, eLpNorm_eq_lintegral_rpow_enorm hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm hp0 hpt, lintegral_add_measure]
  exact ENNReal.rpow_add_le_add_rpow _ _ (by positivity) (by
    rw [div_le_one (by linarith)]; simpa using hpr)

theorem eLpNorm_finset_sum_measure_le {α ι : Type*} [MeasurableSpace α] (f : α → ℝ) {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (ν : ι → Measure α) (t : Finset ι) :
    eLpNorm f p (∑ i ∈ t, ν i) ≤ ∑ i ∈ t, eLpNorm f p (ν i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (eLpNorm_add_measure_le' f hp1 hpt _ _).trans (by gcongr)

theorem eLpNorm_restrict_iUnion_le {α ι : Type*} [MeasurableSpace α] [Fintype ι] (f : α → ℝ)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) (μ : Measure α) (s : ι → Set α) :
    eLpNorm f p (μ.restrict (⋃ i, s i)) ≤ ∑ i, eLpNorm f p (μ.restrict (s i)) := by
  have h1 : μ.restrict (⋃ i, s i) ≤ ∑ i, μ.restrict (s i) := by
    have := Measure.restrict_iUnion_le (μ := μ) (s := s)
    simpa [Measure.sum_fintype] using this
  exact (eLpNorm_mono_measure f h1).trans (by simpa using eLpNorm_finset_sum_measure_le f hp1 hpt (fun i => μ.restrict (s i)) Finset.univ)

end SubdiffusiveProcess.Meyers
