module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicHalfMeasureLower
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

/-! # The half-measure alternative and normalized oscillation reduction -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- An almost-everywhere measurable real function or its complement has
a half-measure set above `1/2`. The selected set is genuinely measurable. -/
theorem harmonic_half_measure_alternative {X : Type*} [MeasurableSpace X]
    {mu : Measure X} [IsFiniteMeasure mu] {h : X → ℝ}
    (hh : AEStronglyMeasurable h mu) :
    (∃ E : Set X, MeasurableSet E ∧ (mu Set.univ).toReal / 2 ≤ (mu E).toReal ∧
      ∀ᵐ x ∂mu.restrict E, 1 / 2 ≤ h x) ∨
    (∃ E : Set X, MeasurableSet E ∧ (mu Set.univ).toReal / 2 ≤ (mu E).toReal ∧
      ∀ᵐ x ∂mu.restrict E, 1 / 2 ≤ 1 - h x) := by
  let E : Set X := {x | (1 / 2 : ℝ) ≤ hh.mk h x}
  have hE : MeasurableSet E := measurableSet_le measurable_const hh.stronglyMeasurable_mk.measurable
  by_cases hhalf : (mu Set.univ).toReal / 2 ≤ (mu E).toReal
  · left
    refine ⟨E, hE, hhalf, ?_⟩
    filter_upwards [ae_restrict_mem hE, hh.ae_eq_mk.filter_mono (ae_mono Measure.restrict_le_self)] with x hx heq
    rw [heq]
    exact hx
  · right
    refine ⟨Eᶜ, hE.compl, ?_, ?_⟩
    · have hadd := measureReal_add_measureReal_compl (μ := mu) hE
      simp only [Measure.real] at hadd
      linarith
    · filter_upwards [ae_restrict_mem hE.compl,
        hh.ae_eq_mk.filter_mono (ae_mono (Measure.restrict_le_self (s := Eᶜ)))] with x hx heq
      rw [heq]
      have : hh.mk h x < 1 / 2 := lt_of_not_ge hx
      linarith

/-- Values in `[0,1]` lose a fixed dimensional interval on the eighth
cube, on one side or the other. -/
theorem exists_harmonic_unit_interval_reduction {d : ℕ} (hd : 2 ≤ d) :
    ∃ k : ℝ, 0 < k ∧ k ≤ 1 / 8 ∧
      ∀ (a : Vec d → ℝ) (z : Vec d),
      (∀ x ∈ centeredAxisCube z 1, 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z 1)) →
      ∀ h : Vec d → ℝ, WeakHarmonic a (centeredAxisCube z 1) h →
      (∀ x ∈ centeredAxisCube z 1, 0 ≤ h x ∧ h x ≤ 1) →
      (∀ x ∈ centeredAxisCube z (1 / 8), k ≤ h x) ∨
      (∀ x ∈ centeredAxisCube z (1 / 8), h x ≤ 1 - k) := by
  obtain ⟨delta, hdelta, hdelta1, hlower⟩ := exists_harmonic_unit_half_measure_lower hd
  refine ⟨delta / 2, by positivity, by linarith, ?_⟩
  intro a z hab ha h hh hh01
  let Q := centeredAxisCube z (1 / 2)
  have hQsub : Q ⊆ centeredAxisCube z 1 := centeredAxisCube_mono (by norm_num)
  let : IsFiniteMeasure (volume.restrict Q) :=
    (isOpenBoundedConvexDomain_axisCube (fun i => z i - (1 / 2) / 2) (1 / 2)).isFiniteMeasure_restrict_volume
  have hmeas : AEStronglyMeasurable h (volume.restrict Q) :=
    (hh.1.mono hQsub).aestronglyMeasurable (isOpen_axisCube _ _).measurableSet
  rcases harmonic_half_measure_alternative hmeas with ⟨E, _, hhalf, hgood⟩ | ⟨E, _, hhalf, hgood⟩
  · left
    exact hlower a z hab ha h hh hh01 E
      (by simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using hhalf) hgood
  · right
    have hc : WeakHarmonic a (centeredAxisCube z 1) (fun x => 1 - h x) := by
      convert harmonic_weakHarmonic_affine_value hh (-1) 1 using 1
      ext x
      ring
    have hc01 : ∀ x ∈ centeredAxisCube z 1, 0 ≤ 1 - h x ∧ 1 - h x ≤ 1 := by
      intro x hx
      constructor <;> linarith [(hh01 x hx).1, (hh01 x hx).2]
    have hcLower := hlower a z hab ha (fun x => 1 - h x) hc hc01 E
      (by simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using hhalf) hgood
    intro x hx
    linarith [hcLower x hx]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
