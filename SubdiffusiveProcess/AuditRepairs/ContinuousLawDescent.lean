module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

@[expose] public section

/-! Arbitrary almost-everywhere predicates descend along continuous maps of regular
probability spaces. No measurability of the target predicate is assumed. -/

open MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.AuditRepairs

/-- Compact subsets of the full good event have compact measurable images. This retains
original-space null-set identification even before the constructed inverse is measurable. -/
theorem ae_of_ae_comp_continuous
    {Ω X : Type*} [TopologicalSpace Ω] [T2Space Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (Ph : Measure Ω) [IsProbabilityMeasure Ph] [Ph.InnerRegularCompactLTTop]
    (P : Measure X) [IsProbabilityMeasure P]
    (f : Ω → X) (hf : Continuous f) (hlaw : MeasurePreserving f Ph P)
    (p : X → Prop) (hp : ∀ᵐ ω ∂Ph, p (f ω)) : ∀ᵐ x ∂P, p x := by
  classical
  rw [ae_iff]
  let B : Set X := {x | ¬p x}
  change P B = 0
  by_contra hB
  let eps : ℝ≥0∞ := P B / 2
  have heps : eps ≠ 0 := ne_of_gt (ENNReal.div_pos hB (by norm_num))
  have hepslt : eps < P B := ENNReal.half_lt_self hB (measure_ne_top P B)
  obtain ⟨N, hbadsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  let G : Set Ω := Nᶜ
  have hGmeas : MeasurableSet G := hNmeas.compl
  have hgood : ∀ ω ∈ G, p (f ω) := by
    intro ω hω
    by_contra h
    exact hω (hbadsub h)
  obtain ⟨K, hKG, hK, hdiff⟩ :=
    hGmeas.exists_isCompact_diff_lt (measure_ne_top Ph G) heps
  have hKsmall : Ph Kᶜ < eps := by
    have hsub : Kᶜ ⊆ N ∪ (G \ K) := by
      intro ω hω
      by_cases hN : ω ∈ N
      · exact Or.inl hN
      · exact Or.inr ⟨hN, hω⟩
    have hle : Ph Kᶜ ≤ Ph N + Ph (G \ K) :=
      (measure_mono hsub).trans (measure_union_le N (G \ K))
    rw [hN0, zero_add] at hle
    exact hle.trans_lt hdiff
  have hImage : MeasurableSet (f '' K) := (hK.image hf).isClosed.measurableSet
  have hBsub : B ⊆ (f '' K)ᶜ := by
    intro x hx
    rintro ⟨ω, hω, rfl⟩
    exact hx (hgood ω (hKG hω))
  have hPre : f ⁻¹' (f '' K)ᶜ ⊆ Kᶜ := by
    intro ω hω hKω
    exact hω ⟨ω, hKω, rfl⟩
  have hbound : P B ≤ Ph Kᶜ := by
    calc
      P B ≤ P (f '' K)ᶜ := measure_mono hBsub
      _ = Ph (f ⁻¹' (f '' K)ᶜ) :=
        (hlaw.measure_preimage hImage.compl.nullMeasurableSet).symm
      _ ≤ Ph Kᶜ := measure_mono hPre
  exact (not_lt_of_ge hbound) (hKsmall.trans hepslt)

end SubdiffusiveProcess.AuditRepairs
