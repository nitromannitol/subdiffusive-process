module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicHalfMeasureAlternative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialHarmonicHalfMeasure

@[expose] public section

/-! # Essential interval reduction for bounded H¹ weak solutions -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Values in `[0,1]` lose a fixed dimensional interval on the eighth
cube, on one side or the other. -/
theorem exists_essential_harmonic_interval_reduction {d : ℕ} (hd : 2 ≤ d) :
    ∃ k : ℝ, 0 < k ∧ k ≤ 1 / 8 ∧
      ∀ (a : Vec d → ℝ) (z : Vec d),
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z 1), 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z 1)) →
      ∀ h : H1Function (centeredAxisCube z 1), IsWeaklyHarmonicOn a (centeredAxisCube z 1) h →
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z 1), 0 ≤ h.toFun x ∧ h.toFun x ≤ 1) →
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z (1 / 8)), k ≤ h.toFun x) ∨
      (∀ᵐ x ∂volume.restrict (centeredAxisCube z (1 / 8)), h.toFun x ≤ 1 - k) := by
  obtain ⟨delta, hdelta, hdelta1, hlower⟩ := exists_essential_harmonic_half_measure_lower hd
  refine ⟨delta / 2, by positivity, by linarith, ?_⟩
  intro a z hab ha h hh hh01
  let Q := centeredAxisCube z (1 / 2)
  have hQsub : Q ⊆ centeredAxisCube z 1 := centeredAxisCube_mono (by norm_num)
  letI : IsFiniteMeasure (volume.restrict Q) :=
    (isOpenBoundedConvexDomain_axisCube (fun i => z i - (1 / 2) / 2) (1 / 2)).isFiniteMeasure_restrict_volume
  have hmeas : AEStronglyMeasurable h.toFun (volume.restrict Q) :=
    h.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hQsub le_rfl)
  rcases harmonic_half_measure_alternative hmeas with ⟨E, _, hhalf, hgood⟩ | ⟨E, _, hhalf, hgood⟩
  · left
    exact hlower a z hab ha h hh hh01 E
      (by simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using! hhalf) hgood
  · right
    letI : IsFiniteMeasure (volume.restrict (centeredAxisCube z 1)) :=
      (isOpenBoundedConvexDomain_axisCube (fun i => z i - 1 / 2) 1).isFiniteMeasure_restrict_volume
    let g := ((-1 : ℝ) • h).addConst 1
    have hg := essential_harmonic_affine h hh (-1) 1
    have hgf : g.toFun = fun x => 1 - h.toFun x := by
      funext x
      change (-1 : ℝ) * h.toFun x + 1 = _
      ring
    have hg01 : ∀ᵐ x ∂volume.restrict (centeredAxisCube z 1), 0 ≤ g.toFun x ∧ g.toFun x ≤ 1 := by
      filter_upwards [hh01] with x hx
      rw [hgf]
      constructor <;> linarith
    have hgoodg : ∀ᵐ x ∂(volume.restrict Q).restrict E, 1 / 2 ≤ g.toFun x := by
      simpa only [hgf] using! hgood
    have hl := hlower a z hab ha g hg hg01 E
      (by simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using! hhalf) hgoodg
    filter_upwards [hl] with x hx
    rw [hgf] at hx
    linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
