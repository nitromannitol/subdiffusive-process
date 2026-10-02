import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.SevenACoefficientHull
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTranslation




set_option autoImplicit false

open Homogenization hiding Vec
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Spatial translations preserve the outer probability of arbitrary events. -/
theorem measure_preimage_translatePotentialSequence {d : ℕ} (M : GMCModel d)
    (z : Vec d) (s : Set (PotentialSample d)) :
    M.P.toMeasure (translatePotentialSequence z ⁻¹' s) = M.P.toMeasure s := by
  exact Section6Covariance.measure_preimage_translatePotentialSample M z s

/-- The native box at a site is the translate of the reference box. -/
theorem nativeBox_origin_image {d : ℕ} (n : ℕ) (C : ℝ) (z : Lattice d) :
    nativeBox n C z =
      (fun x : Vec d => x + goodCubeCentre n z) '' nativeBox n C 0 := by
  simpa only [zero_add] using nativeBox_add n C (0 : Lattice d) z

/-- Positive box factors give a nonempty observation window. -/
theorem nativeBox_nonempty {d : ℕ} (n : ℕ) {C : ℝ} (hC : 0 < C)
    (z : Lattice d) : (nativeBox n C z).Nonempty := by
  refine ⟨goodCubeCentre n z, ?_⟩
  change goodCubeCentre n z ∈ SubdiffusiveProcess.Section9.centeredAxisCube
    (goodCubeCentre n z) (C * (3 : ℝ) ^ n)
  rw [mem_centeredAxisCube]
  intro i
  simp only [sub_self, abs_zero]
  positivity

/-- Translating a single reference event gives exact lattice covariance. -/
theorem translatedEvent_covariant {d : ℕ} (n : ℕ) (s : Set (PotentialSample d))
    (z a : Lattice d) :
    translatePotentialSequence (goodCubeCentre n (z + a)) ⁻¹' s =
      translatePotentialSequence (goodCubeCentre n a) ⁻¹'
        (translatePotentialSequence (goodCubeCentre n z) ⁻¹' s) := by
  ext w
  simp only [Set.mem_preimage]
  have h := Section6Covariance.translatePotentialSample_translate
    (goodCubeCentre n a) (goodCubeCentre n z) w
  change translatePotentialSequence (goodCubeCentre n z)
    (translatePotentialSequence (goodCubeCentre n a) w) =
    translatePotentialSequence (goodCubeCentre n a + goodCubeCentre n z) w at h
  rw [h, goodCubeCentre_add, add_comm (goodCubeCentre n z) (goodCubeCentre n a)]

/-- A reference-box coefficient predicate, transported to each lattice site.
The predicate need not be measurable. -/
def coefficientLocalBadEvent {d : ℕ} (M : GMCModel d) (n : ℕ) (C : ℝ)
    (bad : Set (nativeBox n C (0 : Lattice d) → ℝ))
    (z : Lattice d) : Set (PotentialSample d) :=
  translatePotentialSequence (goodCubeCentre n z) ⁻¹'
    (restrictedCoefficientObservation (aCutoff M n) (nativeBox n C 0) ⁻¹' bad)

/-- Clause 7a at every site, with pointwise containment, unchanged outer
probability, and exact covariance. This applies to the full local analytic
bad predicate, including all three components of the manuscript's `G(U)`. -/
theorem exists_coefficientLocalBadEvent_hull {d : ℕ} (M : GMCModel d) (n : ℕ)
    {C : ℝ} (hC : 0 < C) (bad : Set (nativeBox n C (0 : Lattice d) → ℝ)) :
    ∃ E0 : Lattice d → Set (PotentialSample d),
      (∀ z, MeasurableSet[restrictedCoefficientSigma (aCutoff M n)
        (nativeBox n C z)] (E0 z)) ∧
      (∀ z, coefficientLocalBadEvent M n C bad z ⊆ E0 z) ∧
      (∀ z, M.P.toMeasure (E0 z) =
        M.P.toMeasure (coefficientLocalBadEvent M n C bad z)) ∧
      ∀ z a, E0 (z + a) =
        translatePotentialSequence (goodCubeCentre n a) ⁻¹' (E0 z) := by
  obtain ⟨x, hx⟩ := nativeBox_nonempty n hC (0 : Lattice d)
  letI : Nonempty (nativeBox n C (0 : Lattice d)) := ⟨⟨x, hx⟩⟩
  obtain ⟨S, hS, hsub, hmu⟩ :=
    exists_cutoff_local_measurable_hull M n (nativeBox n C 0) bad
  refine ⟨fun z => translatePotentialSequence (goodCubeCentre n z) ⁻¹' S,
    ?_, ?_, ?_, ?_⟩
  · intro z
    rw [nativeBox_origin_image]
    exact measurableSet_preimage_translate_restricted M n _ _ hS
  · intro z
    exact Set.preimage_mono hsub
  · intro z
    unfold coefficientLocalBadEvent
    rw [measure_preimage_translatePotentialSequence,
      measure_preimage_translatePotentialSequence, hmu]
  · intro z a
    exact translatedEvent_covariant n S z a

/-- Enlarging only the layer-zero bad event shrinks the good-cube event
pointwise. Consequently every analytic conclusion on the old good event
continues to hold on the new one, for the same sample and diffusion law. -/
theorem goodCubeEvent_mono_layerZero {d : ℕ} (n : ℕ) (C e : ℝ)
    (s t : Lattice d → Set (PotentialSample d)) (hst : ∀ z, s z ⊆ t z)
    (z : Lattice d) :
    goodCubeEvent (goodCubeEventField n C e t) z ⊆
      goodCubeEvent (goodCubeEventField n C e s) z := by
  intro w hw
  apply Set.mem_iInter.mpr
  intro j
  have hj := Set.mem_iInter.mp hw j
  cases j with
  | zero => exact fun h => hj (hst z h)
  | succ j => exact hj

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
