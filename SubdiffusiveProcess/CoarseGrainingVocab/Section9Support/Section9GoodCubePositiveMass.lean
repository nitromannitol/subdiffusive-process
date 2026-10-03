module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeMassReduction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeWeightedMassFiniteness

@[expose] public section

/-!
# Positive finite cutoff mass on every positive cube

A cutoff coefficient is continuous and strictly positive for every sample.
Compactness of a bounded cube's closure therefore supplies finite nonzero
weighted mass without a good-event hypothesis. This fact removes an
unnecessary containment requirement from the selected v4 reduction.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Set MeasureTheory
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Every positive-side cube has finite nonzero cutoff mass, for every sample. -/
theorem goodCube_weightedMeasure_aCutoff_ne_zero_ne_top {d : ℕ}
    (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (Q : Cube d) (hQ : 0 < Q.2) :
    weightedMeasure (aCutoff M L omega) (cubeSet Q) ≠ 0 ∧
      weightedMeasure (aCutoff M L omega) (cubeSet Q) ≠ ⊤ := by
  have hB : Bornology.IsBounded (cubeSet Q) := by
    simpa [cubeSet] using
      isBounded_centeredAxisCube Q.1 Q.2
  have hcompact : IsCompact (closure (cubeSet Q)) := hB.isCompact_closure
  have hvol : volume (cubeSet Q) = ENNReal.ofReal (Q.2 ^ d) :=
    volume_cubeSet (le_of_lt hQ)
  have hvolne : volume (cubeSet Q) ≠ 0 := by
    rw [hvol]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hQ d))
  have hvolt : volume (cubeSet Q) ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  have hmeas : MeasurableSet (cubeSet Q) := measurableSet_cubeSet Q
  have hpos : ∀ x ∈ cubeSet Q, 0 < aCutoff M L omega x :=
    fun x _ => aCutoff_pos M L omega x
  have h := SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.setLIntegral_ofReal_ne_zero_and_ne_top_of_compact_closure
    (volume) (cubeSet Q) (aCutoff M L omega)
    (continuous_aCutoff M L omega) hcompact hvolne hvolt hpos
  rw [weightedMeasure, withDensity_apply _ hmeas]
  exact h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
