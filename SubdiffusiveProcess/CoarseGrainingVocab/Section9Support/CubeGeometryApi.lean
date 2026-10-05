module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

/-!
# Cube-geometry API for the Section 9 local families

Routine consequences of `cubeSet`, `middleQuarter` and `CompactlyInside`.
-/

set_option autoImplicit false

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube

theorem cubeSet_eq_centeredAxisCube {d : ℕ} (Q : Cube d) :
    cubeSet Q = SubdiffusiveProcess.Section9.centeredAxisCube Q.1 Q.2 := by
  simp [cubeSet]

theorem middleQuarter_eq_centeredAxisCube {d : ℕ} (U : Cube d) :
    middleQuarter U = SubdiffusiveProcess.Section9.centeredAxisCube U.1 (U.2 / 4) := by
  simp [middleQuarter]

theorem compactlyInside_iff {d : ℕ} (Q R : Cube d) :
    CompactlyInside Q R ↔
      closure (cubeSet Q) ⊆ cubeSet R := by
  unfold CompactlyInside
  exact Iff.rfl

theorem cubeSet_subset_of_compactlyInside {d : ℕ} (Q R : Cube d)
    (h : CompactlyInside Q R)
    (x : Vec d) (hx : x ∈ cubeSet Q) :
    x ∈ cubeSet R := by
  unfold CompactlyInside at h
  exact h (subset_closure hx)

theorem compactlyInside_of_subset_left {d : ℕ} (Q M R : Cube d)
    (hQM : cubeSet Q ⊆ cubeSet M)
    (hMR : CompactlyInside M R) :
    CompactlyInside Q R := by
  unfold CompactlyInside at *
  exact le_trans (closure_mono hQM) hMR

theorem cubeSet_nonempty_of_compactlyInside {d : ℕ} (Q R : Cube d)
    (h : CompactlyInside Q R)
    (hne : (closure (cubeSet Q)).Nonempty) :
    (cubeSet R).Nonempty := by
  unfold CompactlyInside at h
  exact hne.mono h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
