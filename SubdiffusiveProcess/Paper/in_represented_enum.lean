module

public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



def in_represented_enum
    (d : ℕ) (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) : Prop :=
  ∃ (rootCenter : SpatialCoordinates d) (rootSide : ℝ) (hRootSide : 0 < rootSide),
    (∀ i : Fin d, ∃ q : ℚ, rootCenter i = (q : ℝ)) ∧
    (∃ k : ℤ, rootSide = (3 : ℝ) ^ k) ∧
    ∀ (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0),
      (∀ i : Fin d, ∃ q : ℚ, z0 i = (q : ℝ)) →
      (∃ k : ℤ, r0 = (3 : ℝ) ^ k) →
      (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d)) ⊆
        (centeredCube rootCenter rootSide hRootSide : Set (SpatialCoordinates d)) →
      ∃ i : ℕ, z i = z0 ∧ r i = r0

end Paper
