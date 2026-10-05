module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeAuxGeometryCovers
public import Mathlib.Topology.Separation.Regular

@[expose] public section

/-!
# Auxiliary neighborhoods and covers of the original finite cube family

For every original compact descendant pair, choose an open neighborhood with
compact closure inside the outer cube. The neighborhoods precede the side
caps and depths. Subsequent compactness gives one common outer depth and one
cardinality bound for all auxiliary covers. The original family is unchanged.
-/

set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Compact descendant pairs drawn only from the fixed original cube family. -/
abbrev GoodCubeCompactPair {d : ℕ} (Qfam : Set (Cube d)) :=
  {p : Cube d × Cube d // p.1 ∈ Qfam ∧ p.2 ∈ Qfam ∧ CompactlyInside p.1 p.2}

/-- A finite original family has only finitely many compact descendant pairs. -/
theorem goodCube_compact_pair_finite {d : ℕ} {Qfam : Set (Cube d)}
    (hQfam : Qfam.Finite) : Finite (GoodCubeCompactPair Qfam) := by
  have hP : ({p : Cube d × Cube d |
      p.1 ∈ Qfam ∧ p.2 ∈ Qfam ∧ CompactlyInside p.1 p.2}).Finite :=
    (hQfam.prod hQfam).subset (fun p hp => ⟨hp.1, hp.2.1⟩)
  exact hP.to_subtype

/-- The fixed original family admits interior neighborhoods and arbitrarily small finite auxiliary covers. -/
theorem exists_goodCube_auxiliary_family_geometry {d : ℕ}
    (Qfam : Set (Cube d)) (hQfam : Qfam.Finite) :
    ∃ W : GoodCubeCompactPair Qfam → Set (Vec d),
      (∀ p, IsOpen (W p) ∧ closure (cubeSet p.val.1) ⊆ W p ∧
        closure (W p) ⊆ cubeSet p.val.2 ∧ IsCompact (closure (W p))) ∧
      ∀ (eta : GoodCubeCompactPair Qfam → ℝ), (∀ p, 0 < eta p) →
        ∀ j k0 : ℕ,
          ∃ (k N : ℕ) (centers : GoodCubeCompactPair Qfam → Finset (Vec d)),
            k0 ≤ k ∧ ∀ p, (3 : ℝ) ^ (-(k : ℤ)) ≤ eta p ∧
              (centers p).card ≤ N ∧
              (↑(centers p) : Set (Vec d)) ⊆ closure (cubeSet p.val.1) ∧
              closure (cubeSet p.val.1) ⊆ ⋃ x ∈ centers p,
                centeredAxisCube x
                  ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (-(k : ℤ))) ∧
              ∀ x ∈ centers p,
                closure (centeredAxisCube x ((3 : ℝ) ^ (-(k : ℤ)))) ⊆ W p := by
  have hP : ({p : Cube d × Cube d |
      p.1 ∈ Qfam ∧ p.2 ∈ Qfam ∧ CompactlyInside p.1 p.2}).Finite :=
    (hQfam.prod hQfam).subset (fun p hp => ⟨hp.1, hp.2.1⟩)
  let : Finite (GoodCubeCompactPair Qfam) := hP.to_subtype
  have hK : ∀ p : GoodCubeCompactPair Qfam,
      IsCompact (closure (cubeSet p.val.1)) :=
    fun p => Bornology.IsBounded.isCompact_closure
      (isBounded_centeredAxisCube p.val.1.1 p.val.1.2)
  have hex : ∀ p : GoodCubeCompactPair Qfam, ∃ V, IsOpen V ∧
      closure (cubeSet p.val.1) ⊆ V ∧ closure V ⊆ cubeSet p.val.2 ∧
      IsCompact (closure V) :=
    fun p => exists_open_between_and_isCompact_closure (hK p)
      (isOpen_centeredAxisCube p.val.2.1 p.val.2.2) p.property.2.2
  choose W hWprop using hex
  refine ⟨W, hWprop, ?_⟩
  intro eta heta j k0
  have hKW : ∀ p : GoodCubeCompactPair Qfam,
      closure (cubeSet p.val.1) ⊆ W p := fun p => (hWprop p).2.1
  have hres := exists_goodCube_auxiliary_covers (d := d)
    (ι := GoodCubeCompactPair Qfam)
    (K := fun (p : GoodCubeCompactPair Qfam) => closure (cubeSet p.val.1))
    (W := W) hK (fun (p : GoodCubeCompactPair Qfam) => (hWprop p).1) hKW
    eta heta j k0
  obtain ⟨k, N, centers, hk0, hrest⟩ := hres
  exact ⟨k, N, centers, hk0, hrest⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
