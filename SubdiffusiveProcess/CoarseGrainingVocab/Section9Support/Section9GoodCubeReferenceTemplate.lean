module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeProviderV2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceGeometry

@[expose] public section

/-!
# The reference template input of the version 2 good-cube anchor

Version 2 of
the good-cube events lemma  fixes one template on the unit reference
cube and transports it.  Combining `exists_isLocalCubeGeometry` at the unit
cube centred at the origin with the affine transport of
`Section9GoodCubeReferenceGeometry`, the `hgeom` input of
`weighted_good_cube_events_v2_of_supportInputs` is **discharged**: for every
pair of depths `j1 ≥ 2`, `j2 ≥ 1` there is one reference template whose
transported images are admissible local cube geometries at every scale and
every lattice site.

The template depends on `j1, j2` only, hence is chosen before the model, as
version 2 requires.
-/

set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-- The block's cube map is the affine transport of this file. -/
theorem goodCubeReferenceTransport_eq_affine (n : ℕ) (z : Lattice d) (Q : Cube d) :
    goodCubeReferenceTransport n z Q =
      affineCubeTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) Q := rfl

/-- The block's pair image is the affine transport of this file. -/
theorem goodCubeReferencePairs_eq_affine (Pfam0 : Set (Cube d × Cube d))
    (n : ℕ) (z : Lattice d) :
    goodCubeReferencePairs Pfam0 n z =
      affinePairTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) '' Pfam0 := rfl

/-- The block's family image is the affine transport of this file. -/
theorem goodCubeReferenceFamily_eq_affine (Qfam0 : Set (Cube d)) (n : ℕ) (z : Lattice d) :
    goodCubeReferenceFamily Qfam0 n z =
      affineCubeTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) '' Qfam0 := rfl

/-- The unit reference cube is carried to the native cube of the site. -/
theorem affineCubeTransport_unit (n : ℕ) (z : Lattice d) :
    affineCubeTransport (goodCubeCentre n z) ((3 : ℝ) ^ n)
        ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ)) = (goodCubeCentre n z, (3 : ℝ) ^ n) := by
  simp [affineCubeTransport]

/-- **Confining an admissible geometry to its parent cube.**

`IsLocalCubeGeometry` does not itself force `Qfam` into the parent cube — that
is exactly the freedom exploited by the version 1 mass obstruction
(`Section9GoodCubeMassObstruction`).  Discarding the cubes that
leave the parent preserves every clause: the paired cubes lie in the middle
half of the parent, and the overlap cubes lie in its middle quarter, so no
cube used by `cover`, `chain` or `A_subset` is discarded.

The manuscript's families are drawn inside the reference cube
and confining them is what lets the
mass constant be read off the family's volume ratios. -/
theorem isLocalCubeGeometry_restrict_inside {grid0 : Finset (Vec d)} {j1 j2 : ℕ}
    {U0 : Cube d} {Pfam0 : Set (Cube d × Cube d)} {Qfam0 Afam0 : Set (Cube d)}
    (h : IsLocalCubeGeometry grid0 j1 j2 U0 Pfam0 Qfam0 Afam0) :
    IsLocalCubeGeometry grid0 j1 j2 U0 Pfam0
      {Q ∈ Qfam0 | cubeSet Q ⊆ cubeSet U0} Afam0 := by
  have hU0 : 0 < U0.2 := h.side_pos U0 h.self_mem
  have hhalf : centeredAxisCube U0.1 (U0.2 / 2) ⊆ cubeSet U0 :=
    centeredAxisCube_mono (by linarith)
  have hquarter : middleQuarter U0 ⊆ cubeSet U0 :=
    centeredAxisCube_mono (by linarith)
  have houter : ∀ p ∈ Pfam0, cubeSet p.2 ⊆ cubeSet U0 :=
    fun p hp => (h.pair_in_half p hp).trans hhalf
  have hinner : ∀ p ∈ Pfam0, cubeSet p.1 ⊆ cubeSet U0 := fun p hp =>
    (subset_closure.trans (h.pair_nested p hp)).trans (houter p hp)
  refine
    { finite_Q := h.finite_Q.subset (fun Q hQ => hQ.1)
      finite_P := h.finite_P
      self_mem := ⟨h.self_mem, subset_rfl⟩
      side_pos := fun Q hQ => h.side_pos Q hQ.1
      gridded := fun Q hQ => h.gridded Q hQ.1
      pair_mem := ?_
      pair_nested := h.pair_nested
      pair_middle_half := h.pair_middle_half
      pair_in_half := h.pair_in_half
      pair_outer_side := h.pair_outer_side
      pair_inner_side := h.pair_inner_side
      cover := h.cover
      A_subset := ?_
      A_in_quarter := h.A_in_quarter
      chain := h.chain }
  · intro p hp
    exact ⟨⟨(h.pair_mem p hp).1, hinner p hp⟩, ⟨(h.pair_mem p hp).2, houter p hp⟩⟩
  · intro A hA
    exact ⟨h.A_subset hA, (h.A_in_quarter A hA).trans hquarter⟩

/-- Membership in the confined family. -/
theorem mem_restrict_inside {U0 Q : Cube d} {Qfam0 : Set (Cube d)}
    (hQ : Q ∈ {Q ∈ Qfam0 | cubeSet Q ⊆ cubeSet U0}) : cubeSet Q ⊆ cubeSet U0 := hQ.2

/-- **The `hgeom` input of the version 2 provider, discharged.**

One reference template, depending only on the depths, whose literal translated
and triadically dilated images are admissible local cube geometries at every
scale `n` and every lattice site `z`. -/
theorem exists_goodCubeReferenceTemplate (d : ℕ) {j1 j2 : ℕ} (hj1 : 2 ≤ j1) (hj2 : 1 ≤ j2) :
    ∃ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
      (Qfam0 Afam0 : Set (Cube d)),
      IsLocalCubeGeometry grid0 j1 j2 ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))
          Pfam0 Qfam0 Afam0 ∧
      (∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))) ∧
      ∀ (n : ℕ) (z : Lattice d),
        IsLocalCubeGeometry grid0 j1 j2
          (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferencePairs Pfam0 n z)
          (goodCubeReferenceFamily Qfam0 n z) (goodCubeReferenceFamily Afam0 n z) := by
  obtain ⟨grid0, Pfam0, Qfam1, Afam0, h1, hside1, -⟩ :=
    exists_isLocalCubeGeometry (0 : Vec d) 0 j1 j2 hj1 hj2
  have hsides : ∀ Q ∈ {Q ∈ Qfam1 | cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))},
      Q.2 ≤ 1 := by
    intro Q hQ
    simpa using hside1 Q hQ.1
  refine ⟨grid0, Pfam0, {Q ∈ Qfam1 | cubeSet Q ⊆ cubeSet ((0 : Vec d), (3 : ℝ) ^ (0 : ℕ))},
    Afam0, isLocalCubeGeometry_restrict_inside h1, fun Q hQ => hQ.2, fun n z => ?_⟩
  have h := isLocalCubeGeometry_affineTransport (isLocalCubeGeometry_restrict_inside h1)
    hsides (goodCubeCentre n z) n ⟨z, rfl⟩
  rwa [affineCubeTransport_unit n z] at h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
