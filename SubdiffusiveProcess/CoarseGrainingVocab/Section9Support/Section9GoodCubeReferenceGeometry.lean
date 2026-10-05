module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceAffine

@[expose] public section

/-!
# The fixed reference geometry of the version 2 good-cube anchor

Source `mfd:in-deterministic` and `s.tightness`: "Make
these finite choices on a reference cube and transport them by translations and
triadic dilations."  Version 2 of the weighted good-cube events lemma fixes
**one** template `grid0, Pfam0, Qfam0, Afam0` before the model and gives every
native cube the literal translated and triadically dilated image of it.

This file proves that `IsLocalCubeGeometry` is preserved by every such affine
transport, and derives the exact `hgeom` input of
`weighted_good_cube_events_v2_of_supportInputs`: a single reference template
whose transported images are admissible local cube geometries at **every**
scale `n` and lattice site `z`.

Nothing here is probabilistic; the reference template is chosen with the depths
`j1, j2` only, i.e. before the model, exactly as version 2 requires.
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

/-- The affine map `x ↦ y + s • x` transporting the reference template. -/
def affinePhi (y : Vec d) (s : ℝ) : Vec d → Vec d := fun x => y + s • x

/-- The induced map on cubes: `(centre, side) ↦ (y + s • centre, s * side)`. -/
def affineCubeTransport (y : Vec d) (s : ℝ) (Q : Cube d) : Cube d :=
  (y + s • Q.1, s * Q.2)

/-- The induced map on cube pairs. -/
def affinePairTransport (y : Vec d) (s : ℝ) (p : Cube d × Cube d) : Cube d × Cube d :=
  (affineCubeTransport y s p.1, affineCubeTransport y s p.2)

/-- The image finset does not depend on the decidable-equality instance. -/
theorem finset_image_classical {alpha beta : Type*} [DecidableEq beta]
    (f : alpha → beta) (s : Finset alpha) :
    @Finset.image alpha beta (Classical.decEq beta) f s = s.image f := by
  ext b
  simp only [Finset.mem_image]

theorem affinePhi_apply (y : Vec d) (s : ℝ) (x : Vec d) :
    affinePhi y s x = y + s • x := rfl

/-- A nondegenerate affine map transports closures exactly. -/
theorem closure_image_affinePhi (y : Vec d) {s : ℝ} (hs : s ≠ 0) (S : Set (Vec d)) :
    closure (affinePhi y s '' S) = affinePhi y s '' closure S :=
  goodCube_affine_closure y hs S

theorem affinePhi_injective (y : Vec d) {s : ℝ} (hs : s ≠ 0) :
    Function.Injective (affinePhi y s) := by
  intro a b hab
  have h : s • a = s • b := by
    have := congrArg (fun x => x - y) hab
    simpa only [affinePhi, add_sub_cancel_left] using this
  exact smul_right_injective (Vec d) hs h

/-- The point set of a transported cube is the image of the reference point set. -/
theorem cubeSet_affineCubeTransport (y : Vec d) {s : ℝ} (hs : 0 < s) (Q : Cube d) :
    cubeSet (affineCubeTransport y s Q) = affinePhi y s '' cubeSet Q :=
  goodCube_affine_cube_image y Q.1 Q.2 hs

/-- The middle quarter of a transported cube is the image of the reference one. -/
theorem middleQuarter_affineCubeTransport (y : Vec d) {s : ℝ} (hs : 0 < s) (Q : Cube d) :
    middleQuarter (affineCubeTransport y s Q) = affinePhi y s '' middleQuarter Q :=
  goodCube_affine_middleQuarter y Q hs

/-- A concentric sub-cube of a transported cube is the image of the reference one. -/
theorem centeredAxisCube_affineCubeTransport (y : Vec d) {s : ℝ} (hs : 0 < s)
    (Q : Cube d) (t : ℝ) :
    centeredAxisCube (affineCubeTransport y s Q).1 ((affineCubeTransport y s Q).2 / t) =
      affinePhi y s '' centeredAxisCube Q.1 (Q.2 / t) := by
  have h : s * Q.2 / t = s * (Q.2 / t) := by ring
  simpa only [affineCubeTransport, h] using!
    goodCube_affine_cube_image y Q.1 (Q.2 / t) hs

/-- **Affine transport of an admissible local cube geometry.**

`mfd:in-deterministic` and `s.tightness`.  Translation by `y` composed with the
triadic dilation by `s = 3 ^ n` maps every clause of `IsLocalCubeGeometry` to
the corresponding clause of the transported families; the depths `j1, j2` are
unchanged, since they only constrain **ratios** of side lengths.

The grid is **not** transported (as specified for the statement).  The manuscript fixes one family of translated triadic grids
and draws the local families of every cube from that same family;
under the scaled reading of `IsGridCube` an offset is
dimensionless, so the family is literally invariant under the transport
(`goodCube_isGridCube_affine`).  Transporting the offsets as points, as versions
2 and 3 of the anchor did, is refuted by
`goodCube_isGridCube_pointTransport_refutation`. -/
theorem isLocalCubeGeometry_affineTransport {grid0 : Finset (Vec d)} {j1 j2 : ℕ}
    {U0 : Cube d} {Pfam0 : Set (Cube d × Cube d)} {Qfam0 Afam0 : Set (Cube d)}
    (h : IsLocalCubeGeometry grid0 j1 j2 U0 Pfam0 Qfam0 Afam0)
    (hsides : ∀ Q ∈ Qfam0, Q.2 ≤ 1)
    (y : Vec d) (n : ℕ) (hy : ∃ w : Fin d → ℤ, y = fun i => (w i : ℝ) * (3 : ℝ) ^ n) :
    IsLocalCubeGeometry grid0
      j1 j2 (affineCubeTransport y ((3 : ℝ) ^ n) U0)
      (affinePairTransport y ((3 : ℝ) ^ n) '' Pfam0)
      (affineCubeTransport y ((3 : ℝ) ^ n) '' Qfam0)
      (affineCubeTransport y ((3 : ℝ) ^ n) '' Afam0) := by
  classical
  set s : ℝ := (3 : ℝ) ^ n with hsdef
  have hs : (0 : ℝ) < s := by rw [hsdef]; positivity
  have hsne : s ≠ 0 := ne_of_gt hs
  have hinj : Function.Injective (affinePhi y s) := affinePhi_injective y hsne
  have hcube : ∀ Q : Cube d,
      cubeSet (affineCubeTransport y s Q) = affinePhi y s '' cubeSet Q :=
    fun Q => cubeSet_affineCubeTransport y hs Q
  refine
    { finite_Q := h.finite_Q.image _
      finite_P := h.finite_P.image _
      self_mem := ⟨U0, h.self_mem, rfl⟩
      side_pos := ?_
      gridded := ?_
      pair_mem := ?_
      pair_nested := ?_
      pair_middle_half := ?_
      pair_in_half := ?_
      pair_outer_side := ?_
      pair_inner_side := ?_
      cover := ?_
      A_subset := ?_
      A_in_quarter := ?_
      chain := ?_ }
  · rintro _ ⟨Q, hQ, rfl⟩
    exact mul_pos hs (h.side_pos Q hQ)
  · rintro _ ⟨Q, hQ, rfl⟩
    obtain ⟨w, hw⟩ := hy
    have hgrid := goodCube_isGridCube_affine (y := y) (h.gridded Q hQ)
      (hsides Q hQ) n w
      (by rw [hw, hsdef])
    simpa only [affineCubeTransport, affinePhi, hsdef] using hgrid
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨⟨p.1, (h.pair_mem p hp).1, rfl⟩, ⟨p.2, (h.pair_mem p hp).2, rfl⟩⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hnest := h.pair_nested p hp
    show closure (cubeSet (affineCubeTransport y s p.1)) ⊆
      cubeSet (affineCubeTransport y s p.2)
    rw [hcube, hcube, closure_image_affinePhi y hsne]
    exact Set.image_mono hnest
  · rintro _ ⟨p, hp, rfl⟩
    have hhalf := h.pair_middle_half p hp
    show cubeSet (affineCubeTransport y s p.1) ⊆
      centeredAxisCube (affineCubeTransport y s p.2).1
        ((affineCubeTransport y s p.2).2 / 2)
    rw [hcube, centeredAxisCube_affineCubeTransport y hs]
    exact Set.image_mono hhalf
  · rintro _ ⟨p, hp, rfl⟩
    have hhalf := h.pair_in_half p hp
    show cubeSet (affineCubeTransport y s p.2) ⊆
      centeredAxisCube (affineCubeTransport y s U0).1
        ((affineCubeTransport y s U0).2 / 2)
    rw [hcube, centeredAxisCube_affineCubeTransport y hs]
    exact Set.image_mono hhalf
  · rintro _ ⟨p, hp, rfl⟩
    have hside := h.pair_outer_side p hp
    show s * p.2.2 = (3 : ℝ) ^ (-(j1 : ℤ)) * (s * U0.2)
    rw [hside]; ring
  · rintro _ ⟨p, hp, rfl⟩
    have hside := h.pair_inner_side p hp
    show s * p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * (s * p.2.2)
    rw [hside]; ring
  · rw [middleQuarter_affineCubeTransport y hs]
    intro x hx
    obtain ⟨x0, hx0, rfl⟩ := hx
    obtain ⟨p, hp, hxS⟩ := Set.mem_iUnion₂.mp (h.cover hx0)
    refine Set.mem_iUnion₂.mpr ⟨affinePairTransport y s p, ⟨p, hp, rfl⟩, ?_⟩
    show affinePhi y s x0 ∈ cubeSet (affineCubeTransport y s p.1)
    rw [hcube]
    exact ⟨x0, hxS, rfl⟩
  · exact Set.image_mono h.A_subset
  · rintro _ ⟨A, hA, rfl⟩
    have hq := h.A_in_quarter A hA
    rw [hcube, middleQuarter_affineCubeTransport y hs]
    exact Set.image_mono hq
  · rw [middleQuarter_affineCubeTransport y hs]
    rintro _ ⟨x0, hx0, rfl⟩ _ ⟨y0, hy0, rfl⟩
    obtain ⟨k, ch, hchP, hx, hy, hoverlap⟩ := h.chain x0 hx0 y0 hy0
    refine ⟨k, fun i => affineCubeTransport y s (ch i), ?_, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨p, hp, hpe⟩ := hchP i hi
      refine ⟨affinePairTransport y s p, ⟨p, hp, rfl⟩, ?_⟩
      show affineCubeTransport y s (ch i) = affineCubeTransport y s p.1
      rw [hpe]
    · rw [hcube]; exact ⟨x0, hx, rfl⟩
    · rw [hcube]; exact ⟨y0, hy, rfl⟩
    · intro i hi
      obtain ⟨A, hA, hAsub⟩ := hoverlap i hi
      refine ⟨affineCubeTransport y s A, ⟨A, hA, rfl⟩, ?_⟩
      rw [hcube, hcube, hcube, ← Set.image_inter hinj, ← Set.image_inter hinj]
      exact Set.image_mono hAsub

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
