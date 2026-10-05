module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.NestedCellGeometry

@[expose] public section

/-!
# The nested cell index and the complete two-radius family

Cells are indexed by a pair: a retained overlap centre `S` (its overlap cube
is the concentric parent, of scale `mm = S.scale + 1 = K - j`) and a
descendant `R₀` of the **origin** inner parent `originCube d (mm - a)`, where
`a = depth + 1` is the fixed Calderon--Zygmund interior depth.  The cell is
`R₀` translated to `cubeCenter S`.

Taking *all* descendants of the inner parent — rather than the single
concentric cell — is what makes the Dirichlet member's fourth moment a
genuine descendant average, hence controlled by
`exists_lintegral_nfOriginDirichlet_descendantCellB_source_le` up to the
`N`-independent constant `(3^d)^a`.  Every cell still sits inside the fixed
concentric interior of its parent, so the two harmonic estimates are
unaffected.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Lattice shift carrying an origin-centred cell to its copy at
`cubeCenter S`. -/
def nfCellShift (S : TriadicCube d) (N : ℕ) : Fin d → ℤ :=
  fun i => S.index i * 3 ^ (N - 1)

theorem nfCellShift_translate_eq (S : TriadicCube d) {N : ℕ} (hN : 1 ≤ N)
    {mm : ℤ} (hmm : S.scale + 1 = mm) (R₀ : TriadicCube d)
    (hR₀ : R₀.scale = mm - (N : ℤ)) :
    (fun i => ((nfCellShift S N i : ℤ) : ℝ) * cubeScaleFactor R₀) =
      cubeCenter S := by
  funext i
  have hthree : (3 : ℝ) ≠ 0 := by norm_num
  have hexp : (((N - 1 : ℕ) : ℤ)) + (mm - (N : ℤ)) = S.scale := by omega
  simp only [nfCellShift, cubeCenter, cubeScaleFactor, hR₀]
  push_cast
  rw [← zpow_natCast (3 : ℝ) (N - 1), mul_assoc, ← zpow_add₀ hthree, hexp]

theorem openCubeSet_nfCell_eq (S : TriadicCube d) {N : ℕ} (hN : 1 ≤ N)
    {mm : ℤ} (hmm : S.scale + 1 = mm) (R₀ : TriadicCube d)
    (hR₀ : R₀.scale = mm - (N : ℤ)) :
    openCubeSet (translateCube (nfCellShift S N) R₀) =
      translateSet (cubeCenter S) (openCubeSet R₀) := by
  rw [openCubeSet_translateCube_eq,
    nfCellShift_translate_eq S hN hmm R₀ hR₀]

theorem translateSet_mono (z : Vec d) {A B : Set (Vec d)} (hAB : A ⊆ B) :
    translateSet z A ⊆ translateSet z B := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, hAB hy, rfl⟩

/-! ## The index -/

/-- Index of the nested cell family. -/
abbrev NFNestedIndex (d : ℕ) (K : ℤ) (j : ℕ) (P₀ : TriadicCube d) (k : ℕ) :=
  NFOverlapIndex d K j ×
    {R₀ : TriadicCube d // R₀ ∈ descendantsAtDepth P₀ k}

/-- The cell attached to a nested index. -/
def nfNestedCell {K : ℤ} {j : ℕ} (N : ℕ) {P₀ : TriadicCube d} {k : ℕ}
    (q : NFNestedIndex d K j P₀ k) : TriadicCube d :=
  translateCube (nfCellShift q.1.1 N) q.2.1

@[simp] theorem nfNestedCell_scale {K : ℤ} {j : ℕ} (N : ℕ)
    {P₀ : TriadicCube d} {k : ℕ} (q : NFNestedIndex d K j P₀ k) :
    (nfNestedCell N q).scale = (q.2.1).scale := rfl

/-- Every nested cell has the scale gap `N` to its concentric parent. -/
theorem nfNestedCell_scale_add {K : ℤ} {j N : ℕ} {mm : ℤ}
    {P₀ : TriadicCube d} {a k : ℕ} (hP₀ : P₀.scale = mm - (a : ℤ))
    (hak : a + k = N) (q : NFNestedIndex d K j P₀ k) :
    (nfNestedCell N q).scale + (N : ℤ) = mm := by
  have hR := scale_eq_sub_of_mem_descendantsAtDepth q.2.2
  simp only [nfNestedCell_scale, hR, hP₀]
  omega

/-- Every nested cell sits inside the fixed concentric interior of its
parent. -/
theorem openCubeSet_nfNestedCell_subset_concentric
    {K : ℤ} {j N : ℕ} {mm : ℤ} {a k : ℕ}
    (hN : 1 ≤ N) (hak : a + k = N)
    (hmm : ∀ S : NFOverlapIndex d K j, (S.1).scale + 1 = mm)
    (q : NFNestedIndex d K j (originCube d (mm - (a : ℤ))) k) :
    openCubeSet (nfNestedCell N q) ⊆
      axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner
          (oneStepCenteredAxisCorner (cubeCenter q.1.1) mm)
          (cubeScaleFactor (originCube d mm)) a)
        (CubeCalderonZygmund.axisCubeConcentricDepthSide
          (cubeScaleFactor (originCube d mm)) a) := by
  have hR : (q.2.1).scale = mm - (N : ℤ) := by
    have := scale_eq_sub_of_mem_descendantsAtDepth q.2.2
    simp only [originCube] at this
    omega
  rw [nfAxisConcentric_eq_translate d (cubeCenter q.1.1) mm a]
  rw [nfNestedCell, openCubeSet_nfCell_eq q.1.1 hN (hmm q.1) q.2.1 hR]
  exact translateSet_mono _
    (openCubeSet_subset_of_mem_descendantsAtDepth q.2.2)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
