module

public import SubdiffusiveProcess.Section10.InitialSimplexPackingGeometry

@[expose] public section

/-! The actual coordinate-order facets of the initial Kuhn simplex. -/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

theorem mem_initialSimplex_iff {ell : ℕ} {pi : Equiv.Perm (Fin d)} {x : Vec d} :
    x ∈ (initialSimplex ell pi).openCarrier ↔
      x ∈ openCubeSet (originCube d (ell : ℤ)) ∧
        ∀ i j : Fin d, i.val < j.val → x (pi i) < x (pi j) := by
  simpa [initialSimplex, Kuhn.triadicLocalCoordinate, originCube] using
    (Kuhn.KuhnCell.mem_openCarrier_iff (T := initialSimplex ell pi) (x := x))

/-- Containment in the open simplex is precisely strict ordering of the
integer grid indices. Adjacent grid intervals still have strictly ordered
open interiors. -/
theorem descendant_subset_initialSimplex_iff {ell n : ℕ}
    {pi : Equiv.Perm (Fin d)} {Q : TriadicCube d}
    (hQ : Q ∈ descendantsAtDepth (originCube d (ell : ℤ)) n) :
    openCubeSet Q ⊆ (initialSimplex ell pi).openCarrier ↔
      ∀ i j : Fin d, i.val < j.val → Q.index (pi i) < Q.index (pi j) := by
  have hs : 0 < cubeScaleFactor Q := by
    exact zpow_pos (by norm_num) Q.scale
  constructor
  · intro hsub i j hij
    have hc : cubeCenter Q ∈ openCubeSet Q := by
      rw [← ball_cubeCenter_eq_openCubeSet]
      exact Metric.mem_ball_self (cubeRadius_pos Q)
    have h := (mem_initialSimplex_iff.mp (hsub hc)).2 i j hij
    change (Q.index (pi i) : ℝ) * cubeScaleFactor Q <
      (Q.index (pi j) : ℝ) * cubeScaleFactor Q at h
    exact_mod_cast (mul_lt_mul_iff_left₀ hs).mp h
  · intro hord x hx
    refine mem_initialSimplex_iff.mpr
      ⟨openCubeSet_subset_of_mem_descendantsAtDepth hQ hx, ?_⟩
    intro i j hij
    have hidx : (Q.index (pi i) : ℝ) + 1 ≤ Q.index (pi j) := by
      exact_mod_cast hord i j hij
    have hsep : ((Q.index (pi i) : ℝ) + 1 / 2) * cubeScaleFactor Q ≤
        ((Q.index (pi j) : ℝ) - 1 / 2) * cubeScaleFactor Q := by
      apply mul_le_mul_of_nonneg_right _ hs.le
      linarith
    exact lt_trans (hx (pi i)).2 (lt_of_le_of_lt hsep (hx (pi j)).1)

/-- Meeting the simplex forces weak ordering of the grid indices. -/
theorem index_le_of_inter_initialSimplex {ell : ℕ} {pi : Equiv.Perm (Fin d)}
    {Q : TriadicCube d} (h : (cubeSet Q ∩ (initialSimplex ell pi).openCarrier).Nonempty)
    (i j : Fin d) (hij : i.val < j.val) : Q.index (pi i) ≤ Q.index (pi j) := by
  obtain ⟨x, hxQ, hxU⟩ := h
  have hord := (mem_initialSimplex_iff.mp hxU).2 i j hij
  have hs : 0 < cubeScaleFactor Q := zpow_pos (by norm_num) Q.scale
  by_contra hle
  have hidx : (Q.index (pi j) : ℝ) + 1 ≤ Q.index (pi i) := by
    exact_mod_cast (show Q.index (pi j) + 1 ≤ Q.index (pi i) by omega)
  have hsep : ((Q.index (pi j) : ℝ) + 1 / 2) * cubeScaleFactor Q ≤
      ((Q.index (pi i) : ℝ) - 1 / 2) * cubeScaleFactor Q := by
    apply mul_le_mul_of_nonneg_right _ hs.le
    linarith
  have hlo := (hxQ (pi i)).1
  have hhi := (hxQ (pi j)).2
  linarith

/-- The only unresolved descendants lie on a coordinate-equality facet at
the integer-grid level. This supplies the finite counting problem. -/
theorem unresolved_initialSimplex_has_equal_indices {ell n : ℕ}
    {pi : Equiv.Perm (Fin d)} {Q : TriadicCube d}
    (hQ : Q ∈ unresolvedAtDepth (originCube d (ell : ℤ))
      (initialSimplex ell pi).openCarrier n) :
    ∃ i j : Fin d, i.val < j.val ∧ Q.index (pi i) = Q.index (pi j) := by
  obtain ⟨hQR, hinter, hnot⟩ := mem_unresolvedAtDepth.mp hQ
  have hnot' := (descendant_subset_initialSimplex_iff hQR).not.mp hnot
  push Not at hnot'
  obtain ⟨i, j, hij, hle⟩ := hnot'
  exact ⟨i, j, hij, le_antisymm (index_le_of_inter_initialSimplex hinter i j hij) hle⟩

theorem originCube_not_subset_initialSimplex (hd : 2 ≤ d) (ell : ℕ)
    (pi : Equiv.Perm (Fin d)) :
    ¬ openCubeSet (originCube d (ell : ℤ)) ⊆ (initialSimplex ell pi).openCarrier := by
  intro h
  have hord := (descendant_subset_initialSimplex_iff
    (show originCube d (ell : ℤ) ∈ descendantsAtDepth (originCube d (ell : ℤ)) 0
      by simp)).mp h
  have hbad := hord ⟨0, by omega⟩ ⟨1, by omega⟩ (by norm_num)
  simp [originCube] at hbad

/-- The literal finite packing, as input to the translated-cell supplier. -/
def initialSimplexPackingCubes (ell : ℕ) (pi : Equiv.Perm (Fin d)) :
    Finset (TriadicCube d) :=
  maximalContainedPacking (originCube d (ell : ℤ)) (initialSimplex ell pi).openCarrier ell

def initialSimplexPackingDepth (ell : ℕ) (Q : TriadicCube d) : ℕ :=
  packingCubeDepth (originCube d (ell : ℤ)) Q

def initialSimplexUnresolved (ell : ℕ) (pi : Equiv.Perm (Fin d)) (n : ℕ) :
    Finset (TriadicCube d) :=
  unresolvedAtDepth (originCube d (ell : ℤ)) (initialSimplex ell pi).openCarrier n

theorem initialSimplexPacking_depth_bounds {ell : ℕ} {pi : Equiv.Perm (Fin d)}
    {Q : TriadicCube d} (hQ : Q ∈ initialSimplexPackingCubes ell pi) :
    0 < initialSimplexPackingDepth ell Q ∧ initialSimplexPackingDepth ell Q ≤ ell ∧
      Q.scale = ((ell - initialSimplexPackingDepth ell Q : ℕ) : ℤ) := by
  obtain ⟨hp, hl, hs⟩ := maximalContainedPacking_depth_bounds hQ
  refine ⟨hp, hl, ?_⟩
  change Q.scale = (ell : ℤ) - (initialSimplexPackingDepth ell Q : ℤ) at hs
  change initialSimplexPackingDepth ell Q ≤ ell at hl
  rw [Nat.cast_sub hl]
  exact hs

theorem initialSimplexPacking_subset {ell : ℕ} {pi : Equiv.Perm (Fin d)}
    {Q : TriadicCube d} (hQ : Q ∈ initialSimplexPackingCubes ell pi) :
    openCubeSet Q ⊆ (initialSimplex ell pi).openCarrier :=
  maximalContainedPacking_subset hQ

theorem initialSimplexPacking_disjoint (ell : ℕ) (pi : Equiv.Perm (Fin d)) :
    (initialSimplexPackingCubes ell pi : Set (TriadicCube d)).PairwiseDisjoint openCubeSet :=
  maximalContainedPacking_pairwiseDisjoint_open _ _ _

theorem initialSimplexPacking_cover (hd : 2 ≤ d) (ell : ℕ) (pi : Equiv.Perm (Fin d)) :
    (initialSimplex ell pi).openCarrier ⊆
      (⋃ Q ∈ initialSimplexPackingCubes ell pi, cubeSet Q) ∪
        ⋃ Q ∈ initialSimplexUnresolved ell pi ell, cubeSet Q := by
  apply maximalContainedPacking_cover
  · exact (Kuhn.KuhnCell.openCarrier_subset_openCubeSet _).trans
      (openCubeSet_subset_cubeSet _)
  · exact originCube_not_subset_initialSimplex hd ell pi

@[simp] theorem initialSimplexPackingCubes_zero (pi : Equiv.Perm (Fin d)) :
    initialSimplexPackingCubes 0 pi = ∅ := by
  simp [initialSimplexPackingCubes, maximalContainedPacking]

end
end SubdiffusiveProcess.Section10
