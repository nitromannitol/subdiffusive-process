module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionGraphDistance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsExterior

@[expose] public section

/-!
# Feeding an overlapping stopping graph to the exterior row

`wholeSpaceSolution_exterior_decay_of_stopping_cells` is phrased using a
finite enumeration of every graph sphere.  A stopping construction is more
naturally indexed by one countable cell type with a graph and a finite source
family.  This file proves the exact adapter between those presentations.

The cells are merely a cover.  No disjointness or tiling hypothesis occurs:
this is essential because the consumer asks for a literal cover of each open
centred enlargement.  In the Section 8 construction the intended cells are
the half-spaced overlapping cells of `StoppingPartitionFailureHeight`.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Section8
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Number of cells in the `j`-th finite graph sphere. -/
def stoppingLevelCellCount {Cell : Type*} (levelCells : ℕ → Finset Cell)
    (j : ℕ) : ℕ :=
  (levelCells j).card

/-- The cell represented by an index in a finite graph sphere. -/
def stoppingLevelCellIndex {Cell : Type*} (levelCells : ℕ → Finset Cell)
    (j : ℕ) (i : Fin (stoppingLevelCellCount levelCells j)) : Cell :=
  ((levelCells j).equivFin.symm i : levelCells j)

theorem stoppingLevelCellIndex_mem {Cell : Type*}
    (levelCells : ℕ → Finset Cell) (j : ℕ)
    (i : Fin (stoppingLevelCellCount levelCells j)) :
    stoppingLevelCellIndex levelCells j i ∈ levelCells j :=
  ((levelCells j).equivFin.symm i).2

/-- Position of a cell in the enumeration of its graph sphere. -/
def stoppingLevelFinIndex {Cell : Type*} (levelCells : ℕ → Finset Cell)
    (level : Cell → ℕ) (hlevel : ∀ j q, q ∈ levelCells j ↔ level q = j)
    (q : Cell) : Fin (stoppingLevelCellCount levelCells (level q)) :=
  (levelCells (level q)).equivFin ⟨q, (hlevel (level q) q).2 rfl⟩

@[simp]
theorem stoppingLevelCellIndex_stoppingLevelFinIndex {Cell : Type*}
    (levelCells : ℕ → Finset Cell)
    (level : Cell → ℕ) (hlevel : ∀ j q, q ∈ levelCells j ↔ level q = j)
    (q : Cell) :
    stoppingLevelCellIndex levelCells (level q)
      (stoppingLevelFinIndex levelCells level hlevel q) = q := by
  rw [stoppingLevelCellIndex, stoppingLevelFinIndex, Equiv.symm_apply_apply]

theorem stoppingLevelCellIndex_cast_stoppingLevelFinIndex {Cell : Type*}
    (levelCells : ℕ → Finset Cell)
    (level : Cell → ℕ) (hlevel : ∀ j q, q ∈ levelCells j ↔ level q = j)
    (q : Cell) {j : ℕ} (hj : level q = j) :
    stoppingLevelCellIndex levelCells j
      (Fin.cast (congrArg (stoppingLevelCellCount levelCells) hj)
        (stoppingLevelFinIndex levelCells level hlevel q)) = q := by
  subst j
  exact stoppingLevelCellIndex_stoppingLevelFinIndex levelCells level hlevel q

/-- **Overlapping stopping-graph adapter.**

Finite graph spheres are enumerated and supplied to
`wholeSpaceSolution_exterior_decay_of_stopping_cells`.  Adjacency itself gives
the required one-level inequality, and the raw graph-distance exterior cover
is reindexed by the tail sigma type expected by the consumer. -/
theorem wholeSpaceSolution_exterior_decay_of_overlapping_stopping_graph
    {Cell : Type*} {a f : Vec d → ℝ} {t : ℝ}
    (ht : 0 < t) (haNonneg : ∀ x, 0 ≤ a x)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (G : SimpleGraph Cell) (hconnected : G.Connected)
    (source : Finset Cell) (hsourceNonempty : source.Nonempty)
    (levelCells : ℕ → Finset Cell)
    (hlevelCells : ∀ j q, q ∈ levelCells j ↔
      stoppingGraphDistance G source hsourceNonempty q = j)
    (scale : Cell → ℤ) (centre : Cell → Vec d)
    (lam Lam : Cell → ℝ)
    (exterior : Set (Vec d)) {A theta0 : ℝ} (N D Nnbr : ℕ) {rate : ℝ}
    (hA : 0 ≤ A) (htheta0 : 0 < theta0) (hNnbr : 0 < Nnbr) (hD : 0 < D)
    (heffective : (D : ℝ) * ((Nnbr : ℝ) * theta0) < 1)
    (hsource : ∀ q, stoppingGraphDistance G source hsourceNonempty q = 0 →
      ∫ x in translatedCube d (scale q) (centre q), u.toFun x ^ 2 ∂volume ≤ A)
    (hLamNonneg : ∀ q, 0 ≤ Lam q)
    (hell : ∀ q, 0 < stoppingGraphDistance G source hsourceNonempty q →
      IsEllipticFieldOn (lam q) (Lam q)
        (translatedCube d (scale q + 1) (centre q)) (scalarCoeffField a))
    (habove : ∀ q, 0 < stoppingGraphDistance G source hsourceNonempty q →
      ∀ x ∈ translatedCube d (scale q + 1) (centre q), a x ≤ Lam q)
    (hquiet : ∀ q, 0 < stoppingGraphDistance G source hsourceNonempty q →
      ∀ x ∈ translatedCube d (scale q + 1) (centre q), f x = 0)
    (hsmall : ∀ q, 0 < stoppingGraphDistance G source hsourceNonempty q →
      4096 * (d : ℝ) * Lam q * t * ((3 : ℝ) ^ scale q)⁻¹ ^ 2 ≤ theta0)
    (hnbr : ∀ q, 0 < stoppingGraphDistance G source hsourceNonempty q →
      ∃ s : Finset Cell, s.Nonempty ∧ s.card ≤ Nnbr ∧
        (∀ p ∈ s, G.Adj q p) ∧
        translatedCube d (scale q + 1) (centre q) ⊆
          ⋃ p ∈ s, translatedCube d (scale p) (centre p))
    (hcard : ∀ j, (levelCells j).card ≤ N * D ^ j)
    (hcover : ∀ x ∈ exterior, ∃ q,
      ⌈rate⌉₊ ≤ stoppingGraphDistance G source hsourceNonempty q ∧
        x ∈ translatedCube d (scale q) (centre q)) :
    ∫ x in exterior, u.toFun x ^ 2 ∂volume ≤
      (N : ℝ) * A * (1 - (D : ℝ) * ((Nnbr : ℝ) * theta0))⁻¹ *
        Real.exp (Real.log ((D : ℝ) * ((Nnbr : ℝ) * theta0)) * rate) := by
  let count : ℕ → ℕ := stoppingLevelCellCount levelCells
  let cellAt : (j : ℕ) → Fin (count j) → Cell :=
    fun j i ↦ stoppingLevelCellIndex levelCells j i
  have hcellLevel : ∀ j (i : Fin (count j)),
      stoppingGraphDistance G source hsourceNonempty (cellAt j i) = j := by
    intro j i
    exact (hlevelCells j (cellAt j i)).1
      (stoppingLevelCellIndex_mem levelCells j i)
  refine wholeSpaceSolution_exterior_decay_of_stopping_cells ht haNonneg u
    (count := count) (fun j i ↦ scale (cellAt j i))
    (fun j i ↦ centre (cellAt j i))
    (fun j i ↦ lam (cellAt j i)) (fun j i ↦ Lam (cellAt j i))
    exterior N D Nnbr hA htheta0 hNnbr hD heffective ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    exact hsource (cellAt 0 i) (hcellLevel 0 i)
  · intro j i
    exact hLamNonneg (cellAt j i)
  · intro j i hj
    exact hell (cellAt j i) (by rwa [hcellLevel j i])
  · intro j i hj
    exact habove (cellAt j i) (by rwa [hcellLevel j i])
  · intro j i hj
    exact hquiet (cellAt j i) (by rwa [hcellLevel j i])
  · intro j i hj
    exact hsmall (cellAt j i) (by rwa [hcellLevel j i])
  · intro j i hj
    obtain ⟨s, hsne, hscard, hsadj, hscover⟩ :=
      hnbr (cellAt j i) (by rwa [hcellLevel j i])
    let encode : Cell → Σ k : ℕ, Fin (count k) := fun q ↦
      ⟨stoppingGraphDistance G source hsourceNonempty q,
        stoppingLevelFinIndex levelCells
          (stoppingGraphDistance G source hsourceNonempty)
          hlevelCells q⟩
    refine ⟨s.image encode, Finset.image_nonempty.mpr hsne,
      (Finset.card_image_le.trans hscard), ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hqs, rfl⟩ := Finset.mem_image.mp hp
      have hdist := stoppingGraphDistance_le_succ_of_adj G hconnected
        hsourceNonempty (hsadj q hqs)
      simpa only [hcellLevel j i, encode] using hdist
    · intro x hx
      obtain ⟨q, hqs, hxq⟩ := Set.mem_iUnion₂.mp (hscover hx)
      refine Set.mem_iUnion₂.mpr
        ⟨encode q, Finset.mem_image_of_mem encode hqs, ?_⟩
      change x ∈ translatedCube d
        (scale (cellAt (stoppingGraphDistance G source hsourceNonempty q)
          (stoppingLevelFinIndex levelCells
            (stoppingGraphDistance G source hsourceNonempty) hlevelCells q)))
        (centre (cellAt (stoppingGraphDistance G source hsourceNonempty q)
          (stoppingLevelFinIndex levelCells
            (stoppingGraphDistance G source hsourceNonempty) hlevelCells q)))
      rw [show cellAt (stoppingGraphDistance G source hsourceNonempty q)
        (stoppingLevelFinIndex levelCells
          (stoppingGraphDistance G source hsourceNonempty) hlevelCells q) = q by
        exact stoppingLevelCellIndex_stoppingLevelFinIndex levelCells
          (stoppingGraphDistance G source hsourceNonempty) hlevelCells q]
      exact hxq
  · intro j
    exact hcard j
  · intro x hx
    obtain ⟨q, hqlevel, hxq⟩ := hcover x hx
    let k := stoppingGraphDistance G source hsourceNonempty q - ⌈rate⌉₊
    have hsum : ⌈rate⌉₊ + k =
        stoppingGraphDistance G source hsourceNonempty q := by
      simp only [k, Nat.add_sub_of_le hqlevel]
    have hdist : stoppingGraphDistance G source hsourceNonempty q =
        ⌈rate⌉₊ + k := hsum.symm
    let iq : Fin (count (⌈rate⌉₊ + k)) :=
      Fin.cast (congrArg count hdist)
        (stoppingLevelFinIndex levelCells
          (stoppingGraphDistance G source hsourceNonempty) hlevelCells q)
    refine Set.mem_iUnion.mpr ⟨⟨k, iq⟩, ?_⟩
    change x ∈ translatedCube d (scale (cellAt (⌈rate⌉₊ + k) iq))
      (centre (cellAt (⌈rate⌉₊ + k) iq))
    have hiq : cellAt (⌈rate⌉₊ + k) iq = q := by
      exact stoppingLevelCellIndex_cast_stoppingLevelFinIndex levelCells
        (stoppingGraphDistance G source hsourceNonempty) hlevelCells q hdist
    rwa [hiq]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
