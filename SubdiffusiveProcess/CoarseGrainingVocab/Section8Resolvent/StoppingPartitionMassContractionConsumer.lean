module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionConsumer
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsMesoscopic

@[expose] public section

/-!
# Feeding graph-indexed cell contractions to the mesoscopic exterior row

This is the enumeration adapter for the mass-contraction form of the exterior
row.  Its geometric neighbor premise permits the cell itself as well as graph
neighbors: this is the closed-neighborhood cover naturally produced by the
repaired half-grid stopping family.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Enumerate finite graph spheres and feed graph-indexed mass contractions to
`wholeSpaceSolution_exterior_decay_of_cell_mass_contractions`. -/
theorem wholeSpaceSolution_exterior_decay_of_graph_cell_mass_contractions
    {Cell : Type*} {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (G : SimpleGraph Cell)
    (source : Finset Cell) (hsourceNonempty : source.Nonempty)
    (levelCells : ℕ → Finset Cell)
    (hlevelCells : ∀ j q, q ∈ levelCells j ↔
      stoppingGraphDistance G source hsourceNonempty q = j)
    (scale : Cell → ℤ) (centre : Cell → Vec d)
    (exterior : Set (Vec d)) {A theta0 : ℝ} (N D Nnbr : ℕ) {rate : ℝ}
    (hA : 0 ≤ A) (htheta0 : 0 < theta0) (hNnbr : 0 < Nnbr) (hD : 0 < D)
    (heffective : (D : ℝ) * ((Nnbr : ℝ) * theta0) < 1)
    (hsource : ∀ q, stoppingGraphDistance G source hsourceNonempty q = 0 →
      ∫ x in translatedCube d (scale q) (centre q), u.toFun x ^ 2 ∂volume ≤ A)
    (hcell : ∀ q, 0 < stoppingGraphDistance G source hsourceNonempty q →
      ∫ x in translatedCube d (scale q) (centre q), u.toFun x ^ 2 ∂volume ≤
        theta0 * ∫ x in translatedCube d (scale q + 1) (centre q),
          u.toFun x ^ 2 ∂volume)
    (hnbr : ∀ q, 0 < stoppingGraphDistance G source hsourceNonempty q →
      ∃ s : Finset Cell, s.Nonempty ∧ s.card ≤ Nnbr ∧
        (∀ p ∈ s, stoppingGraphDistance G source hsourceNonempty q ≤
          stoppingGraphDistance G source hsourceNonempty p + 1) ∧
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
  refine wholeSpaceSolution_exterior_decay_of_cell_mass_contractions u
    (count := count) (fun j i ↦ scale (cellAt j i))
    (fun j i ↦ centre (cellAt j i)) exterior N D Nnbr hA htheta0 hNnbr hD
    heffective ?_ ?_ ?_ ?_ ?_
  · intro i
    exact hsource (cellAt 0 i) (hcellLevel 0 i)
  · intro j i hj
    exact hcell (cellAt j i) (by rwa [hcellLevel j i])
  · intro j i hj
    obtain ⟨s, hsne, hscard, hslevel, hscover⟩ :=
      hnbr (cellAt j i) (by rwa [hcellLevel j i])
    let encode : Cell → Σ k : ℕ, Fin (count k) := fun q ↦
      ⟨stoppingGraphDistance G source hsourceNonempty q,
        stoppingLevelFinIndex levelCells
          (stoppingGraphDistance G source hsourceNonempty) hlevelCells q⟩
    refine ⟨s.image encode, Finset.image_nonempty.mpr hsne,
      Finset.card_image_le.trans hscard, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, hqs, rfl⟩ := Finset.mem_image.mp hp
      simpa only [hcellLevel j i, encode] using hslevel q hqs
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
  · exact hcard
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
