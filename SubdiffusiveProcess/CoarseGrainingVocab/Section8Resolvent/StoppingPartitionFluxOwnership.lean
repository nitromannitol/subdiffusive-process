import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszPartitionInterface
import Mathlib.Logic.Encodable.Lattice




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set

noncomputable section
attribute [local instance] Classical.propDecidable

variable {X Cell : Type*} [Encodable Cell] [DecidableEq Cell]

/-- The finite family of cells whose canonical encoding is less than `n`. -/
def stoppingCellExhaustion (n : ℕ) : Finset Cell :=
  (Finset.range n).filterMap (Encodable.decode₂ Cell) fun a a' b ha ha' ↦ by
    rw [Encodable.mem_decode₂] at ha ha'
    omega

set_option linter.unusedSectionVars false in
theorem mem_stoppingCellExhaustion_iff {n : ℕ} {q : Cell} :
    q ∈ stoppingCellExhaustion n ↔ Encodable.encode q < n := by
  rw [stoppingCellExhaustion, Finset.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hdecode⟩
    have haq : Encodable.encode q = a :=
      Encodable.decode₂_eq_some.mp hdecode
    simpa only [haq] using Finset.mem_range.mp ha
  · intro hq
    exact ⟨Encodable.encode q, Finset.mem_range.mpr hq,
      Encodable.decode₂_encode q⟩

theorem monotone_stoppingCellExhaustion :
    Monotone (stoppingCellExhaustion : ℕ → Finset Cell) := by
  intro n m hnm q hq
  rw [mem_stoppingCellExhaustion_iff] at hq ⊢
  exact hq.trans_le hnm

theorem exists_mem_stoppingCellExhaustion (q : Cell) :
    ∃ n, q ∈ stoppingCellExhaustion n :=
  ⟨Encodable.encode q + 1, mem_stoppingCellExhaustion_iff.mpr (by omega)⟩

/-- The points assigned to `q`: points of its cell which do not lie in an
earlier cell. -/
def stoppingOwnershipPiece (cell : Cell → Set X) (q : Cell) : Set X :=
  cell q \ ⋃ p ∈ stoppingCellExhaustion (Encodable.encode q), cell p

set_option linter.unusedSectionVars false in
theorem stoppingOwnershipPiece_subset (cell : Cell → Set X) (q : Cell) :
    stoppingOwnershipPiece cell q ⊆ cell q :=
  diff_subset

set_option linter.unusedSectionVars false in
theorem measurableSet_stoppingOwnershipPiece [MeasurableSpace X]
    (cell : Cell → Set X) (hcell : ∀ q, MeasurableSet (cell q)) (q : Cell) :
    MeasurableSet (stoppingOwnershipPiece cell q) := by
  apply (hcell q).diff
  exact Finset.measurableSet_biUnion _ fun p _ ↦ hcell p

/-- Ownership pieces are pairwise disjoint even though the cells overlap. -/
theorem pairwiseDisjoint_stoppingOwnershipPiece (cell : Cell → Set X) :
    (Set.univ : Set Cell).PairwiseDisjoint (stoppingOwnershipPiece cell) := by
  rw [Set.pairwiseDisjoint_iff]
  intro q _ p _ hnonempty
  by_contra hqp
  rcases lt_or_gt_of_ne (Encodable.encode_injective.ne hqp) with hlt | hgt
  · obtain ⟨x, hxq, hxp⟩ := hnonempty
    exact hxp.2 (Set.mem_iUnion₂.mpr
      ⟨q, mem_stoppingCellExhaustion_iff.mpr hlt, hxq.1⟩)
  · obtain ⟨x, hxq, hxp⟩ := hnonempty
    exact hxq.2 (Set.mem_iUnion₂.mpr
      ⟨p, mem_stoppingCellExhaustion_iff.mpr hgt, hxp.1⟩)

/-- The ownership pieces cover the same union as the original cells. -/
theorem iUnion_stoppingOwnershipPiece_eq_iUnion (cell : Cell → Set X) :
    (⋃ q, stoppingOwnershipPiece cell q) = ⋃ q, cell q := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_mono fun q ↦ stoppingOwnershipPiece_subset cell q
  · intro x hx
    obtain ⟨q₀, hxq₀⟩ := Set.mem_iUnion.mp hx
    let hasCell : ℕ → Prop := fun n ↦ ∃ q, Encodable.encode q = n ∧ x ∈ cell q
    have hexists : ∃ n, hasCell n := ⟨Encodable.encode q₀, q₀, rfl, hxq₀⟩
    obtain ⟨q, hqencode, hxq⟩ := Nat.find_spec hexists
    refine Set.mem_iUnion.mpr ⟨q, hxq, ?_⟩
    intro hxEarlier
    obtain ⟨p, hpEarly, hxp⟩ := Set.mem_iUnion₂.mp hxEarlier
    have hpFind : Nat.find hexists ≤ Encodable.encode p :=
      Nat.find_min' hexists ⟨p, rfl, hxp⟩
    have hpLt : Encodable.encode p < Encodable.encode q :=
      mem_stoppingCellExhaustion_iff.mp hpEarly
    rw [hqencode] at hpLt
    omega

/-- If the cells cover the ambient space, so do their disjoint ownership
pieces. -/
theorem iUnion_stoppingOwnershipPiece_eq_univ
    (cell : Cell → Set X) (hcover : (⋃ q, cell q) = Set.univ) :
    (⋃ q, stoppingOwnershipPiece cell q) = Set.univ := by
  rw [iUnion_stoppingOwnershipPiece_eq_iUnion, hcover]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
