module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionConsumer
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszPartitionEnergy
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Cell : Type*} [DecidableEq Cell]

set_option linter.unusedSectionVars false in
/-- Nonnegative per-cell prices are summable when their sums over finite
stopping-graph spheres have a summable majorant. -/
theorem summable_cellPrice_of_stoppingLevel_sums
    (levelCells : ℕ → Finset Cell) (level : Cell → ℕ)
    (hlevel : ∀ j q, q ∈ levelCells j ↔ level q = j)
    (cellPrice : Cell → ℝ) (hcellPrice : ∀ q, 0 ≤ cellPrice q)
    (shellPrice : ℕ → ℝ) (hshellPrice : Summable shellPrice)
    (hshell : ∀ j,
      ∑ q ∈ levelCells j, cellPrice q ≤ shellPrice j) :
    Summable cellPrice := by
  have hpartition : ∀ q, ∃! j, q ∈ (levelCells j : Set Cell) := by
    intro q
    refine ⟨level q, ?_, ?_⟩
    · exact (hlevel (level q) q).2 rfl
    · intro j hj
      exact (hlevel j q).1 hj |>.symm
  apply (summable_partition (s := fun j ↦ (levelCells j : Set Cell))
    hcellPrice hpartition).2
  constructor
  · intro j
    letI : Fintype (levelCells j : Set Cell) :=
      (levelCells j).finite_toSet.fintype
    exact summable_of_finite_support
      (Set.toFinite (Function.support fun q : (levelCells j : Set Cell) ↦
        cellPrice q))
  · refine Summable.of_nonneg_of_le
      (fun j ↦ tsum_nonneg fun q ↦ hcellPrice q) ?_ hshellPrice
    intro j
    simpa only [Finset.tsum_subtype'] using hshell j

/-- Assemble agent4's coefficient budget from a graph-sphere summation
bound.  The local comparison remains exactly the per-cell negative-Sobolev
estimate, while all global summability is discharged here. -/
def fluxRowRieszCoefficientBudget_of_stoppingLevel_sums
    (P : FluxRowRieszPartition d Cell) (localNegative : Fin d → Cell → ℝ)
    (K : ℝ)
    (hlocNonneg : ∀ i q, 0 ≤ localNegative i q)
    (cellPrice : Fin d → Cell → ℝ)
    (hpriceNonneg : ∀ i q, 0 ≤ cellPrice i q)
    (hlocal : ∀ i q,
      P.cellVolume q * localNegative i q ^ 2 ≤ cellPrice i q)
    (levelCells : ℕ → Finset Cell) (level : Cell → ℕ)
    (hlevel : ∀ j q, q ∈ levelCells j ↔ level q = j)
    (shellPrice : Fin d → ℕ → ℝ)
    (hshellSummable : ∀ i, Summable (shellPrice i))
    (hshell : ∀ i j,
      ∑ q ∈ levelCells j, cellPrice i q ≤ shellPrice i j) :
    FluxRowRieszCoefficientBudget P localNegative K where
  localNegative_nonneg := hlocNonneg
  cellPrice := cellPrice
  cellPrice_nonneg := hpriceNonneg
  localNegative_sq_le := hlocal
  cellPrice_summable := fun i ↦
    summable_cellPrice_of_stoppingLevel_sums levelCells level hlevel
      (cellPrice i) (hpriceNonneg i) (shellPrice i) (hshellSummable i)
      (hshell i)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
