module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFluxColoring
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TriadicMeanComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Composition

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Cell : Type*} [Encodable Cell] [DecidableEq Cell]

/-- The smooth subordinate partition of unity consumed by the flux-row
partition carrier.  These are exactly the fields produced by
`exists_fluxRowFractionalNormalizedCutoff` for a stopping family. -/
structure StoppingFluxRowCutoff (d : ℕ) (Cell : Type*) [Encodable Cell]
    [DecidableEq Cell] (scale : Cell → ℤ) (center : Cell → Vec d) where
  cutoff : Cell → Vec d → ℝ
  lipschitzConstant : Cell → ℝ
  measurable : ∀ q, Measurable (cutoff q)
  nonneg : ∀ q x, 0 ≤ cutoff q x
  le_one : ∀ q x, cutoff q x ≤ 1
  support : ∀ q x,
    x ∉ translatedCube d (scale q + 1) (center q) → cutoff q x = 0
  lipschitz : ∀ q x y,
    |cutoff q x - cutoff q y| ≤ lipschitzConstant q * ‖x - y‖
  sum_le_one : ∀ n x, ∑ q ∈ stoppingCellExhaustion n, cutoff q x ≤ 1
  tendsto_one : ∀ x,
    Filter.Tendsto (fun n ↦ ∑ q ∈ stoppingCellExhaustion n, cutoff q x)
      Filter.atTop (nhds 1)

/-- Build agent4's abstract flux-row partition from the geometric stopping
cover, a subordinate partition of unity, and a proper finite coloring of a
graph containing every intersection edge. -/
def stoppingFluxRowRieszPartition
    (scale : Cell → ℤ) (center : Cell → Vec d)
    (_hcover : (⋃ q, translatedCube d (scale q) (center q)) = Set.univ)
    (overlapCount : ℕ) (hoverlapCount : 0 < overlapCount)
    (G : SimpleGraph Cell) (coloring : G.Coloring (Fin overlapCount))
    (hintersection : ∀ {q p}, q ≠ p →
      (translatedCube d (scale q + 1) (center q) ∩
        translatedCube d (scale p + 1) (center p)).Nonempty → G.Adj q p)
    (chi : StoppingFluxRowCutoff d Cell scale center) :
    FluxRowRieszPartition d Cell where
  cells := stoppingCellExhaustion
  cells_mono := monotone_stoppingCellExhaustion
  cells_exhaustive := exists_mem_stoppingCellExhaustion
  scale := scale
  center := center
  cutoff := chi.cutoff
  cutoff_measurable := chi.measurable
  cutoff_nonneg := chi.nonneg
  cutoff_le_one := chi.le_one
  cutoff_support := chi.support
  cutoffLipschitz := chi.lipschitzConstant
  cutoff_lipschitz := chi.lipschitz
  cutoff_sum_le_one := chi.sum_le_one
  cutoff_tendsto_one := chi.tendsto_one
  overlapCount := overlapCount
  overlapCount_pos := hoverlapCount
  color := coloring
  cell_measurable := fun q ↦
    Section6Schauder.measurableSet_translatedCube d (scale q + 1) (center q)
  cell_disjoint_color := fun n k ↦
    pairwiseDisjoint_filtered_cells_of_intersectionGraphColoring
      (stoppingCellExhaustion n)
      (fun q ↦ translatedCube d (scale q + 1) (center q)) G coloring
      hintersection k
  cellVolume := fun q ↦
    (volume (translatedCube d (scale q + 1) (center q))).toReal
  cellVolume_pos := fun q ↦
    Section6BoundedMultiplier.volume_translatedCube_toReal_pos
      (scale q + 1) (center q)

section Cutoff

variable (scale : Cell → ℤ) (center : Cell → Vec d)
variable (hcover : (⋃ q, translatedCube d (scale q) (center q)) = Set.univ)
variable (overlapCount : ℕ) (hoverlapCount : 0 < overlapCount)
variable (G : SimpleGraph Cell) (coloring : G.Coloring (Fin overlapCount))
variable (hintersection : ∀ {q p}, q ≠ p →
  (translatedCube d (scale q + 1) (center q) ∩
    translatedCube d (scale p + 1) (center p)).Nonempty → G.Adj q p)
variable (chi : StoppingFluxRowCutoff d Cell scale center)

@[simp]
theorem stoppingFluxRowRieszPartition_cell (q : Cell) :
    (stoppingFluxRowRieszPartition scale center hcover overlapCount
      hoverlapCount G coloring hintersection chi).cell q =
      translatedCube d (scale q + 1) (center q) :=
  rfl

@[simp]
theorem stoppingFluxRowRieszPartition_cellVolume (q : Cell) :
    (stoppingFluxRowRieszPartition scale center hcover overlapCount
      hoverlapCount G coloring hintersection chi).cellVolume q =
      (volume (translatedCube d (scale q + 1) (center q))).toReal :=
  rfl

@[simp]
theorem stoppingFluxRowRieszPartition_cutoff (q : Cell) :
    (stoppingFluxRowRieszPartition scale center hcover overlapCount
      hoverlapCount G coloring hintersection chi).cutoff q = chi.cutoff q :=
  rfl

end Cutoff

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
