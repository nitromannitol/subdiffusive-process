module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszStoppingLimit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowFractionalPairing
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.Frozen.Section8
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Geometry of a possibly overlapping stopping-cell family together with a
smooth subordinate partition of unity and finite exhausting subfamilies. -/
structure FluxRowRieszPartition (d : ℕ) (Cell : Type*) [DecidableEq Cell] where
  cells : ℕ → Finset Cell
  cells_mono : Monotone cells
  cells_exhaustive : ∀ q, ∃ n, q ∈ cells n
  scale : Cell → ℤ
  center : Cell → Vec d
  cutoff : Cell → Vec d → ℝ
  cutoff_measurable : ∀ q, Measurable (cutoff q)
  cutoff_nonneg : ∀ q x, 0 ≤ cutoff q x
  cutoff_le_one : ∀ q x, cutoff q x ≤ 1
  cutoff_support : ∀ q x,
    x ∉ translatedCube d (scale q + 1) (center q) → cutoff q x = 0
  cutoffLipschitz : Cell → ℝ
  cutoff_lipschitz : ∀ q x y,
    |cutoff q x - cutoff q y| ≤ cutoffLipschitz q * ‖x - y‖
  cutoff_sum_le_one : ∀ n x, ∑ q ∈ cells n, cutoff q x ≤ 1
  cutoff_tendsto_one : ∀ x,
    Tendsto (fun n ↦ ∑ q ∈ cells n, cutoff q x) atTop (𝓝 1)
  overlapCount : ℕ
  overlapCount_pos : 0 < overlapCount
  color : Cell → Fin overlapCount
  cell_measurable : ∀ q,
    MeasurableSet (translatedCube d (scale q + 1) (center q))
  cell_disjoint_color : ∀ n k,
    ((cells n).filter (fun q ↦ color q = k) : Set Cell).PairwiseDisjoint
      (fun q ↦ translatedCube d (scale q + 1) (center q))
  cellVolume : Cell → ℝ
  cellVolume_pos : ∀ q, 0 < cellVolume q

variable {d : ℕ} {Cell : Type*} [DecidableEq Cell]

/-- The analytic cube attached to a partition index: the **centered threefold
enlargement** `Q̂` of the covering cube of scale `P.scale q`.  This is the
manuscript's localization cube, and it is where the subordinate cutoff of the
cell lives (`cutoff_support`). -/
def FluxRowRieszPartition.cell (P : FluxRowRieszPartition d Cell)
    (q : Cell) : Set (Vec d) :=
  translatedCube d (P.scale q + 1) (P.center q)

/-- A color class in a finite exhaustion is a disjoint family of cells. -/
theorem FluxRowRieszPartition.pairwiseDisjoint_color
    (P : FluxRowRieszPartition d Cell) (n : ℕ) (k : Fin P.overlapCount) :
    Set.PairwiseDisjoint
      (((P.cells n).filter (fun q ↦ P.color q = k) : Finset Cell) : Set Cell)
      P.cell := by
  exact P.cell_disjoint_color n k

/-- The sum of local positive energies over overlapping cells is bounded by
the coloring multiplicity times the global positive energy. -/
theorem FluxRowRieszPartition.sum_localPositiveEnergy_le
    (P : FluxRowRieszPartition d Cell) (n : ℕ)
    (massWeight : Cell → ℝ≥0∞) (globalMassWeight : ℝ≥0∞)
    (hweight : ∀ q ∈ P.cells n, massWeight q ≤ globalMassWeight)
    (kernel : Vec d × Vec d → ℝ≥0∞) (density : Vec d → ℝ≥0∞) :
    (∑ q ∈ P.cells n,
      fluxRowLocalPositiveEnergy volume (P.cell q) (massWeight q)
        kernel density) ≤
      (P.overlapCount : ℝ≥0∞) *
        fluxRowGlobalPositiveEnergy volume globalMassWeight kernel density := by
  let energy : Cell → ℝ≥0∞ := fun q ↦
    fluxRowLocalPositiveEnergy volume (P.cell q) (massWeight q) kernel density
  calc
    (∑ q ∈ P.cells n, energy q) =
        ∑ k : Fin P.overlapCount,
          ∑ q ∈ (P.cells n).filter (fun q ↦ P.color q = k), energy q := by
      rw [Finset.sum_fiberwise_of_maps_to]
      exact fun q _ ↦ Finset.mem_univ (P.color q)
    _ ≤ ∑ _k : Fin P.overlapCount,
        fluxRowGlobalPositiveEnergy volume globalMassWeight kernel density := by
      apply Finset.sum_le_sum
      intro k _
      apply sum_fluxRowLocalPositiveEnergy_le_global volume
      · intro q hq
        exact P.cell_measurable q
      · exact P.pairwiseDisjoint_color n k
      · intro q hq
        exact hweight q (Finset.mem_filter.mp hq).1
    _ = (P.overlapCount : ℝ≥0∞) *
        fluxRowGlobalPositiveEnergy volume globalMassWeight kernel density := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin]

/-- The normalized complex physical pairing against the cell's cutoff. -/
def FluxRowRieszPartition.cellPairing
    (P : FluxRowRieszPartition d Cell) (F : Vec d → Vec d)
    (i : Fin d) (phi : SchwartzMap (Vec d) ℂ) (q : Cell) : ℂ :=
  fluxRowFractionalCellPairing (P.cutoff q) (P.cellVolume q) F i
    (inverseFourierSchwartz phi)

/-- Finite localized pairings converge to the global physical pairing along
the partition exhaustion. -/
theorem FluxRowRieszPartition.tendsto_mk_localizedPairing
    (P : FluxRowRieszPartition d Cell) (F : Vec d → Vec d)
    (i : Fin d) (phi : SchwartzMap (Vec d) ℂ)
    (hintegrable : Integrable
      (fun x ↦ Complex.ofReal (F x i) * inverseFourierSchwartz phi x) volume) :
    Tendsto
      (fun n ↦ Complex.mk
        (fluxRowLocalizedPairing (P.cells n) P.cellVolume
          (fun q ↦ (P.cellPairing F i phi q).re))
        (fluxRowLocalizedPairing (P.cells n) P.cellVolume
          (fun q ↦ (P.cellPairing F i phi q).im)))
      atTop
      (𝓝 (∫ x, Complex.ofReal (F x i) * inverseFourierSchwartz phi x ∂volume)) :=
  fluxRowFractional_tendsto_cellPairing P.cells P.cutoff P.cutoff_measurable
    P.cutoff_nonneg P.cutoff_le_one P.cutoff_sum_le_one P.cutoff_tendsto_one
    P.cellVolume (fun q ↦ ne_of_gt (P.cellVolume_pos q)) F i
    (inverseFourierSchwartz phi) hintegrable

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
