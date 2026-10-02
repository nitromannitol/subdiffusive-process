import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFluxBoundedDegree




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization

noncomputable section

variable {d : ℕ} {Omega Cell : Type*}
variable [Encodable Cell] [DecidableEq Cell]

/-- Geometry of a repaired stopping family after fixing the sample.  The map
`failureCube` records the triadic-cube provenance of each selected/refined
cell; `scale` and `center` describe the actual analytic cell. -/
structure FluxRowRieszStoppingFamily
    (failure : TriadicCube d → Set Omega) (omega : Omega) where
  failureCube : Cell → TriadicCube d
  scale : Cell → ℤ
  scale_eq_failureCube : ∀ q, scale q = (failureCube q).scale
  center : Cell → Vec d
  cover : (⋃ q, translatedCube d (scale q) (center q)) = Set.univ
  cutoffData : StoppingFluxRowCutoff d Cell scale center
  graph : SimpleGraph Cell
  graphLocallyFinite : graph.LocallyFinite
  degreeBound : ℕ
  degree_le : ∀ q, (graph.neighborFinset q).card ≤ degreeBound
  intersection_edge : ∀ {q p}, q ≠ p →
    (translatedCube d (scale q + 1) (center q) ∩
      translatedCube d (scale p + 1) (center p)).Nonempty → graph.Adj q p

/-- Package a repaired selected family and its bounded-degree intersection
graph.  This is the direct constructor expected from the geometric producer. -/
def FluxRowRieszStoppingFamily.ofBoundedDegree
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (failureCube : Cell → TriadicCube d) (scale : Cell → ℤ)
    (hscale : ∀ q, scale q = (failureCube q).scale)
    (center : Cell → Vec d)
    (hcover : (⋃ q, translatedCube d (scale q) (center q)) = Set.univ)
    (chi : StoppingFluxRowCutoff d Cell scale center)
    (G : SimpleGraph Cell) [G.LocallyFinite] (D : ℕ)
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D)
    (hintersection : ∀ {q p}, q ≠ p →
      (translatedCube d (scale q + 1) (center q) ∩
        translatedCube d (scale p + 1) (center p)).Nonempty → G.Adj q p) :
    FluxRowRieszStoppingFamily (Cell := Cell) failure omega where
  failureCube := failureCube
  scale := scale
  scale_eq_failureCube := hscale
  center := center
  cover := hcover
  cutoffData := chi
  graph := G
  graphLocallyFinite := inferInstance
  degreeBound := D
  degree_le := hdegree
  intersection_edge := hintersection

variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- The failure event attached to the selected triadic ancestor of a repaired
cell.  This is cube-indexed even when the repaired cell has a half-grid
offset. -/
def FluxRowRieszStoppingFamily.failureEvent
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega)
    (q : Cell) : Set Omega :=
  failure (H.failureCube q)

/-- The canonical `D + 1` coloring of the repaired intersection graph. -/
def FluxRowRieszStoppingFamily.coloring
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega) :
    H.graph.Coloring (Fin (H.degreeBound + 1)) := by
  letI : H.graph.LocallyFinite := H.graphLocallyFinite
  exact stoppingBoundedDegreeColoring H.graph H.degreeBound H.degree_le

/-- Build the Riesz partition on the repaired carrier.  Unlike the old raw
`Lattice d` adapter, this constructor neither inserts deleted cells nor
changes the supplied centres. -/
def FluxRowRieszStoppingFamily.toPartition
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega) :
    FluxRowRieszPartition d Cell := by
  letI : H.graph.LocallyFinite := H.graphLocallyFinite
  exact stoppingFluxRowRieszPartitionOfBoundedDegree H.scale H.center H.cover
    H.graph H.degreeBound H.degree_le H.intersection_edge H.cutoffData



theorem FluxRowRieszStoppingFamily.ofBoundedDegree_toPartition
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (failureCube : Cell → TriadicCube d) (scale : Cell → ℤ)
    (hscale : ∀ q, scale q = (failureCube q).scale)
    (center : Cell → Vec d)
    (hcover : (⋃ q, translatedCube d (scale q) (center q)) = Set.univ)
    (chi : StoppingFluxRowCutoff d Cell scale center)
    (G : SimpleGraph Cell) [G.LocallyFinite] (D : ℕ)
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D)
    (hintersection : ∀ {q p}, q ≠ p →
      (translatedCube d (scale q + 1) (center q) ∩
        translatedCube d (scale p + 1) (center p)).Nonempty → G.Adj q p) :
    (FluxRowRieszStoppingFamily.ofBoundedDegree failure omega failureCube
      scale hscale center hcover chi G D hdegree hintersection).toPartition =
      stoppingFluxRowRieszPartitionOfBoundedDegree scale center hcover G D
        hdegree hintersection chi :=
  rfl

@[simp]
theorem FluxRowRieszStoppingFamily.toPartition_scale
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega) (q : Cell) :
    H.toPartition.scale q = H.scale q :=
  rfl

@[simp]
theorem FluxRowRieszStoppingFamily.toPartition_center
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega) (q : Cell) :
    H.toPartition.center q = H.center q :=
  rfl

@[simp]
theorem FluxRowRieszStoppingFamily.toPartition_cell
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega) (q : Cell) :
    H.toPartition.cell q = translatedCube d (H.scale q + 1) (H.center q) :=
  rfl

@[simp]
theorem FluxRowRieszStoppingFamily.toPartition_cellVolume
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega) (q : Cell) :
    H.toPartition.cellVolume q =
      (MeasureTheory.volume
        (translatedCube d (H.scale q + 1) (H.center q))).toReal :=
  rfl

@[simp]
theorem FluxRowRieszStoppingFamily.toPartition_overlapCount
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega) :
    H.toPartition.overlapCount = H.degreeBound + 1 :=
  rfl

@[simp]
theorem FluxRowRieszStoppingFamily.toPartition_color
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega) (q : Cell) :
    H.toPartition.color q = H.coloring q :=
  rfl

/-- The analytic scale retains the triadic failure-event provenance. -/
theorem FluxRowRieszStoppingFamily.toPartition_scale_eq_failureCube
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega) (q : Cell) :
    H.toPartition.scale q = (H.failureCube q).scale := by
  rw [H.toPartition_scale, H.scale_eq_failureCube]

/-- **The `3 ^ d` normalization gap of the enlarged analytic cell.**

The flux-row partition's analytic cell is the centered threefold enlargement
`z + □_{scale q + 1}` (the manuscript's `Q̂`, and the support of the cell's
cutoff), so its volume is `3 ^ d` times the volume `cubeVolume (originCube d
(scale q))` normalizing `localSymmetricEnergyENorm` and the manuscript's
`|Q| ‖F‖²_{H^{-σ}(Q)}`.  Consumers of the per-cell price must pay this
dimension-only factor deliberately. -/
theorem FluxRowRieszStoppingFamily.toPartition_cellVolume_eq_three_pow_mul
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega) (q : Cell) :
    H.toPartition.cellVolume q =
      (3 : ℝ) ^ d * cubeVolume (originCube d (H.scale q)) := by
  rw [H.toPartition_cellVolume,
    Section6BoundedMultiplier.volume_translatedCube_toReal,
    cubeVolume_eq_pow_scale]
  have h3 : (3 : ℝ) ^ (H.scale q + 1) = 3 * (3 : ℝ) ^ H.scale q := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring
  rw [h3, mul_pow]
  simp only [originCube]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
