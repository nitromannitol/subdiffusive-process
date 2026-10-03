module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsGridCover
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeFailureTailSummability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.CampanatoWindowGeometry

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Omega : Type*}

/-- One plus the last failed level at a half-spaced lattice centre.  The value
at an infinite failure height is a junk value; every theorem that uses the
selected scale also carries the finiteness certificate. -/
def stoppingPartitionDepth (failure : Lattice d → ℕ → Set Omega)
    (omega : Omega) (z : Lattice d) : ℕ :=
  (failureHeightAt (failure z) omega).untopD 0

/-- The integer scale selected above the base scale. -/
def stoppingPartitionScale (base : ℤ)
    (failure : Lattice d → ℕ → Set Omega) (omega : Omega)
    (z : Lattice d) : ℤ :=
  base + stoppingPartitionDepth failure omega z

/-- The selected open stopping cell.  Its centre remains on the half-spaced
base grid while its side is enlarged according to the local failure height. -/
def overlappingStoppingCell (base : ℤ)
    (failure : Lattice d → ℕ → Set Omega) (omega : Omega)
    (z : Lattice d) : Set (Vec d) :=
  translatedCube d (stoppingPartitionScale base failure omega z)
    (gridCentre d base z)

theorem base_le_stoppingPartitionScale (base : ℤ)
    (failure : Lattice d → ℕ → Set Omega) (omega : Omega)
    (z : Lattice d) :
    base ≤ stoppingPartitionScale base failure omega z := by
  rw [stoppingPartitionScale]
  omega

/-- A failure at level `j` lies strictly below the selected level whenever the
failure height is finite. -/
theorem lt_stoppingPartitionDepth_of_mem_failure
    (failure : Lattice d → ℕ → Set Omega) {omega : Omega} {z : Lattice d}
    (hfinite : failureHeightAt (failure z) omega ≠ (⊤ : WithTop ℕ))
    {j : ℕ} (hfail : omega ∈ failure z j) :
    j < stoppingPartitionDepth failure omega z := by
  have hcontribution :
      ((j + 1 : ℕ) : WithTop ℕ) ≤ failureHeightAt (failure z) omega :=
    coe_succ_le_extendedFailureHeight hfail
  generalize hheight : failureHeightAt (failure z) omega = height at hcontribution
  cases height with
  | top => exact (hfinite hheight).elim
  | coe H =>
      have hnat : j + 1 ≤ H := WithTop.coe_le_coe.mp hcontribution
      simpa only [stoppingPartitionDepth, hheight, WithTop.untopD_coe,
        Nat.lt_iff_add_one_le] using hnat

/-- No failure occurs at or above the selected level. -/
theorem not_mem_failure_of_stoppingPartitionDepth_le
    (failure : Lattice d → ℕ → Set Omega) {omega : Omega} {z : Lattice d}
    (hfinite : failureHeightAt (failure z) omega ≠ (⊤ : WithTop ℕ))
    {j : ℕ} (hlevel : stoppingPartitionDepth failure omega z ≤ j) :
    omega ∉ failure z j := by
  intro hfail
  exact (not_lt_of_ge hlevel)
    (lt_stoppingPartitionDepth_of_mem_failure failure hfinite hfail)

/-- In particular, the cell selected one level above the last failure is good. -/
theorem not_mem_failure_stoppingPartitionDepth
    (failure : Lattice d → ℕ → Set Omega) {omega : Omega} {z : Lattice d}
    (hfinite : failureHeightAt (failure z) omega ≠ (⊤ : WithTop ℕ)) :
    omega ∉ failure z (stoppingPartitionDepth failure omega z) :=
  not_mem_failure_of_stoppingPartitionDepth_le failure hfinite le_rfl

/-- Every point belongs to the selected cell above the rounded half-grid
index.  Hence the selected family is an overlapping cover of all of `R^d`. -/
theorem mem_overlappingStoppingCell_gridIndex (base : ℤ)
    (failure : Lattice d → ℕ → Set Omega) (omega : Omega) (x : Vec d) :
    x ∈ overlappingStoppingCell base failure omega (gridIndex d base x) := by
  apply translatedCube_subset_translatedCube_sameCenter
    (base_le_stoppingPartitionScale base failure omega (gridIndex d base x))
  exact mem_translatedCube_gridIndex d base x

/-- Set-level cover statement.  It is intentionally a cover, not a disjoint
partition: open cubes from a tiling would miss all shared faces. -/
theorem iUnion_overlappingStoppingCell_eq_univ (base : ℤ)
    (failure : Lattice d → ℕ → Set Omega) (omega : Omega) :
    (⋃ z : Lattice d, overlappingStoppingCell base failure omega z) =
      (Set.univ : Set (Vec d)) := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr
    ⟨gridIndex d base x, mem_overlappingStoppingCell_gridIndex base failure omega x⟩

variable [MeasurableSpace Omega]

/-- Geometric level tails give one full-measure event on which every selected
cell is good at its own stopping level.  This is the Borel--Cantelli use in the
partition proof. -/
theorem ae_forall_not_mem_failure_stoppingPartitionDepth
    (mu : Measure Omega) (failure : Lattice d → ℕ → Set Omega)
    (C q : ENNReal) (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ z j, mu (failure z j) ≤ C * q ^ j) :
    ∀ᵐ omega ∂mu, ∀ z,
      omega ∉ failure z (stoppingPartitionDepth failure omega z) := by
  filter_upwards [ae_forall_failureHeightAt_ne_top_of_le_geometric
    mu failure C q hC hq hmeasure] with omega hfinite
  intro z
  exact not_mem_failure_stoppingPartitionDepth failure (hfinite z)

/-- The same full-measure event gives the selected-level conclusion
simultaneously at every larger level. -/
theorem ae_forall_not_mem_failure_above_stoppingPartitionDepth
    (mu : Measure Omega) (failure : Lattice d → ℕ → Set Omega)
    (C q : ENNReal) (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ z j, mu (failure z j) ≤ C * q ^ j) :
    ∀ᵐ omega ∂mu, ∀ z j,
      stoppingPartitionDepth failure omega z ≤ j → omega ∉ failure z j := by
  filter_upwards [ae_forall_failureHeightAt_ne_top_of_le_geometric
    mu failure C q hC hq hmeasure] with omega hfinite
  intro z j hj
  exact not_mem_failure_of_stoppingPartitionDepth_le failure (hfinite z) hj

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
