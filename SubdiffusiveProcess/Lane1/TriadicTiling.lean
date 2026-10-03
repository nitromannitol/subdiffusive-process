module

public import SubdiffusiveProcess.Lane1.TriadicGrid
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-!
# The half-open triadic tiling

The vague limit compares `∫ f dmu_N` with a step sum over a finite disjoint
family covering the support of `f`.  The family is the half-open triadic
tiling: `x` lies in exactly one tile of each generation, the one indexed by
`⌊x i 3 ^ j⌋`.  The open cubes of `TriadicGrid` will not do — they overlap —
but the two agree in measure, because a tile and the open cube inside it have
the same Lebesgue volume and the cutoff measures are absolutely continuous.
-/

open MeasureTheory

noncomputable section
namespace SubdiffusiveProcess

/-- The half-open triadic tile of generation `j` at integer index `k`. -/
def triadicTile {d : ℕ} (j : ℕ) (k : Fin d → ℤ) : Set (SpatialCoordinates d) :=
  Set.pi Set.univ fun i => Set.Ico ((k i : ℝ) * (3 : ℝ) ^ (-(j : ℤ)))
    (((k i : ℝ) + 1) * (3 : ℝ) ^ (-(j : ℤ)))

theorem measurableSet_triadicTile {d : ℕ} (j : ℕ) (k : Fin d → ℤ) :
    MeasurableSet (triadicTile j k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- The index of the generation-`j` tile containing `x`. -/
def tileIndex {d : ℕ} (j : ℕ) (x : SpatialCoordinates d) : Fin d → ℤ :=
  fun i => ⌊x i / (3 : ℝ) ^ (-(j : ℤ))⌋

theorem mem_triadicTile_iff {d : ℕ} (j : ℕ) (k : Fin d → ℤ)
    (x : SpatialCoordinates d) :
    x ∈ triadicTile j k ↔ ∀ i,
      (k i : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) ≤ x i ∧
        x i < ((k i : ℝ) + 1) * (3 : ℝ) ^ (-(j : ℤ)) := by
  simp [triadicTile, Set.mem_univ_pi, Set.mem_Ico]

/-- Every point lies in the tile of its index. -/
theorem mem_triadicTile_tileIndex {d : ℕ} (j : ℕ) (x : SpatialCoordinates d) :
    x ∈ triadicTile j (tileIndex j x) := by
  have ht : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_neg_pos j
  rw [mem_triadicTile_iff]
  intro i
  constructor
  · have h := Int.floor_le (x i / (3 : ℝ) ^ (-(j : ℤ)))
    have := (le_div_iff₀ ht).mp h
    simpa [tileIndex] using this
  · have h := Int.lt_floor_add_one (x i / (3 : ℝ) ^ (-(j : ℤ)))
    have := (div_lt_iff₀ ht).mp h
    simpa [tileIndex] using this

/-- The index of a tile containing `x` is the index of `x`. -/
theorem tileIndex_eq_of_mem {d : ℕ} {j : ℕ} {k : Fin d → ℤ}
    {x : SpatialCoordinates d} (hx : x ∈ triadicTile j k) :
    k = tileIndex j x := by
  have ht : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_neg_pos j
  rw [mem_triadicTile_iff] at hx
  funext i
  obtain ⟨h1, h2⟩ := hx i
  have hle : (k i : ℝ) ≤ x i / (3 : ℝ) ^ (-(j : ℤ)) := (le_div_iff₀ ht).mpr h1
  have hlt : x i / (3 : ℝ) ^ (-(j : ℤ)) < (k i : ℝ) + 1 := (div_lt_iff₀ ht).mpr h2
  symm
  simpa [tileIndex] using Int.floor_eq_iff.mpr ⟨hle, hlt⟩

/-- Distinct tiles of the same generation are disjoint. -/
theorem triadicTile_disjoint {d : ℕ} (j : ℕ) {k l : Fin d → ℤ} (hkl : k ≠ l) :
    Disjoint (triadicTile j k) (triadicTile j l) := by
  rw [Set.disjoint_left]
  intro x hk hl
  exact hkl ((tileIndex_eq_of_mem hk).trans (tileIndex_eq_of_mem hl).symm)

/-- The centre of a triadic tile. -/
def tileCenter {d : ℕ} (j : ℕ) (k : Fin d → ℤ) : SpatialCoordinates d :=
  fun i => ((k i : ℝ) + 1 / 2) * (3 : ℝ) ^ (-(j : ℤ))

/-- The open cube inscribed in a tile is the centred cube of side `3 ^ (-j)`. -/
theorem centeredCube_tile_eq {d : ℕ} (j : ℕ) (k : Fin d → ℤ) :
    ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ))) (zpow_neg_pos j)) :
        Set (SpatialCoordinates d))
      = Set.pi Set.univ fun i => Set.Ioo ((k i : ℝ) * (3 : ℝ) ^ (-(j : ℤ)))
          (((k i : ℝ) + 1) * (3 : ℝ) ^ (-(j : ℤ))) := by
  rw [centeredCube_eq_pi]
  refine Set.pi_congr rfl fun i _ => ?_
  congr 1 <;> · simp only [tileCenter]; ring

/-- The inscribed open cube sits inside the tile. -/
theorem centeredCube_tile_subset {d : ℕ} (j : ℕ) (k : Fin d → ℤ) :
    ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ))) (zpow_neg_pos j)) :
        Set (SpatialCoordinates d)) ⊆ triadicTile j k := by
  rw [centeredCube_tile_eq, triadicTile]
  refine Set.pi_mono fun i _ => ?_
  exact Set.Ioo_subset_Ico_self

/-- A tile has the volume of its side to the `d`-th power. -/
theorem volume_triadicTile {d : ℕ} (j : ℕ) (k : Fin d → ℤ) :
    volume (triadicTile j k)
      = ENNReal.ofReal (((3 : ℝ) ^ (-(j : ℤ))) ^ d) := by
  have ht : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_neg_pos j
  rw [triadicTile, Real.volume_pi_Ico]
  have hcoord : ∀ i : Fin d,
      ENNReal.ofReal ((((k i : ℝ) + 1) * (3 : ℝ) ^ (-(j : ℤ)))
          - ((k i : ℝ) * (3 : ℝ) ^ (-(j : ℤ))))
        = ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) := by
    intro i
    congr 1
    ring
  rw [Finset.prod_congr rfl (fun i _ => hcoord i), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow ht.le]

/-- A tile and its inscribed open cube differ by a Lebesgue-null set. -/
theorem volume_triadicTile_sdiff {d : ℕ} (j : ℕ) (k : Fin d → ℤ) :
    volume (triadicTile j k \
      ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ))) (zpow_neg_pos j)) :
        Set (SpatialCoordinates d))) = 0 := by
  have ht : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_neg_pos j
  have hsub := centeredCube_tile_subset j k
  have hcube : volume ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ)))
      (zpow_neg_pos j)) : Set (SpatialCoordinates d))
      = ENNReal.ofReal (((3 : ℝ) ^ (-(j : ℤ))) ^ d) :=
    centeredCube_volume _ (zpow_neg_pos j)
  have hmble : MeasurableSet
      ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ))) (zpow_neg_pos j)) :
        Set (SpatialCoordinates d)) :=
    (centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ)))
      (zpow_neg_pos j)).isOpen.measurableSet
  rw [measure_diff hsub hmble.nullMeasurableSet
    (by rw [hcube]; exact ENNReal.ofReal_ne_top), volume_triadicTile, hcube,
    tsub_self]

/-- For a measure absolutely continuous with respect to Lebesgue, the mass of a
tile is the mass of its inscribed open cube. -/
theorem measure_triadicTile_eq {d : ℕ} (mu : Measure (SpatialCoordinates d))
    (hac : mu ≪ volume) (j : ℕ) (k : Fin d → ℤ) :
    mu (triadicTile j k)
      = mu ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ)))
          (zpow_neg_pos j)) : Set (SpatialCoordinates d)) := by
  have hsub := centeredCube_tile_subset j k
  have hnull : mu (triadicTile j k \
      ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ))) (zpow_neg_pos j)) :
        Set (SpatialCoordinates d))) = 0 :=
    hac (volume_triadicTile_sdiff j k)
  set cube : Set (SpatialCoordinates d) :=
    ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ))) (zpow_neg_pos j)) :
      Set (SpatialCoordinates d)) with hcube
  refine le_antisymm ?_ (measure_mono hsub)
  have hun : triadicTile j k ⊆ cube ∪ (triadicTile j k \ cube) := by
    intro x hx
    by_cases hxc : x ∈ cube
    · exact Or.inl hxc
    · exact Or.inr ⟨hx, hxc⟩
  calc mu (triadicTile j k) ≤ mu (cube ∪ (triadicTile j k \ cube)) :=
        measure_mono hun
    _ ≤ mu cube + mu (triadicTile j k \ cube) := measure_union_le _ _
    _ = mu cube := by rw [hnull, add_zero]

/-- Two points of a tile are within its side of each other. -/
theorem dist_le_of_mem_triadicTile {d : ℕ} {j : ℕ} {k : Fin d → ℤ}
    {x y : SpatialCoordinates d} (hx : x ∈ triadicTile j k)
    (hy : y ∈ triadicTile j k) :
    dist x y ≤ (3 : ℝ) ^ (-(j : ℤ)) := by
  have ht : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_neg_pos j
  rw [mem_triadicTile_iff] at hx hy
  refine (dist_pi_le_iff ht.le).mpr fun i => ?_
  obtain ⟨hx1, hx2⟩ := hx i
  obtain ⟨hy1, hy2⟩ := hy i
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

end SubdiffusiveProcess
